import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitelyManyIsoClassesProjectiveNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntBilinFormToRealMemBalancedPsdConeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellGeneratorOnRayOfLinIndepSubcellStatement

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section
namespace GlobalTheory.PolFan

namespace MultBound
variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  {X₁ : Type} [AddCommGroup X₁] [Module O X₁] {m : ℕ}

theorem cellMult_map {Y : Type} [AddCommGroup Y] [Module O Y] (f : balForms bar X ≃ₗ[ℤ] balForms bar Y)
    (δ : Fin m → balForms bar X) : cellMult bar (fun i => f (δ i)) = cellMult bar δ := by
  unfold cellMult
  have hs : (Submodule.span ℤ (Set.range δ)).map (f : balForms bar X →ₗ[ℤ] balForms bar Y) =
      Submodule.span ℤ (Set.range fun i => f (δ i)) := by
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  let g := Submodule.Quotient.equiv _ _ f hs
  symm
  refine Nat.card_congr (g.toEquiv.subtypeEquiv fun x => ?_)
  simp only [Submodule.mem_torsion_iff]
  refine exists_congr fun a => ?_
  rw [Submonoid.smul_def, Submonoid.smul_def]
  change _ ↔ (a : ℤ) • g x = 0
  rw [← map_smul, LinearEquiv.map_eq_zero_iff]

theorem cellMult_le_of_finite (T : Set (balForms bar X)) (hT : T.Finite) :
    ∃ C : ℕ, ∀ (m : ℕ) (δ : Fin m → balForms bar X), (∀ i, δ i ∈ T) → cellMult bar δ ≤ C := by
  classical
  let F : Set (balForms bar X) → ℕ := fun s => Nat.card (Submodule.torsion ℤ (balForms bar X ⧸ Submodule.span ℤ s))
  refine ⟨hT.toFinset.powerset.sup fun s => F ↑s, fun m δ hδ => ?_⟩
  have hr : Set.range δ ⊆ T := Set.range_subset_iff.2 hδ
  have e : Set.range δ = ↑((hT.subset hr).toFinset) := by simp
  have hmem : (hT.subset hr).toFinset ∈ hT.toFinset.powerset :=
    Finset.mem_powerset.2 (Set.Finite.toFinset_subset_toFinset.2 hr)
  show F (Set.range δ) ≤ _
  rw [e]
  exact Finset.le_sup_of_le hmem le_rfl

theorem zsmul_cancel {g : ℤ} (hg : g ≠ 0) {u w : balForms bar X} (h : g • u = g • w) : u = w :=
  Subtype.ext (LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ (congrArg Subtype.val h) a b
    simp only [Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hg this)

theorem prim_eq_of_smul {β β' : balForms bar X} (hβ : IsPrim bar β) (hβ' : IsPrim bar β') {p q : ℕ} (hp : 0 < p)
    (h : p • β = q • β') : β = β' := by
  have hd0 : 0 < Nat.gcd p q := Nat.gcd_pos_of_pos_left _ hp
  obtain ⟨p', q', hcop, hp', hq'⟩ := Nat.exists_coprime p q
  have h' : (p' : ℤ) • β = (q' : ℤ) • β' := by
    refine zsmul_cancel (g := (Nat.gcd p q : ℤ)) (by exact_mod_cast hd0.ne') ?_
    rw [smul_smul, smul_smul, ← Nat.cast_mul, ← Nat.cast_mul, mul_comm, ← hp', mul_comm, ← hq', natCast_zsmul,
      natCast_zsmul]
    exact h
  have hb : ((Nat.gcd p' q' : ℕ) : ℤ) = p' * Nat.gcdA p' q' + q' * Nat.gcdB p' q' := Nat.gcd_eq_gcd_ab p' q'
  rw [hcop, Nat.cast_one] at hb
  set A := Nat.gcdA p' q'
  set B := Nat.gcdB p' q'
  set x : balForms bar X := B • β + A • β'
  have e1 : β = q' • x := by
    rw [← natCast_zsmul, smul_add, smul_smul, smul_smul,
      show ((q' : ℤ) * A) • β' = (A * p') • β by rw [mul_comm, ← smul_smul, ← h', smul_smul], ← add_smul]
    conv_lhs => rw [← one_smul ℤ β]
    congr 1
    rw [hb]; ring
  have e2 : β' = p' • x := by
    rw [← natCast_zsmul, smul_add, smul_smul, smul_smul,
      show ((p' : ℤ) * B) • β = (B * q') • β' by rw [mul_comm, ← smul_smul, h', smul_smul], ← add_smul]
    conv_lhs => rw [← one_smul ℤ β']
    congr 1
    rw [hb]; ring
  have h1 := hβ _ _ e1
  have h2 := hβ' _ _ e2
  rw [e1, e2, h1, h2]

theorem transport [Module.Finite O X] [Module.Finite O X₁] (e : X ≃ₗ[O] X₁) {δ : Fin m → LinearMap.BilinForm ℤ X₁}
    (h : IsCell bar φ δ) (hl : LinearIndependent ℤ δ) (hp : ∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X₁)) :
    ∃ h' : IsCell bar φ (fun i => pull e.toLinearMap (δ i)), LinearIndependent ℤ (fun i => pull e.toLinearMap (δ i)) ∧
      (∀ i, IsPrim bar (⟨_, h'.mem i⟩ : balForms bar X)) ∧
      cellMult bar (fun i => (⟨pull e.toLinearMap (δ i), h'.mem i⟩ : balForms bar X)) =
        cellMult bar (fun i => (⟨δ i, h.mem i⟩ : balForms bar X₁)) := by
  have h' : IsCell bar φ (fun i => pull e.toLinearMap (δ i)) :=
    ⟨fun i => pull_mem _ (h.mem i), fun i _ => h.nonneg i _, (linearOn_pull_iff e.surjective).2 h.linear,
      IsStrict.of_pull (r := e.symm.toLinearMap) e.symm.surjective (by simpa using h.strict)⟩
  have e0 : ∀ i, (pullBalEquiv bar e) ⟨δ i, h.mem i⟩ = ⟨pull e.toLinearMap (δ i), h'.mem i⟩ := fun i => rfl
  have hfam : (fun i => (pullBalEquiv bar e) ⟨δ i, h.mem i⟩) =
      fun i => (⟨pull e.toLinearMap (δ i), h'.mem i⟩ : balForms bar X) := funext e0
  refine ⟨h', ?_, fun i k β' hk => ?_, by rw [← hfam]; exact cellMult_map _ _⟩
  · let P : LinearMap.BilinForm ℤ X₁ →ₗ[ℤ] LinearMap.BilinForm ℤ X :=
      { toFun := pull e.toLinearMap, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    exact hl.map' P (LinearMap.ker_eq_bot.2 fun a b hab => by
      rw [← pull_symm_pull e a, ← pull_symm_pull e b]; exact congrArg _ hab)
  · exact hp i k _ (by rw [← (pullBalEquiv bar e).symm_apply_apply ⟨δ i, h.mem i⟩, e0, hk, map_nsmul])

theorem perModule [Module.Finite O X] (hF : IsPolyFanOn bar φ X)
    (hpsd : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → toReal β ∈ psdCone bar X) :
    ∃ C : ℕ, ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ), LinearIndependent ℤ δ →
      (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) → cellMult bar (fun i => (⟨δ i, h.mem i⟩ : balForms bar X)) ≤ C := by
  classical
  obtain ⟨S, hS, hcov⟩ := hF.finite
  let T : Set (balForms bar X) :=
    {β | IsPrim bar β ∧ ∃ γ : balForms bar X, γ.1 ∈ S ∧ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a • β = b • γ}
  have hT : T.Finite := by
    have hS' : {γ : balForms bar X | γ.1 ∈ S}.Finite := hS.preimage Subtype.val_injective.injOn
    choose! f hf using fun β (hβ : β ∈ T) => hβ.2
    refine Set.Finite.of_injOn (f := f) (fun β hβ => (hf β hβ).1) (fun β hβ β' hβ' hff => ?_) hS'
    obtain ⟨-, a, b, ha, hb, h1⟩ := hf β hβ
    obtain ⟨-, a', b', ha', hb', h2⟩ := hf β' hβ'
    rw [hff] at h1
    refine prim_eq_of_smul hβ.1 hβ'.1 (p := b' * a) (q := b * a') (by positivity) ?_
    rw [mul_smul, h1, mul_smul, h2, smul_comm]
  obtain ⟨C, hC⟩ := cellMult_le_of_finite T hT
  refine ⟨C, fun m δ h hl hp => ?_⟩
  have hB : toReal (∑ i, δ i) ∈ psdCone bar X := hpsd _ (Submodule.sum_mem _ fun i _ => h.mem i) fun y => by
    simp only [LinearMap.sum_apply]; exact Finset.sum_nonneg fun i _ => h.nonneg i y
  obtain ⟨e, n, γ, c, hγ, hγS, hc, hrel⟩ := hcov _ hB
  obtain ⟨h', hl', hp', hm⟩ := transport e h hl hp
  rw [← hm]
  refine hC m _ fun i => ⟨hp' i, ?_⟩
  have hrel' : ∑ i, toReal (pull e.toLinearMap (δ i)) = ∑ j, c j • toReal (γ j) := by
    rw [← hrel]; ext a b; simp [LinearMap.sum_apply]
  obtain ⟨j, a, b, ha, hb, hab⟩ := GlobalTheory.T.cellGenerator_on_ray_of_linIndep_subcell O bar φ X m n _ γ c h' hγ hl' hc hrel' i
  exact ⟨⟨γ j, hγ.mem j⟩, hγS j, a, b, ha, hb, Subtype.ext (by simpa using hab)⟩

end MultBound

open MultBound in

theorem maxMult_lt_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (φ : InvFun (𝓞 E)), IsPolyFan H.bar q φ → maxMult H.bar q φ < ⊤ := by
  intro E _ _ _ H q φ hφ
  obtain ⟨n, Y, hY⟩ := GlobalTheory.T.finitely_many_iso_classes_projective_numberField E q
  have hb : ∀ k : Fin n, ∃ C : ℕ, ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]
      [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → Nonempty (X ≃ₗ[𝓞 E] Y k) → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
      LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
      cellMult H.bar (fun i => (⟨δ i, h.mem i⟩ : balForms H.bar X)) ≤ C := by
    intro k
    by_cases hk : ∃ (X : Type) (_ : AddCommGroup X) (_ : Module (𝓞 E) X) (_ : Module.Finite (𝓞 E) X)
      (_ : Module.Projective (𝓞 E) X), Module.finrank (𝓞 E) X ≤ q ∧ Nonempty (X ≃ₗ[𝓞 E] Y k)
    · obtain ⟨X, _, _, _, _, hX, ⟨e⟩⟩ := hk
      haveI : Module.Finite (𝓞 E) (Y k) := Module.Finite.equiv e
      haveI : Module.Projective (𝓞 E) (Y k) := Module.Projective.of_equiv e
      have hYr : Module.finrank (𝓞 E) (Y k) ≤ q := e.finrank_eq ▸ hX
      obtain ⟨C, hC⟩ := perModule (hφ (Y k) hYr) (GlobalTheory.T.intBilinFormToReal_mem_balancedPsdCone E H (Y k))
      refine ⟨C, fun X' _ _ _ _ _ he' m δ h hl hp => ?_⟩
      obtain ⟨e'⟩ := he'
      obtain ⟨h', hl', hp', hc⟩ := transport e'.symm h hl hp
      rw [← hc]
      exact hC m _ h' hl' hp'
    · exact ⟨0, fun X _ _ _ _ hX he => (hk ⟨X, _, _, inferInstance, inferInstance, hX, he⟩).elim⟩
  choose C hC using hb
  refine lt_of_le_of_lt (b := ((Finset.univ.sup C : ℕ) : ℕ∞)) ?_ (ENat.coe_lt_top _)
  unfold maxMult
  refine iSup_le fun X => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => iSup_le fun hX =>
    iSup_le fun m => iSup_le fun δ => iSup_le fun h => iSup_le fun hl => iSup_le fun hp => ?_
  obtain ⟨k, he⟩ := hY X hX
  exact_mod_cast (hC k X hX he m δ h hl hp).trans (Finset.le_sup (Finset.mem_univ k))

end GlobalTheory.PolFan
