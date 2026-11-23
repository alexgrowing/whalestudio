import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.TwistOfRed
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private noncomputable def linRep {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) :
    Representation k Γ (Fin n → k) where
  toFun g := Matrix.toLin' (r g : Matrix (Fin n) (Fin n) k)
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' g h := by simp [Matrix.toLin'_mul, Module.End.mul_eq_comp]

private theorem linRep_apply {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (g : Γ) (v : Fin n → k) :
    linRep r g v = (r g : Matrix (Fin n) (Fin n) k).mulVec v := rfl

private theorem isIrr_iff {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) :
    IsIrr r ↔ (linRep r).IsIrreducible := by
  constructor
  · rintro ⟨h0, -, h⟩
    haveI : Nontrivial (Subrepresentation (linRep r)) := ⟨⊤, ⊥, fun h' =>
      h0 (congrArg Subrepresentation.toSubmodule h')⟩
    refine ⟨fun S => ?_⟩
    rcases h S.toSubmodule le_top (fun g v hv => S.apply_mem_toSubmodule g hv) with h1 | h1
    · left; exact Subrepresentation.toSubmodule_injective h1
    · right; exact Subrepresentation.toSubmodule_injective h1
  · intro h
    refine ⟨fun h0 => ?_, fun _ _ _ => Submodule.mem_top, fun W _ hW => ?_⟩
    · exact bot_ne_top (α := Subrepresentation (linRep r)) (Subrepresentation.toSubmodule_injective h0.symm)
    · rcases h.eq_bot_or_eq_top (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation (linRep r)) with h1 | h1
      · left; exact congrArg Subrepresentation.toSubmodule h1
      · right; exact congrArg Subrepresentation.toSubmodule h1

private theorem isIrr_comp_of_range {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (φ : Γ' →* Γ) (h : IsIrr (r.comp φ.range.subtype)) : IsIrr (r.comp φ) := by
  obtain ⟨h0, -, h⟩ := h
  refine ⟨h0, fun _ _ _ => Submodule.mem_top, fun W hle hW => h W hle ?_⟩
  rintro ⟨_, g, rfl⟩ v hv
  exact hW g v hv

theorem UpperTheory.galois_representation_irreducible_prime_dimension :
    UpperTheory.V.Af.Sol.IrrPrime := by
  intro Γ Γ' k _ _ _ _ _ n r φ hN hp hn hr
  apply isIrr_comp_of_range
  rw [isIrr_iff]
  by_contra hred
  haveI : φ.range.FiniteIndex := ⟨hp.ne_zero⟩
  have hcomm : commutator Γ ≤ φ.range := by
    haveI : Fact (φ.range.index).Prime := ⟨hp⟩
    haveI : IsCyclic (Γ ⧸ φ.range) := isCyclic_of_prime_card (p := φ.range.index) rfl
    rw [commutator, Subgroup.commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff]
    rw [← QuotientGroup.mk'_apply, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    letI := IsCyclic.commGroup (α := Γ ⧸ φ.range)
    exact mul_comm _ _
  obtain ⟨η, hη, hker, e, he⟩ := UpperTheory.V.AlgebraTools.twistOfRed k Γ (Fin n → k) (linRep r) φ.range
    (Nat.cast_ne_zero.mpr hp.ne_zero) hcomm ((isIrr_iff r).mp hr) hred
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hr.1 (Subsingleton.elim _ _)
  apply hη
  ext g
  have h1 : η g ^ φ.range.index = 1 := by
    rw [← map_pow]; exact hker (Subgroup.pow_index_mem _ g)
  have h2 : η g ^ n = 1 := by
    have hl : linRep r g ∘ₗ (e : (Fin n → k) →ₗ[k] (Fin n → k)) =
        (η g : k) • ((e : (Fin n → k) →ₗ[k] (Fin n → k)) ∘ₗ linRep r g) := LinearMap.ext fun v => he g v
    have hd := congrArg LinearMap.det hl
    rw [LinearMap.det_smul, LinearMap.det_comp, LinearMap.det_comp, Module.finrank_fin_fun] at hd
    have hu : IsUnit (LinearMap.det (linRep r g)) := ((Group.isUnit g).map (linRep r)).map LinearMap.det
    have hue : IsUnit (LinearMap.det (e : (Fin n → k) →ₗ[k] (Fin n → k))) := e.isUnit_det'
    have hne := mul_ne_zero hue.ne_zero hu.ne_zero
    apply Units.ext
    apply mul_right_cancel₀ hne
    rw [Units.val_pow_eq_pow_val, ← hd, Units.val_one, one_mul, mul_comm]
  have hc : Nat.Coprime φ.range.index n := Nat.coprime_of_lt_prime hn0 hn hp
  have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rw [hc, pow_one] at this
  simp [this]
