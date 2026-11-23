import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound

namespace GlobalTheory.SatakeBound.Rep

section Abstract

variable {G X V : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]

theorem norm_le_card {ι : Type} {π : Representation ℂ G V} (hπ : IsUnitarisable π) {v : V} (hv : v ≠ 0)
    (S : Finset ι) (g : ι → G) (l : ℂ) (h : ∑ c ∈ S, π (g c) v = l • v) : ‖l‖ ≤ S.card := by
  obtain ⟨B, b1, b2, b3⟩ := hπ
  letI : InnerProductSpace.Core ℂ V := UnitInd.core B b1 b2
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore _
  have hn : ∀ x : G, ‖π x v‖ = ‖v‖ := fun x => by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) v]
    exact congrArg (fun z : ℂ => √(RCLike.re z)) (b3 x v v)
  have h1 : ‖l‖ * ‖v‖ ≤ S.card * ‖v‖ := by
    rw [← norm_smul, ← h]
    refine (norm_sum_le _ _).trans ?_
    simp [hn]
  exact le_of_mul_le_mul_right h1 (norm_pos_iff.2 hv)

theorem sum_fixed (ρ : Representation ℂ G X) (K : Subgroup G) {w : X} (hw : ∀ x ∈ K, ρ x w = w)
    (S : Finset (G ⧸ K)) (hS : ∀ x ∈ K, ∀ c ∈ S, x • c ∈ S) (x : G) (hx : x ∈ K) :
    ρ x (∑ c ∈ S, ρ c.out w) = ∑ c ∈ S, ρ c.out w := by
  rw [map_sum]
  refine Finset.sum_nbij' (fun c => x • c) (fun c => x⁻¹ • c) (hS x hx) (hS _ (inv_mem hx))
    (fun c _ => by simp) (fun c _ => by simp) fun c _ => ?_
  have h1 : x • c = ((x * c.out : G) : G ⧸ K) := by
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rfl
  obtain ⟨y, hy⟩ := QuotientGroup.mk_out_eq_mul K (x * c.out)
  rw [h1, hy, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hw y y.2]

theorem exists_vector [TopologicalSpace G] [IsTopologicalGroup G] {ρ : Representation ℂ G X}
    {π : Representation ℂ G V} (hρ : IsSmooth ρ) (hπ : IsUnitarisable π) {K : Subgroup G}
    (hK : IsCompact (K : Set G)) (f : ρ.IntertwiningMap π) (hf : Function.Surjective f)
    (hs : fixed π K ≠ ⊥) (E : X →ₗ[ℂ] ℂ) (hE : ∀ u : X, (∀ x ∈ K, ρ x u = u) → E u = 0 → u = 0) :
    ∃ w : X, (∀ x ∈ K, ρ x w = w) ∧ E w = 1 ∧ ∀ S : Finset (G ⧸ K), (∀ x ∈ K, ∀ c ∈ S, x • c ∈ S) →
      ‖∑ c ∈ S, E (ρ c.out w)‖ ≤ S.card := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
  obtain ⟨u, rfl⟩ := hf v
  obtain ⟨w, hw, hfw⟩ := IwahoriOnto.exists_fixed_map_eq hρ hK f.toLinearMap u fun h hh => by
    show f (ρ h u) = f u
    rw [f.isIntertwining]
    simpa using hv ⟨h, hh⟩
  have hw' : ∀ x ∈ K, ρ x w = w := fun x hx => by simpa using hw ⟨x, hx⟩
  have hfw0 : f w ≠ 0 := fun h => hv0 (hfw.symm.trans h)
  have hEw : E w ≠ 0 := fun h => hfw0 (by rw [hE w hw' h, map_zero])
  obtain ⟨z, hz, hEz, hfz⟩ : ∃ z : X, (∀ x ∈ K, ρ x z = z) ∧ E z = 1 ∧ f z ≠ 0 :=
    ⟨(E w)⁻¹ • w, fun x hx => by rw [map_smul, hw' x hx], by simp [hEw], by
      rw [map_smul]; exact smul_ne_zero (inv_ne_zero hEw) hfw0⟩
  refine ⟨z, hz, hEz, fun S hS => norm_le_card hπ hfz S (fun c => c.out) _ ?_⟩
  have h1 := hE (∑ c ∈ S, ρ c.out z - (∑ c ∈ S, E (ρ c.out z)) • z)
    (fun x hx => by rw [map_sub, sum_fixed ρ K hz S hS x hx, map_smul, hz x hx])
    (by rw [map_sub, map_sum, map_smul, hEz, smul_eq_mul, mul_one, sub_self])
  have h2 := congrArg f (sub_eq_zero.1 h1)
  rw [map_sum, map_smul] at h2
  rw [← h2]
  exact Finset.sum_congr rfl fun c _ => (f.isIntertwining _ _ _ _).symm

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem law (α : Fin n → ℂˣ)
    (f : IndSp (points (Fin n)) ((ofChar (torusChar fun i => unrChar k (α i))).comp
      (leviTorus k (Fin n)).symm.toMonoidHom))
    (b : GL (Fin n) k) (hb : b ∈ borel k (Fin n)) (t : Fin n → kˣ)
    (ht : ∀ i, (b : Matrix (Fin n) (Fin n) k) i i = t i) (g : GL (Fin n) k) :
    f.1.1 (b * g) = (∏ i : Fin n, ((α i : ℂ) * (((resCard k : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ))
      ^ ord k (t i)) * f.1.1 g := by
  refine (parInd_law _ _ f ⟨b, hb⟩ g).trans ?_
  show _ • ofChar _ _ (f.1.1 g) = _
  rw [ofChar_apply, torusChar_apply, deltaHalf_apply, smul_eq_mul, ← mul_assoc,
    Units.coe_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have e : Matrix.GeneralLinearGroup.det (leviProj _ (points (Fin n)) ⟨b, hb⟩ i) = t i := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    exact ht i
  show _ * ((unrChar k (α i)
    (Matrix.GeneralLinearGroup.det (leviProj _ (points (Fin n)) ⟨b, hb⟩ i)) : ℂˣ) : ℂ) = _
  have e2 : ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2) =
      ((-(((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ) := by
    rw [modExp_fin _ (fun _ => by simp)]
    push_cast
    ring
  have hq : (0 : ℝ) ≤ resCard k := Nat.cast_nonneg _
  rw [e, e2, val_absPow_ofReal, unrChar_apply, Units.val_zpow_eq_zpow_val, mul_zpow, mul_comm,
    GlobalTheory.LGrp.nabs_eq_zpow, ← Complex.ofReal_zpow, ← Real.rpow_intCast, ← Real.rpow_intCast,
    ← Real.rpow_mul hq, ← Real.rpow_mul hq]
  congr 3
  push_cast
  ring

theorem exists_sph : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (α : Fin n → ℂˣ), IsUnitarisable π → HasSatake π α → ∃ φ : GL (Fin n) k → ℂ, IsBorelSph k (fun i : Fin n => (α i : ℂ) * (((resCard k : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ)) φ ∧ HasBoundedSums k φ := by
  intro k _ _ _ _ n V _ _ π α hu ⟨_, hs, S, f, hf⟩
  have hsm : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth ⟨S, .id _, Function.surjective_id⟩ (isSmooth_parInd _ _)
  let E : S.toSubmodule →ₗ[ℂ] ℂ := ⟨⟨fun u => u.1.1.1 1, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  have hr : ∀ u : S.toSubmodule, (∀ x ∈ KO k (Fin n), S.toRepresentation x u = u) →
      ∀ g, ∀ x ∈ KO k (Fin n), u.1.1.1 (g * x) = u.1.1.1 g := fun u h g x hx =>
    congrArg (fun z : S.toSubmodule => z.1.1.1 g) (h x hx)
  obtain ⟨w, hw, hw1, hb⟩ := exists_vector hsm hu SplitFlip.isCompact_KO f hf hs E fun u h h0 => by
    refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun g => ?_)))
    obtain ⟨b, hb, x, hx, rfl⟩ := iwasawa_blockTriangular k (Fin n) Fin.val g
    have h1 := parInd_law _ _ u.1 ⟨b, (mem_borel _).2 hb⟩ 1
    have h2 : u.1.1.1 1 = 0 := h0
    rw [h2, map_zero, smul_zero, mul_one] at h1
    exact (hr u h b x hx).trans h1
  refine ⟨w.1.1.1, ⟨hr w hw, fun b hb t ht => ?_⟩, fun T hT => ?_⟩
  · have h1 := law α w.1 b hb t ht 1
    have h2 : w.1.1.1 1 = 1 := hw1
    rwa [h2, mul_one, mul_one] at h1
  · refine le_of_eq_of_le ?_ (hb T hT)
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    show _ = w.1.1.1 (1 * c.out)
    rw [one_mul]

end GlobalTheory.SatakeBound.Rep
