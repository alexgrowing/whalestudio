import Mathlib
import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualInt

theorem linK_smul {O : Type} [CommRing O] [IsDomain O] {V : Type} [AddCommGroup V] [Module O V]
    [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]
    (φ : V →ₗ[O] FractionRing O) (c : FractionRing O) (v : V) : φ (c • v) = c * φ v :=
  (LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) (FractionRing O) φ).map_smul c v

theorem exists_pairKO_eq_inv_unif : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT'), ∀ ϖ : O, Irreducible ϖ → ∀ (n : ℕ) (f : ↥D.T'), f ∉ powSub (M := ↥D.T') ϖ n → ∃ x : VT ⧸ D.T, ϖ ^ n • x = 0 ∧ pairKO D.bT D.T x f = toKO O ((algebraMap O (FractionRing O) ϖ)⁻¹) := by
  intro O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ D ϖ hϖ n f hf
  set π : (FractionRing O) := algebraMap O (FractionRing O) ϖ with hπ
  have hπ0 : π ≠ 0 := by
    rw [hπ]; exact (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hϖ.ne_zero
  have hpn : ∀ y : VT', ϖ ^ n • y = π ^ n • y := fun y => by
    rw [← algebraMap_smul (FractionRing O) (ϖ ^ n) y, map_pow]
  have hpnT : ∀ y : VT, ϖ ^ n • y = π ^ n • y := fun y => by
    rw [← algebraMap_smul (FractionRing O) (ϖ ^ n) y, map_pow]
  set f' : VT' := (π ^ n)⁻¹ • (f : VT') with hf'
  have hff' : ϖ ^ n • f' = f := by
    rw [hpn, hf', smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hπ0), one_smul]
  clear_value f' π
  have hnot : f' ∉ D.T' := by
    intro h
    apply hf
    refine mem_powSub.2 ⟨⟨f', h⟩, ?_⟩
    ext
    simp [hff']
  have hnot' : ¬ ∀ x ∈ D.T, D.bT x f' ∈ (1 : Submodule O (FractionRing O)) := hnot
  push_neg at hnot'
  obtain ⟨v, hvT, hu⟩ := hnot'
  set u := D.bT v f' with hu_def
  have hu0 : u ≠ 0 := by
    intro h; apply hu; rw [h]; exact Submodule.zero_mem _
  have hnotint : ¬ IsLocalization.IsInteger O u := by
    rintro ⟨o, ho⟩; exact hu (Submodule.mem_one.2 ⟨o, ho⟩)
  obtain ⟨w, hw⟩ : IsLocalization.IsInteger O u⁻¹ :=
    (ValuationRing.isInteger_or_isInteger O u).resolve_left hnotint
  have hwnu : w ∉ nonunits O → False := by
    intro h
    rw [mem_nonunits_iff, not_not] at h
    obtain ⟨w', hw'⟩ := h
    apply hnotint
    refine ⟨(w'⁻¹ : Oˣ), ?_⟩
    have : algebraMap O (FractionRing O) (w' : O) * u = 1 := by
      rw [hw', hw, inv_mul_cancel₀ hu0]
    have h2 : algebraMap O (FractionRing O) ((w'⁻¹ : Oˣ) : O) * algebraMap O (FractionRing O) (w' : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    calc algebraMap O (FractionRing O) ((w'⁻¹ : Oˣ) : O) = algebraMap O (FractionRing O) ((w'⁻¹ : Oˣ) : O) * (algebraMap O (FractionRing O) (w' : O) * u) := by rw [this, mul_one]
      _ = u := by rw [← mul_assoc, h2, one_mul]
  have hwm : w ∈ IsLocalRing.maximalIdeal O := by
    by_contra h
    exact hwnu h
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton'] at hwm
  obtain ⟨o, ho⟩ := hwm
  have hkey : D.bT (o • v) f' = π⁻¹ := by
    rw [D.bT.map_smul o v, LinearMap.smul_apply, Algebra.smul_def, ← hu_def]
    have h1 : algebraMap O (FractionRing O) o * π = u⁻¹ := by rw [hπ, ← map_mul, ho, hw]
    have : algebraMap O (FractionRing O) o = u⁻¹ * π⁻¹ := by
      rw [← h1, mul_assoc, mul_inv_cancel₀ hπ0, mul_one]
    rw [this, mul_comm u⁻¹, mul_assoc, inv_mul_cancel₀ hu0, mul_one]
  refine ⟨Submodule.Quotient.mk ((π ^ n)⁻¹ • (o • v)), ?_, ?_⟩
  · rw [← Submodule.Quotient.mk_smul, hpnT, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hπ0), one_smul,
      Submodule.Quotient.mk_eq_zero]
    exact D.T.smul_mem o hvT
  · rw [pairKO_mk, ← hkey]
    congr 1
    have e1 : D.bT ((π ^ n)⁻¹ • (o • v)) f = (π ^ n)⁻¹ * D.bT (o • v) f :=
      linK_smul (D.bT.flip (f : VT')) ((π ^ n)⁻¹) (o • v)
    have e2 : D.bT (o • v) ((π ^ n)⁻¹ • (f : VT')) = (π ^ n)⁻¹ * D.bT (o • v) f :=
      linK_smul (D.bT (o • v)) ((π ^ n)⁻¹) (f : VT')
    rw [e1, hf', e2]

end GlobalTheory.LocDualInt
