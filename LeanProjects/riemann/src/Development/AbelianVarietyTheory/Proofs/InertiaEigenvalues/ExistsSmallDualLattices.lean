import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR MeasureTheory Filter Topology

namespace GlobalTheory.JR.DualLattice

variable {F : Type} [NontriviallyNormedField F]

theorem stdChar_key {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) (y : F)
    (h : ∀ c : F, ‖c‖ ≤ 1 → ψ (c * y) = 1) : ‖y‖ ≤ 1 := by
  by_contra hy
  push Not at hy
  obtain ⟨x0, hx0, hx1⟩ := hψ.2
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy; linarith
  have hinv : ‖y⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hy
  have := h _ (hx1 _ hinv)
  rw [mul_assoc, inv_mul_cancel₀ hy0, mul_one] at this
  exact hx0 this

theorem stdChar_continuous {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) : Continuous ψ := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_)
  filter_upwards [Metric.closedBall_mem_nhds x one_pos] with y hy
  have : y = x + (y - x) := by ring
  rw [this, AddChar.map_add_eq_mul, hψ.1 (y - x) (by simpa [dist_eq_norm] using hy), mul_one]

variable {V : Type} [AddCommGroup V] [Module F V]

def box [IsUltrametricDist F] {ι : Type} (e : Module.Basis ι F V) (r : ℝ) (hr : 0 ≤ r) : AddSubgroup V where
  carrier := {x | ∀ i, ‖e.repr x i‖ ≤ r}
  zero_mem' := by intro i; simpa using hr
  add_mem' := by
    intro a b ha hb i
    rw [map_add, Finsupp.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))
  neg_mem' := by
    intro a ha i
    simpa using ha i

theorem mem_box [IsUltrametricDist F] {ι : Type} (e : Module.Basis ι F V) (r : ℝ) (hr : 0 ≤ r) (x : V) :
    x ∈ box e r hr ↔ ∀ i, ‖e.repr x i‖ ≤ r := Iff.rfl

noncomputable def coordHomeo [TopologicalSpace V] [IsModuleTopology F V] {ι : Type} [Fintype ι]
    (e : Module.Basis ι F V) : V ≃ₜ (ι → F) :=
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd F V
  { e.equivFun.toEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.equivFun.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.equivFun.symm.toLinearMap }

theorem box_eq [IsUltrametricDist F] [TopologicalSpace V] [IsModuleTopology F V] {ι : Type} [Fintype ι]
    (e : Module.Basis ι F V) (r : ℝ) (hr : 0 ≤ r) :
    (box e r hr : Set V) = coordHomeo e ⁻¹' Metric.closedBall 0 r := by
  ext x
  rw [SetLike.mem_coe, mem_box, Set.mem_preimage, mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hr]
  rfl

theorem box_open_compact [IsUltrametricDist F] [LocallyCompactSpace F] [TopologicalSpace V]
    [IsModuleTopology F V] {ι : Type} [Fintype ι]
    (e : Module.Basis ι F V) (r : ℝ) (hr : 0 < r) :
    IsOpen (box e r hr.le : Set V) ∧ IsCompact (box e r hr.le : Set V) := by
  haveI : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  rw [box_eq]
  exact ⟨(IsUltrametricDist.isOpen_closedBall _ hr.ne').preimage (coordHomeo e).continuous,
    (coordHomeo e).isCompact_preimage.2 (isCompact_closedBall _ _)⟩

theorem box_dual [IsUltrametricDist F] {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) {ι : Type} [Fintype ι]
    (e e' : Module.Basis ι F V) (B : V → V → F)
    (hB : ∀ x y, B x y = ∑ i, e.repr x i * e'.repr y i) (t : F) (ht : t ≠ 0) (y : V) :
    y ∈ box e' ‖t⁻¹‖ (norm_nonneg _) ↔ ∀ x ∈ box e ‖t‖ (norm_nonneg _), ψ (B x y) = 1 := by
  classical
  have htp : 0 < ‖t‖ := norm_pos_iff.2 ht
  constructor
  · intro hy x hx
    apply hψ.1
    rw [hB]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul]
    calc _ ≤ ‖t‖ * ‖t⁻¹‖ := mul_le_mul (hx i) (hy i) (norm_nonneg _) (norm_nonneg _)
      _ = 1 := by rw [← norm_mul, mul_inv_cancel₀ ht, norm_one]
  · intro h i
    have h1 : ‖t * e'.repr y i‖ ≤ 1 := by
      refine stdChar_key hψ _ fun c hc => ?_
      have hx : (c * t) • e i ∈ box e ‖t‖ (norm_nonneg _) := by
        intro j
        rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
        split_ifs
        · rw [smul_eq_mul, mul_one, norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) hc
        · simp
      have := h _ hx
      rw [hB, Finset.sum_eq_single i] at this
      · simpa [mul_assoc] using this
      · intro j _ hj
        simp [Finsupp.single_apply, hj.symm]
      · simp
    rw [norm_mul] at h1
    rw [norm_inv, ← one_div, le_div_iff₀ htp, mul_comm]
    exact h1

end GlobalTheory.JR.DualLattice

open GlobalTheory.JR.DualLattice in

theorem GlobalTheory.JR.exists_small_dual_lattices : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → Continuous (fun p : V × V => ψ (β p.1 p.2)) ∧ (∀ U ∈ 𝓝 (0 : V), ∃ M N : AddSubgroup V, (M : Set V) ⊆ U ∧ IsOpen (M : Set V) ∧ IsCompact (M : Set V) ∧ IsOpen (N : Set V) ∧ IsCompact (N : Set V) ∧ (∀ y, y ∈ N ↔ ∀ x ∈ M, ψ (β x y) = 1) ∧ (∀ x, x ∈ M ↔ ∀ y ∈ N, ψ (β x y) = 1)) := by
  intro F _ _ _ ψ hψ V _ _ _ _ _ β hs hβ
  classical
  let e := Module.finBasis F V
  let e' := β.dualBasis hβ e
  have hB : ∀ x y, β x y = ∑ i, e.repr x i * e'.repr y i := by
    intro x y
    conv_lhs => rw [← e.sum_repr x]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, hs.eq]
  refine ⟨(stdChar_continuous hψ).comp ?_, fun U hU => ?_⟩
  · simp only [hB]
    refine continuous_finset_sum _ fun i _ => ?_
    exact (((continuous_apply i).comp (coordHomeo e).continuous).comp continuous_fst).mul
      (((continuous_apply i).comp (coordHomeo e').continuous).comp continuous_snd)
  · have h0 : (coordHomeo e).symm 0 = 0 := map_zero e.equivFun.symm
    have hU' : (coordHomeo e).symm ⁻¹' U ∈ 𝓝 (0 : Fin (Module.finrank F V) → F) :=
      (coordHomeo e).symm.continuous.continuousAt.preimage_mem_nhds (by rwa [h0])
    obtain ⟨ε, hε, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hU'
    obtain ⟨t, ht0, htε⟩ := NormedField.exists_norm_lt F hε
    have ht : t ≠ 0 := norm_pos_iff.1 ht0
    have hti : 0 < ‖t⁻¹‖ := norm_pos_iff.2 (inv_ne_zero ht)
    refine ⟨box e ‖t‖ (norm_nonneg _), box e' ‖t⁻¹‖ (norm_nonneg _), ?_,
      (box_open_compact e _ ht0).1, (box_open_compact e _ ht0).2,
      (box_open_compact e' _ hti).1, (box_open_compact e' _ hti).2,
      box_dual hψ e e' (fun x y => β x y) hB t ht, fun x => ?_⟩
    · rw [box_eq]
      intro x hx
      have := hsub (Metric.closedBall_subset_closedBall htε.le hx)
      simpa using this
    · have := box_dual hψ e' e (fun y x => β x y)
        (fun y x => by simp only [hB, mul_comm]) t⁻¹ (inv_ne_zero ht) x
      simpa only [inv_inv] using this
