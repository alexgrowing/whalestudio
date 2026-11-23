import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs

noncomputable section

open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

section HS

variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']

theorem hsA_smul (c : ℂ) (A : V' →L[ℂ] V) : hsA (c • A) = ‖c‖ ^ 2 * hsA A := by
  unfold Formalism.L2.SG.Pf.EnergyAbs.hsA
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.smul_apply, norm_smul, mul_pow]

private theorem sum_norm_inner_stdBasis_sq_eq_norm_sq {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (x : E) :
    ∑ i, ‖⟪stdOrthonormalBasis ℂ E i, x⟫_ℂ‖ ^ 2 = ‖x‖ ^ 2 := by
  exact (stdOrthonormalBasis ℂ E).sum_sq_norm_inner_right x

theorem hsA_eq_adjoint (A : V' →L[ℂ] V) :
    hsA A = ∑ i, ‖(ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V i)‖ ^ 2 := by
  unfold Formalism.L2.SG.Pf.EnergyAbs.hsA
  calc ∑ i, ‖A (stdOrthonormalBasis ℂ V' i)‖ ^ 2
      = ∑ i, ∑ j, ‖⟪stdOrthonormalBasis ℂ V j, A (stdOrthonormalBasis ℂ V' i)⟫_ℂ‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [sum_norm_inner_stdBasis_sq_eq_norm_sq]
    _ = ∑ j, ∑ i, ‖⟪stdOrthonormalBasis ℂ V' i,
          (ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V j)⟫_ℂ‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
    _ = ∑ j, ‖(ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V j)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sum_norm_inner_stdBasis_sq_eq_norm_sq]

private theorem norm_sq_apply_of_inner_preserving {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : E →L[ℂ] E) (hU : ∀ a b, ⟪U a, U b⟫_ℂ = ⟪a, b⟫_ℂ) (v : E) : ‖U v‖ ^ 2 = ‖v‖ ^ 2 := by
  have h := hU v v
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

theorem hsA_conj (U : V →L[ℂ] V) (U' : V' →L[ℂ] V') (hU : ∀ a b, ⟪U a, U b⟫_ℂ = ⟪a, b⟫_ℂ)
    (hU' : ∀ a b, ⟪U' a, U' b⟫_ℂ = ⟪a, b⟫_ℂ) (A : V' →L[ℂ] V) :
    hsA (U.comp (A.comp (ContinuousLinearMap.adjoint U'))) = hsA A := by
  have h1 : Formalism.L2.SG.Pf.EnergyAbs.hsA (U.comp (A.comp (ContinuousLinearMap.adjoint U'))) =
      Formalism.L2.SG.Pf.EnergyAbs.hsA (A.comp (ContinuousLinearMap.adjoint U')) := by
    unfold Formalism.L2.SG.Pf.EnergyAbs.hsA
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.comp_apply]
    exact norm_sq_apply_of_inner_preserving U hU _
  rw [h1, hsA_eq_adjoint, hsA_eq_adjoint A]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.comp_apply]
  exact norm_sq_apply_of_inner_preserving U' hU' _

def hsL : (V' →L[ℂ] V) →ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ V') => V) where
  toFun A := WithLp.toLp 2 (fun j => A (stdOrthonormalBasis ℂ V' j))
  map_add' A B := by
    ext j
    simp
  map_smul' c A := by
    ext j
    simp

def hsC : (V' →L[ℂ] V) →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ V') => V) :=
  LinearMap.toContinuousLinearMap hsL

theorem norm_hsC (A : V' →L[ℂ] V) : ‖hsC A‖ = Real.sqrt (hsA A) := by
  rw [PiLp.norm_eq_of_L2]
  rfl

theorem sqrt_hsA_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} (f : α → (V' →L[ℂ] V))
    (hf : Integrable f μ) :
    Real.sqrt (hsA (∫ x, f x ∂μ)) ≤ ∫ x, Real.sqrt (hsA (f x)) ∂μ := by
  simp_rw [← norm_hsC]
  rw [← ContinuousLinearMap.integral_comp_comm _ hf]
  exact norm_integral_le_integral_norm _

theorem sqrt_hsA_le_add_sub (A B : V' →L[ℂ] V) :
    Real.sqrt (hsA A) ≤ Real.sqrt (hsA B) + Real.sqrt (hsA (A - B)) := by
  simp_rw [← norm_hsC]
  have h : hsC A = hsC B + hsC (A - B) := by
    simp [map_sub]
  rw [h]
  exact norm_add_le _ _

end HS

section Rep

variable {G : Type} [Group G] [TopologicalSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH]

theorem rep_mul_apply {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (x y : G) (a : HH) :
    σ x (σ y a) = σ (x * y) a := by
  obtain ⟨-, hmul, -, -⟩ := hσ
  rw [hmul, ContinuousLinearMap.mul_apply]

end Rep

section Kernel

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

end Kernel

section Quot

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

theorem quot_map_inv {μ μS ν : Measure G} [SFinite ν] [SFinite μS] (hq : IsQuot μ μS ν)
    (hinv : μS.map (fun x => x⁻¹) = μS) :
    μ = (ν.prod μS).map (fun p => p.2⁻¹ * p.1) := by
  have hm : Measurable (fun p : G × G => p.2⁻¹ * p.1) := measurable_snd.inv.mul measurable_fst
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs)]
  have h := hq (s.indicator 1) (measurable_one.indicator hs)
  rw [lintegral_indicator_one hs] at h
  rw [h]
  refine lintegral_congr fun x => ?_
  have hx : MeasurableSet ((fun t : G => t * x) ⁻¹' s) := measurable_mul_const x hs
  have hx' : MeasurableSet ((fun t : G => t⁻¹ * x) ⁻¹' s) := (measurable_inv.mul_const x) hs
  calc ∫⁻ t, s.indicator (1 : G → ℝ≥0∞) (t * x) ∂μS
      = ∫⁻ t, ((fun t : G => t * x) ⁻¹' s).indicator (1 : G → ℝ≥0∞) t ∂μS := rfl
    _ = μS ((fun t : G => t * x) ⁻¹' s) := lintegral_indicator_one hx
    _ = (μS.map (fun t => t⁻¹)) ((fun t : G => t⁻¹ * x) ⁻¹' s) := by
        rw [Measure.map_apply measurable_inv hx']
        congr 1
        ext t
        simp
    _ = μS ((fun t : G => t⁻¹ * x) ⁻¹' s) := by rw [hinv]
    _ = _ := rfl

end Quot

end Formalism.L2.S.Pv.EnergyAbs
