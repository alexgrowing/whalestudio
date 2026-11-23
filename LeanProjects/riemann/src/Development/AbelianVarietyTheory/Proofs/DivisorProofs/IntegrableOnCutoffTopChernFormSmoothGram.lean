import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPolarisedTopChernCoeff

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma continuousAt_cutoff_mul_chern_form_coeff {n : ℕ} {r : Type} [Fintype r]
    [DecidableEq r] {G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ} {ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n}
    (hG : _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G v) (hdet : IsUnit (G v).det) (hρ : ContinuousAt ρ v) :
    ContinuousAt (fun x => (ρ x : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G x)
      v := by
  refine ContinuousAt.mul (Complex.continuous_ofReal.continuousAt.comp (f := ρ) hρ) ?_
  refine _root_.GlobalTheory.GoodTop.continuousAt_mixTop (K := fun x _ => _root_.GlobalTheory.GoodTop.curvAt G x)
    fun i a b p q => ?_
  have h := hG.curv (j := 0) hdet
    (by rw [zero_add]; first | exact le_top | exact_mod_cast (le_top : ((2 : ℕ∞) ≤ ⊤)) | exact WithTop.coe_le_coe.2 le_top)
    (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) p q
  exact h.continuousAt

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in

theorem _root_.GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth :
    ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (U K : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) (G₀ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ),
      IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → ContDiffOn ℝ ∞ ρ U →
      (∀ v ∈ U, v ∉ K → ρ v = 0) → IntegrableOn (fun v => (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) U := by
  intro n r _ _ U K G₀ ρ hU hK hKU hG₀ hρ hρK
  have hcont : ContinuousOn
      (fun v => (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) K :=
    fun v hv => (continuousAt_cutoff_mul_chern_form_coeff (hG₀ v (hKU hv)).1 (hG₀ v (hKU hv)).2
      (hρ.contDiffAt (hU.mem_nhds (hKU hv))).continuousAt).continuousWithinAt
  refine (hcont.integrableOn_compact hK).of_forall_diff_eq_zero hU.measurableSet
    fun v hv => ?_
  rw [hρK v hv.1 hv.2, Complex.ofReal_zero, zero_mul]

end GlobalTheory.GoodTop
