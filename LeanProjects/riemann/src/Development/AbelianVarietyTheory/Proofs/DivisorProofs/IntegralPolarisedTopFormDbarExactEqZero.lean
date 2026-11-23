import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAntiholomorphicJacobianEqZeroPoincareGroStatement

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem integral_mixTop_mdbar_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (θ : Fin n → Fin n → V n → Matrix r r ℂ) (j : Fin n) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ i a, ∀ v ∈ offHyp S U, MContDiffAt 2 (θ i a) v) → (∀ a, ∀ v ∈ offHyp S U, v ∉ K → θ j a v = 0) → (∀ v ∈ offHyp S U, v ∈ K → ∀ a p q, ‖θ j a v p q‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, v ∈ K → ∀ i a b p q, ‖mdbar (θ i a) v (coordVec b) p q‖ * (poinWt S v a * poinWt S v b) ≤ c) → IntegrableOn (fun v => mixTop fun i a b => mdbar (θ i a) v (coordVec b)) (offHyp S U) ∧ ∫ v in offHyp S U, (mixTop fun i a b => mdbar (θ i a) v (coordVec b)) = 0 := by
  intro n r _ _ S U K θ j c hU hK hKU hS hθ h0 hb hd
  have key : ∀ (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      IntegrableOn (fun v => (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det)
        (offHyp S U) ∧
      ∫ v in offHyp S U, (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det = 0 := by
    intro p π u
    exact GlobalTheory.T.integral_antiholomorphicJacobian_eq_zero_poincareGrowth S U K (fun i x => θ i (u i) x (p i) (p (π i))) j u c hU hK hKU hS
      (fun i v hv => (hθ i (u i) v hv (p i) (p (π i))).contDiffWithinAt)
      (fun v hv hvK => by simp [h0 (u j) v hv hvK])
      (fun v hv hvK => hb v hv hvK (u j) _ _)
      (fun v hv hvK i b => hd v hv hvK i (u i) b (p i) (p (π i)))
  have hI : ∀ (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      Integrable (fun v => ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det)
        (volume.restrict (offHyp S U)) := fun p π u => Integrable.const_mul (key p π u).1 _
  have hI2 : ∀ (p : Fin n → r) (π : Equiv.Perm (Fin n)),
      Integrable (fun v => ∑ u : Equiv.Perm (Fin n), ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det)
        (volume.restrict (offHyp S U)) := fun p π => integrable_finset_sum _ fun u _ => hI p π u
  have hI3 : ∀ (p : Fin n → r),
      Integrable (fun v => ∑ π : Equiv.Perm (Fin n), ∑ u : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => mdbar (θ i (u i)) v (coordVec b) (p i) (p (π i))).det)
        (volume.restrict (offHyp S U)) := fun p => integrable_finset_sum _ fun π _ => hI2 p π
  unfold mixTop
  refine ⟨Integrable.const_mul (integrable_finset_sum _ fun p _ => hI3 p) _, ?_⟩
  rw [integral_const_mul, integral_finset_sum _ fun p _ => hI3 p]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun p _ => ?_)
  rw [integral_finset_sum _ fun π _ => hI2 p π]
  refine Finset.sum_eq_zero fun π _ => ?_
  rw [integral_finset_sum _ fun u _ => hI p π u]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [integral_const_mul, (key p π u).2, mul_zero]

end GlobalTheory.GoodTop
