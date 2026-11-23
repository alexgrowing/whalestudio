import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeDensitySymmetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDensityHermitianMetrics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobiDensityWeightedThetaIntegralZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeEqFormDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeWeightedRootProductSum
open Filter Topology MeasureTheory Matrix
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (emb jacDens)
open GlobalTheory.FlagFibre (Low uni)
open GlobalTheory.FlagFormDeg (apolar)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open scoped ContDiff ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vandermonde_density_symmetric : ∀ r e : ℕ, ∃ κ : ℝ, ∀ D : ℕ, D = e + 2 + Fintype.card (Low r) → ∀ (I : Type) [Fintype I] (c : I → ℝ) (m : I → Option (Fin r) → ℤ), ∑ j, c j • lin (fun o => (m j o : ℝ)) ^ D = vdmPol r e → ∀ v : Fin (e + 2) → Option (Fin r) → ℂ, ∑ j, (c j : ℂ) * (D.factorial * ((∏ k, ∑ o, (m j o : ℂ) * v k o) * ∏ s : Low r, ((m j (some s.1.1) : ℂ) - m j (some s.1.2)))) = κ * ∑ t : Equiv.Perm (Fin (e + 2)), (((r : ℂ) + 1) * ∑ i, v (t 0) (some i) * v (t 1) (some i) - (∑ i, v (t 0) (some i)) * ∑ i, v (t 1) (some i)) * ∏ p : Fin e, v (t p.succ.succ) none := by
  first | exact @GlobalTheory.VdmPolar.polar_vdmPol | exact GlobalTheory.VdmPolar.polar_vdmPol | (intros; apply GlobalTheory.VdmPolar.polar_vdmPol <;> assumption)
