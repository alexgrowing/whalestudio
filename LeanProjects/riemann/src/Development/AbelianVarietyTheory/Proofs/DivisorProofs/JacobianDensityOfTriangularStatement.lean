import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDensityOfTriangular
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
theorem _root_.GlobalTheory.T.jacobian_density_of_triangular : ∀ (n r D : ℕ) (ε : Fin D ≃ Fin n ⊕ Low r) (G : V n → Matrix (Fin r) (Fin r) ℂ) (ψ : V n → ℝ) (u : V n), MContDiffAt ∞ G u → (∀ᶠ v in 𝓝 u, (G v).PosDef) → ContDiffAt ℝ 2 ψ u → ∀ (x : Low r → ℂ) (T : Matrix (Fin r) (Fin r) ℂ), (∀ a c : Fin r, c < a → T a c = 0) → chg T (chg (uni x) (G u)) = 1 → ∃ J : Matrix (Fin D) (Fin D) ℂ, ‖J.det‖ ^ 2 = jacDens (G u) x ∧ (∀ i : Fin r, cHess D (fun v => (rootWt ε G i v : ℂ)) (pt ε u x) = chg J ((fromBlocks (Matrix.of fun j l : Fin n => ((uni x * T)⁻¹ * curv G u (bas n j) (bas n l) * (uni x * T)) i i) 0 0 (diagonal fun s : Low r => ((if i = s.1.1 then 1 else 0) - if i = s.1.2 then 1 else 0 : ℂ))).submatrix ε ε)) ∧ cHess D (fun v => (ψ (base ε v) : ℂ)) (pt ε u x) = chg J ((fromBlocks (cHess n (fun v => (ψ v : ℂ)) u) 0 0 (0 : Matrix (Low r) (Low r) ℂ)).submatrix ε ε) := by
  first | exact @GlobalTheory.ArchLim.NormalBase.normal_coords_base | exact GlobalTheory.ArchLim.NormalBase.normal_coords_base | (intros; apply GlobalTheory.ArchLim.NormalBase.normal_coords_base <;> assumption)
