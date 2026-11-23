import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidModelSectionJetEvaluation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigid_model_section_jet_evaluation : ∀ (K'' : Type) [Field K''] [NumberField K''] (P : Out.PolAV (Sp K'')) (AA : Over (Sp (𝓞 K''))) [GrpObj AA] [IsCommMonObj AA] (φ : P.A.left ⟶ AA.left) (MM : RigLB AA) (N : ℕ) (w : LB.Iso (MM.L.pull φ) (lbPow P.L N)) (r : ℕ) (b : Fin r → (lbPow P.L N).Sec) (i₀ : (lbPow P.L N).ι) (y : epsR K'' ⟶ P.A) (Y : epsR (𝓞 K'') ⟶ AA) (c : Fin r → K'') (t : MM.L.Sec) (i : ℕ), IsModel w → ⊤ ≤ (eSec P.A) ⁻¹ᵁ (lbPow P.L N).U i₀ → IsTangent Y → GlobalTheory.IsVecOver (algebraMap (𝓞 K'') K'') φ Y y → SecMaps w (secPull t φ) (secComb P.A.hom c b) → c ∈ filt (jetFun y i₀ (rigVal w i₀) b) i → IsIntegral ℤ (jetFun y i₀ (rigVal w i₀) b i c) := by
  first | exact @GlobalTheory.JetIntegral.isIntegral_jetFun | exact GlobalTheory.JetIntegral.isIntegral_jetFun | (intros; apply GlobalTheory.JetIntegral.isIntegral_jetFun <;> assumption)
