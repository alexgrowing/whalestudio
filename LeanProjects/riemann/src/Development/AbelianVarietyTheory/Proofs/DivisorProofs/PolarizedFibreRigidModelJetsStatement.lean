import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedFibreRigidModelJets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarized_fibre_rigid_model_jets : ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K) (K'' : Type) [Field K''] [NumberField K''] [Algebra K K''] (P : Out.PolAV (Sp K'')) (ψ : P.A.left ⟶ F.P₀.A.left) (AA : Over (Sp (𝓞 K''))) [GrpObj AA] [IsCommMonObj AA] (φ : P.A.left ⟶ AA.left) (MM : RigLB AA) (N : ℕ) (w : LB.Iso (MM.L.pull φ) (lbPow P.L N)) (v' : Fin F.P₀.g → (epsR K'' ⟶ P.A)), Hypotheses2 → GlobalTheory.IsPolFibre (algebraMap K K'') F.P₀ P ψ → IsModel w → (∀ k, GlobalTheory.IsVecOver (algebraMap K K'') ψ (F.v k) (v' k)) → ∀ z ∈ latBC K'' F.lieLat, ∃ Y : epsR (𝓞 K'') ⟶ AA, IsTangent Y ∧ GlobalTheory.IsVecOver (algebraMap (𝓞 K'') K'') φ Y (tanComb z v') := by
  first | exact @GlobalTheory.SecJet.exists_tangent_of_mem_latBC | exact GlobalTheory.SecJet.exists_tangent_of_mem_latBC | (intros; apply GlobalTheory.SecJet.exists_tangent_of_mem_latBC <;> assumption)
