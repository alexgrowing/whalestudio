import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedModelSectionNonvanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidified_model_section_nonvanishing : ∀ (K'' : Type) [Field K''] [NumberField K''] (P : Out.PolAV (Sp K'')) (AA : Over (Sp (𝓞 K''))) [GrpObj AA] [IsCommMonObj AA] (φ : P.A.left ⟶ AA.left) (MM : RigLB AA) (N : ℕ) (w : LB.Iso (MM.L.pull φ) (lbPow P.L N)) (i₀ : (lbPow P.L N).ι), IsModel w → ⊤ ≤ (eSec P.A) ⁻¹ᵁ (lbPow P.L N).U i₀ → rigVal w i₀ ≠ 0 := by
  first | exact @GlobalTheory.SecJet.rigVal_ne_zero | exact GlobalTheory.SecJet.rigVal_ne_zero | (intros; apply GlobalTheory.SecJet.rigVal_ne_zero <;> assumption)
