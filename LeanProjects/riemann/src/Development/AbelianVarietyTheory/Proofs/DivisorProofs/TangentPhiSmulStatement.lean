import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSmul
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_Phi_smul : ∀ (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (A : Over (Sp O)) [GrpObj A] (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (c : O) (w : Wmod A), Phi z h (c • w) = c • Phi z h w := by
  first | exact @GlobalTheory.SqZeroPt.Phi_smul | exact GlobalTheory.SqZeroPt.Phi_smul | (intros; apply GlobalTheory.SqZeroPt.Phi_smul <;> assumption)
