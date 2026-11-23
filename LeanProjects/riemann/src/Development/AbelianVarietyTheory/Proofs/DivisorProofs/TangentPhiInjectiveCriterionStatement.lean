import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiInjectiveCriterion
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_Phi_injective_criterion : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (z z' : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O M ≫ z' = η[A]), (∀ w, Phi z h w = Phi z' h' w) → z = z') → (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (n : ℕ) (φ : G.A n →ₐ[O] TrivSqZeroExt O M) (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) (w : Wmod A), Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w = GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩ (cn t n w)) → ∀ n : ℕ, Function.Surjective (cn t n) := by
  first | exact @GlobalTheory.SqZeroPt.CnSurj.cn_surjective | exact GlobalTheory.SqZeroPt.CnSurj.cn_surjective | (intros; apply GlobalTheory.SqZeroPt.CnSurj.cn_surjective <;> assumption)
