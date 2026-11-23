import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt

theorem cotMap_res_cn : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), (∀ (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w)) → ∀ (n : ℕ) (w : Wmod A), GlobalTheory.PDiv.cotMap (G.res n) (cn t (n + 1) w) = cn t n w := by
  intro p O _ G A _ t hnat n w
  have key : (TrivSqZeroExt.map (GlobalTheory.PDiv.cotMap (G.res n))).comp (univ G (n + 1)) =
      (univ G n).comp (G.res n : G.A (n + 1) →ₐ[O] G.A n) := by
    ext a
    · simp [univ]
    · simp [univ]
  have hz : GlobalTheory.GrpTangent.sqZeroMap (GlobalTheory.PDiv.cotMap (G.res n)) ≫
      (spOver (univ G (n + 1)) ≫ t.y (n + 1)) = spOver (univ G n) ≫ t.y n := by
    have e1 : GlobalTheory.GrpTangent.sqZeroMap (GlobalTheory.PDiv.cotMap (G.res n)) =
        spOver (TrivSqZeroExt.map (GlobalTheory.PDiv.cotMap (G.res n))) := rfl
    rw [← Category.assoc, e1, spOver_comp, key, ← spOver_comp, Category.assoc, t.res n]
  have h0 := zeroSec_spOver_y t (n + 1) _ (fst_comp_univ (G := G) (n + 1))
  have h1 : zeroSec O _ ≫ (GlobalTheory.GrpTangent.sqZeroMap (GlobalTheory.PDiv.cotMap (G.res n)) ≫
      (spOver (univ G (n + 1)) ≫ t.y (n + 1))) = η[A] := by
    rw [hz]; exact zeroSec_spOver_y t n _ (fst_comp_univ (G := G) n)
  have := hnat _ _ (GlobalTheory.PDiv.cotMap (G.res n)) _ h0 h1 w
  unfold cn
  rw [← this]
  have hP : ∀ {z z' : TM O (GlobalTheory.PDiv.Cot O (G.A n)) ⟶ A} (e : z = z') h h', Phi z h = Phi z' h' := by
    rintro _ _ rfl _ _; rfl
  exact congrArg (fun f => f w) (hP hz _ _)

end GlobalTheory.SqZeroPt
