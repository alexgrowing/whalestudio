import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHom
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem kTriv_of_cover : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → ∀ (L : LB A.left) (M : ∀ i, LB (G i).left), L.IsLB → (∀ i, (M i).IsLB) → (∀ i, LBIso (M i) (L.pull (ψ i))) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → (∀ i, Out.KTriv (G i) (M i)) → Out.KTriv A L := by
  intro S I U A _ G _ ψ hU hG L M hL hM hLM hA hGA hK
  rw [GlobalTheory.UU.kTriv_iff_forall]
  intro T x hx
  apply over_ext hU
  intro i T' r
  obtain ⟨y, hy⟩ := exists_lift (hG i).1 (r ≫ x)
  have hpush : pushPt (hG i).1.w y = r ≫ x := by
    ext1
    exact hy.symm
  have hyK : GlobalTheory.UU.InK (G i) (M i) y :=
    GlobalTheory.UU.inK_of_push (hG i) hL (hM i) (hLM i) y (hpush ▸ hx.comp r)
  have hy1 : y = 1 := (GlobalTheory.UU.kTriv_iff_forall.1 (hK i)) T' y hyK
  have hsq : (r ≫ x) * (r ≫ x) = r ≫ x := by
    ext1
    rw [((hG i).2 T' y y (r ≫ x) (r ≫ x) hy hy), hy, hy1, _root_.mul_one]
  have h1 : r ≫ x = 1 := by simpa using hsq
  rw [h1]
  simp

end GlobalTheory.CoverGlue
