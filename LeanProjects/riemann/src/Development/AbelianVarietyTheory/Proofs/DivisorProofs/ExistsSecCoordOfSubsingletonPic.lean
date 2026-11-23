import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsE8ThetaStructure
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM
open scoped CategoryTheory.Obj
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier

noncomputable section
namespace GlobalTheory.ZM.FieldPoint

theorem exists_secCoord_of_subsingleton_pic {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {I : Type} (σ : I → M.Sec)
    {A : Type} [CommRing A] [Subsingleton (CommRing.Pic A)] (x : Sp A ⟶ X) : ∃ v : I → A, SecCoord M σ x v := by
  have hL := LB.isLB_pull hM x
  obtain ⟨t, ht⟩ := GlobalTheory.LB.exists_isGen_of_subsingleton_pic hL
  let a := ReciprocityTheory.ChartRestriction.G.DVR.genSec t ht
  have ha : ⊤ ≤ nonzeroLocus a := (nonzeroLocus_genSec hL t ht).ge
  choose v hv using fun j => fnOn_top_bijective.2 (resG _ ha (secRatio a (secPull (σ j) x)))
  refine ⟨v, t, ht, fun i j h => ?_⟩
  have h1 := secRatio_on a (secPull (σ i) x) j (le_top.trans ha) le_rfl
  rw [resG_self, resG_self] at h1
  change _ = fnOn _ (v i) * a.f j
  rw [← resG_fnOn (le_top : _ ≤ ⊤), hv, resG_resG]
  exact h1

theorem exists_secCoord : ∀ (o : Type) [CommRing o] (m : ℕ) (K : Type) [Field K] (y : Sp K ⟶ PSpace o m),
    ∃ v : Fin (m + 1) → K, SecCoord (GlobalTheory.ProjSpace.O1 o m) (GlobalTheory.ProjSpace.coord o m) y v :=
  fun o _ m _ _ y => exists_secCoord_of_subsingleton_pic (O1_isLB o m) _ y

end GlobalTheory.ZM.FieldPoint
