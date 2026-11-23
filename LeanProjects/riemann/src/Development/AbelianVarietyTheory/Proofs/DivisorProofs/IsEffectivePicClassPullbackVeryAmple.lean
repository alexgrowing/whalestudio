import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffOfSec
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.EffBound

open GlobalTheory.CechPic

theorem eff_pull_of_veryAmpleBy : ∀ (R : Type) [CommRing R] {X Y : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (hH : H.IsLB), GlobalTheory.AbLaw.VeryAmpleBy f H s → ∀ (φ : Y ⟶ X), Nonempty Y → GlobalTheory.EffBound.Eff (GlobalTheory.CechPic.pull φ (GlobalTheory.CechPic.cls H hH)) := by
  intro R _ X Y f H m s hH hva φ hY
  obtain ⟨y⟩ := hY
  have hy : φ y ∈ ⨆ i, nonzeroLocus (s i) := by rw [hva.1]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  have hy' : y ∈ nonzeroLocus (GlobalTheory.secPull (s i) φ) := by
    rw [GlobalTheory.nonzeroLocus_secPull]; exact hi
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy'
  have hne : (GlobalTheory.secPull (s i) φ).f k ≠ 0 := by
    intro h0
    rw [h0, Scheme.basicOpen_zero] at hk
    exact hk
  rw [← cls_pull hH φ (pull_isLB hH φ)]
  exact eff_of_sec _ _ _ k hne

end GlobalTheory.EffBound
