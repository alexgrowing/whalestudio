import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupNonzeroLocusEmbH
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftClosedImmersionOfDense
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.toProj_secPull_secPull (R : Type) [CommRing R] (N : ℕ) (X Y Z : Scheme.{0}) (L : LB X)
    (s : Fin (N + 1) → L.Sec) (h : Y ⟶ X) (g : Z ⟶ Y) (f : Z ⟶ Sp R)
    (hs₁ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (GlobalTheory.secPull (s i) h) g) = ⊤)
    (hs₂ : ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) (g ≫ h)) = ⊤) :
    GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (GlobalTheory.secPull (s i) h) g) hs₁ =
      GlobalTheory.ProjSpace.toProj f (fun i => GlobalTheory.secPull (s i) (g ≫ h)) hs₂ := by
  refine GlobalTheory.ProjSpace.toProj_eq_of_locally hs₂ hs₁ fun z => ?_
  obtain ⟨k, hk⟩ : ∃ k : PUnit → L.ι, z ∈ (L.pull (g ≫ h)).U k :=
    GlobalTheory.ProjSpace.exists_chart_of_iSup_nonzeroLocus hs₂ z
  let l : ((L.pull h).pull g).ι := fun _ _ => k PUnit.unit
  have hle : (L.pull (g ≫ h)).U k ≤ ((L.pull h).pull g).U l := by
    rw [GlobalTheory.Cartier.pull_U L (g ≫ h) k, GlobalTheory.Cartier.pull_U (L.pull h) g l,
      GlobalTheory.Cartier.pull_U L h (fun _ => k PUnit.unit)]
    exact fun _ hy => hy
  refine ⟨_, hk, k, le_rfl, l, hle, 1, fun j => ?_⟩
  rw [_root_.one_mul]
  unfold GlobalTheory.secPull
  rw [GlobalTheory.chartSec_f, GlobalTheory.chartSec_f, GlobalTheory.chartSec_f (GlobalTheory.chartPullPull L (g ≫ h)) (s j) k]
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE_assoc,
    Scheme.Hom.appLE_map]
  rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_map]
  rfl
