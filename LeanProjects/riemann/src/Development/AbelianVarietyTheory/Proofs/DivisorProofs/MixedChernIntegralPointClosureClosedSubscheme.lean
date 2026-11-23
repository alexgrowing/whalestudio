import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedClosureOfPointProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableAgainstMixedChernFormIffPullIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleIsometryCalculusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureEqOfIsometricProjStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem cycInt_of_closedImmersion : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k)
    (σ : k →+* ℂ), IsProjOver p → ∀ [IsIntegral Y] (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (D : ℕ)
    (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ),
    (CycIntg L f (π (genericPoint Y)) ↔ Intg (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y))) ∧
      cycInt L f (π (genericPoint Y)) = Mix.int (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) := by
  intro k _ X Y p q σ hp _ π _ hπ D L f
  generalize hz : π (genericPoint Y) = z
  obtain ⟨_, -, -, hY⟩ := GlobalTheory.ClosFacts.clos_facts X z
  obtain ⟨g, hgπ, -, -, hiso⟩ := hY Y π hz
  have : IsIso g := hiso inferInstance
  subst hgπ
  have hpz : IsProjOver (closι z ≫ p) := ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp
  have hq : IsProjOver q := hπ ▸ ProjSpace.isProjOver_comp_of_isClosedImmersion (g ≫ closι z) hp
  have hg : g ≫ (closι z ≫ p) = q := by rw [← Category.assoc]; exact hπ
  obtain ⟨hI, hE⟩ := GlobalTheory.T.integrableAgainstMixedChernForm_iff_pull_iso k (clos z) Y (closι z ≫ p) q σ hpz g hg D (fun i => (L i).pull (closι z) rfl)
    (fun y => f (ptMap (closι z) rfl σ y))
  have hiso' : ∀ i, (((L i).pull (closι z) rfl).pull g hg).Isom ((L i).pull (g ≫ closι z) hπ) := fun i =>
    (GlobalTheory.T.smoothWeightedLineBundle_isometry_calculus k X (clos z) p (closι z ≫ p) σ (closι z) rfl).2.2.2.2.2 Y q g hg hπ (L i)
  have hpart : ∀ ε, part (fun i => ((L i).pull (closι z) rfl).pull g hg) ε = part (fun i => (L i).pull (g ≫ closι z) hπ) ε :=
    GlobalTheory.T.mixedChernFormSignedPartMeasure_eq_of_isometric_projOver k Y q σ hq D _ _ hiso'
  have hfun : (fun y => f (ptMap (closι z) rfl σ (ptMap g hg σ y))) = fun y => f (ptMap (g ≫ closι z) hπ σ y) := by
    funext y; exact congrArg f (PtsOver.map_map _ _ _ _ _ y)
  have hI' : Intg (fun i => ((L i).pull (closι z) rfl).pull g hg) (fun y => f (ptMap (closι z) rfl σ (ptMap g hg σ y))) ↔
      Intg (fun i => (L i).pull (g ≫ closι z) hπ) (fun y => f (ptMap (g ≫ closι z) hπ σ y)) := by
    rw [hfun]; simp only [Intg, hpart]
  have hE' : Mix.int (fun i => ((L i).pull (closι z) rfl).pull g hg) (fun y => f (ptMap (closι z) rfl σ (ptMap g hg σ y))) =
      Mix.int (fun i => (L i).pull (g ≫ closι z) hπ) (fun y => f (ptMap (g ≫ closι z) hπ σ y)) := by
    rw [hfun]; simp only [Mix.int, hpart]
  exact ⟨hI.symm.trans hI', hE.symm.trans hE'⟩

end GlobalTheory.Mix
