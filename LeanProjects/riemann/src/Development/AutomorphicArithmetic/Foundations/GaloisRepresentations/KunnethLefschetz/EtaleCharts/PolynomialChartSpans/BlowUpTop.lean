import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.ProjProd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.CrossOfRel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowUpOff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowUpSmooth
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.ExSmooth
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.DifferentialFormSections
open FunctorialResolution.Blowup

theorem UpperTheory.Gal.KunnethLefschetz.G.blTop :
    UpperTheory.Gal.KunnethLefschetz.G.BlowUpTop := by
  intro R _ _ Z d _ hZ
  have hprop := (UpperTheory.Gal.KunnethLefschetz.G.projProd R (Over.hom Z) (Over.hom Z) hZ).2.2
  haveI : IsSeparated (Over.hom Z) := inferInstance
  haveI : LocallyOfFiniteType (Over.hom Z) := inferInstance
  have hXX : IsProjOver (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z)) :=
    (UpperTheory.Gal.KunnethLefschetz.G.projProd R (Over.hom Z) (Over.hom Z) hZ).1 hZ
  obtain ⟨Y, πl, hπ⟩ := exists_isBlowupAlongIdealSheaf (UpperTheory.Gal.KunnethLefschetz.G.XX Z).left
    (Scheme.Hom.ker (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z)))
  let W : Sch R := Over.mk (πl ≫ Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z))
  let π : W ⟶ UpperTheory.Gal.KunnethLefschetz.G.XX Z := Over.homMk πl rfl
  have hBl : UpperTheory.Gal.KunnethLefschetz.G.IsBl π := hπ
  have hW : IsProjOver (Over.hom W) := by
    obtain ⟨M, f, h, hci⟩ :=
      UpperTheory.Gal.KunnethLefschetz.G.blEmb R (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z)) hXX _ πl hπ
    have hstr : IsProjOver (PSpace.str R M) := ⟨M, 𝟙 _, inferInstance, by simp⟩
    have hP := (UpperTheory.Gal.KunnethLefschetz.G.projProd R (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z))
      (PSpace.str R M) hXX).1 hstr
    have h2 := (UpperTheory.Gal.KunnethLefschetz.G.projProd R _ (πl ≫ Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z)) hP).2.1 _ hci
    rw [pullback.lift_fst_assoc] at h2
    exact h2
  have hoff := UpperTheory.Gal.KunnethLefschetz.G.blOff R π hBl
  have hEx : IsProjOver (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.Ex π)) := by
    have h2 := (UpperTheory.Gal.KunnethLefschetz.G.projProd R (Over.hom W) (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.Ex π)) hW).2.1
      _ hoff.2.1
    rwa [Over.w] at h2
  have hsm := UpperTheory.Gal.KunnethLefschetz.G.blSmooth R (d + 1) π hBl
  have hex := UpperTheory.Gal.KunnethLefschetz.G.exSmooth R d π hBl
  refine ⟨W, π, hBl, hXX, hW, hEx, ?_, hsm.2, ?_⟩
  · haveI : SmoothOfRelativeDimension (d + 1) (pullback.fst (Over.hom Z) (Over.hom Z)) :=
      MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension (d + 1))
        (self := smoothOfRelativeDimension_isStableUnderBaseChange (d + 1))
        (IsPullback.of_hasPullback (Over.hom Z) (Over.hom Z)).flip inferInstance
    show SmoothOfRelativeDimension (d + 1 + (d + 1))
      (pullback.fst (Over.hom Z) (Over.hom Z) ≫ Over.hom Z)
    infer_instance
  · haveI := hex.1
    rw [← Over.w (UpperTheory.Gal.KunnethLefschetz.G.exG π)]
    infer_instance
