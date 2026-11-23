import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver

open AlgebraicGeometry CategoryTheory
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace ModelDimension

theorem subring_spec_morphism_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Ω : Type) [Field Ω] (A : Subring Ω) (g₁ g₂ : Spec (CommRingCat.of A) ⟶ Y.X), Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ g₁ = Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ g₂ → g₁ = g₂ := by
  intro E _ _ _ H Dw l Xo c O _ β Y Ω _ A g₁ g₂ h
  have hpr : IsProper Y.s := GlobalTheory.SchemeWords.isProper_of_isProjOver Y.proj
  have hsep : Y.X.IsSeparated := by
    constructor
    rw [← Limits.terminal.comp_from Y.s]
    infer_instance
  have hdom : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A Ω))) := by
    constructor
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap A Ω)).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (Subtype.val_injective)]
      exact bot_le)
  exact ext_of_isDominant _ h

end ModelDimension
