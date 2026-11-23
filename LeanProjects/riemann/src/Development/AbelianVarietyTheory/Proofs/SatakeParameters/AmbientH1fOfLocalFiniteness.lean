import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodORingOfIntegers
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataCrystallineAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalH1fFiniteDimensionalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualContinuousIntegralOverEnlargedCoeffStatement

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.Pass

theorem ambient_h1f_of_local_finiteness : Formalism.GaloisCohomology.LocalFinitenessK → ∀ (D : D7) (i : D.nd.Loc)
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i),
    Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) →
    EmbeddingTypes.H1fFiniteRankTorsion (D := D) i ρ π dc := by
  intro hLF D i ρ π dc hc _ w hw _ C L2 _ n
  obtain ⟨⟨_, hdvr, hfr⟩, -⟩ := GlobalTheory.Pass.goodO_ringOfIntegers (D.nd.l i) C.LL
  haveI := hdvr
  haveI := hfr
  have hcont := GlobalTheory.T.twistedDual_continuous_integral_over_enlarged_coeff D i w hw C.LL C.le ρ π hc
  have hfin := GlobalTheory.T.local_h1f_finite_dimensional hLF (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL D.R.r
    (TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π)) hcont.1 hcont.2
  exact GlobalTheory.T.period_data_crystalline_admissible (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) L2 hfin n

end GlobalTheory.Pass
