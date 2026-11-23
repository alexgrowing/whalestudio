import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSeriesSatakeParameters
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
open NumberField IsDedekindDomain
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_series_satake_parameters : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (μ₁ μ₂ : (w.adicCompletion E)ˣ →* ℂˣ), GlobalTheory.SplitWeil.IsUnram μ₁ → GlobalTheory.SplitWeil.IsUnram μ₂ →
    GlobalTheory.LFun.HasSatGL w (GlobalTheory.SmGL.prod₂ (GlobalTheory.SmGL.detRep (Fin 1) μ₁) (GlobalTheory.SmGL.detRep (Fin 1) μ₂))
      {μ₁ (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w)), μ₂ (Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w))} := by
  first | exact @GlobalTheory.PrinSat.hasSatGL_prod₂_detRep | exact GlobalTheory.PrinSat.hasSatGL_prod₂_detRep | (intros; apply GlobalTheory.PrinSat.hasSatGL_prod₂_detRep <;> assumption)
