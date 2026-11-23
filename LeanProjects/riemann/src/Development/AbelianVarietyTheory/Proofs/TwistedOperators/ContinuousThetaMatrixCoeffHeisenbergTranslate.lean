import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientSummable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.MatCoefCont

theorem continuous_thPair_heisO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f₀ : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → Continuous (fun w : WO S T => thPair μ 𝓕 f (heisO ψ S T w f₀)) := by
  intro D ψ hψ S T μ 𝓕 h𝓕 f f₀ hf hf₀
  haveI hAE : SecondCountableTopology (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.2.1
  haveI hM : SecondCountableTopology (WO S T) :=
    inferInstanceAs (SecondCountableTopology (Fin T.rank → Fin S.rank → AE D))
  haveI : FirstCountableTopology (WO S T) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨C, hC⟩ := (GlobalTheory.ThetaSquare.squareIntegrable hψ f hf).2.1
  obtain ⟨C₀, hC₀⟩ := (GlobalTheory.ThetaSquare.squareIntegrable hψ f₀ hf₀).2.1
  haveI : IsFiniteMeasure (μ.restrict 𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, h𝓕.2.2]; exact ENNReal.one_lt_top⟩
  have hsc := (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.2.1
  have hF : Continuous (fun p : WO S T × WO S T =>
      f p.2 * star (ψ (symplOH S T p.2 p.1) * f₀ (p.2 + p.1))) :=
    (hf.cont.comp continuous_snd).mul
      (((hψ.1.1.comp (hsc.comp (continuous_snd.prodMk continuous_fst))).mul
        (hf₀.cont.comp (continuous_snd.add continuous_fst))).star)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  unfold thPair heisO
  refine continuous_of_dominated (bound := fun _ => C * C₀) (fun w => ?_) (fun w => ?_) (integrable_const _) ?_
  · exact (hF.comp (Continuous.prodMk_right w)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    rw [norm_mul, norm_star, norm_mul, hψ.1.2.1, one_mul]
    exact mul_le_mul (hC z) (hC₀ _) (norm_nonneg _) hC0
  · exact Filter.Eventually.of_forall fun z => hF.comp (continuous_id.prodMk continuous_const)

end GlobalTheory.MatCoefCont
