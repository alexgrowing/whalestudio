import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RightTranslationSumScalarIsotypic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
open NumberField IsDedekindDomain ReciprocityTheory.Aut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightTranslationSum_scalar_isotypic : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n) (c : ℂ), (∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f) → ∀ f ∈ Formalism.L2.NG.isoTyp a.ρ S, (∀ κ ∈ Umax L n, TrivOutside {v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := by
  first | exact @GlobalTheory.SumTransIso.sumRt_isoTyp | exact GlobalTheory.SumTransIso.sumRt_isoTyp | (intros; apply GlobalTheory.SumTransIso.sumRt_isoTyp <;> assumption)
