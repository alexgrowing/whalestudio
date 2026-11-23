import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

noncomputable section

namespace GlobalTheory.Doubling.AbsSplit

theorem norm_eq_zpow {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {a : Fv F v} (ha : a ≠ 0) :
    ‖a‖ = (qV F v : ℝ) ^ (-ordL a) := by
  have h0 : Valued.v a ≠ 0 := (map_ne_zero _).2 ha
  rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ h0, ordL, dif_neg h0, neg_neg]
  simp [qV]

theorem ordL_congr {L L' : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [Field L']
    [Valued L' (WithZero (Multiplicative ℤ))] {x : L} {y : L'} (h : Valued.v x = Valued.v y) : ordL x = ordL y := by
  unfold ordL
  simp only [h]

theorem absEv_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → ∀ x : (Fv F v ⊗[F] E)ˣ, (absEv F E v x : ℝ) = (qV E w : ℝ) ^ (-(ordL (toCompl h x.1) + ordL (toCompl h' x.1))) := by
  intro F E _ _ _ _ _ σ hE v w h w' h' hne x
  obtain ⟨τ, hτ, -⟩ := existsUnique_splitPrime_eq hE hne h h'
  obtain ⟨τ', hτ', -⟩ := existsUnique_splitPrime_eq hE hne.symm h' h
  obtain rfl : τ' = τ.comp σ := (eq_or_eq_comp_conj hE τ τ').resolve_left fun e => hne (hτ.symm.trans (e ▸ hτ'))
  have hN : Algebra.norm (Fv F v) x.1 = splitProj τ x.1 * splitProj (τ.comp σ) x.1 := by
    have := congrArg (splitProj τ) (algebraMap_norm_eq hE x.1)
    rw [AlgHom.commutes, map_mul, ← splitProj_comp] at this
    exact this
  have hq : qV E w = qV F v := hτ ▸ GlobalTheory.LFun.SplitTie.qV_splitPrime τ
  have e1 : ordL (toCompl h x.1) = ordL (splitProj τ x.1) := ordL_congr (by
    rw [GlobalTheory.LFun.ConjPlace.toCompl_eq hE h hτ, GlobalTheory.LFun.ConjPlace.valued_complMap hE h hτ])
  have e2 : ordL (toCompl h' x.1) = ordL (splitProj (τ.comp σ) x.1) := ordL_congr (by
    rw [GlobalTheory.LFun.ConjPlace.toCompl_eq hE h' hτ', GlobalTheory.LFun.ConjPlace.valued_complMap hE h' hτ'])
  have hq0 : (qV F v : ℝ) ≠ 0 := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    unfold qV
    exact_mod_cast (by omega)
  rw [absEv_apply, coe_nnnorm, hN, norm_mul, hq, e1, e2, neg_add, zpow_add₀ hq0,
    norm_eq_zpow v (x.isUnit.map (splitProj τ)).ne_zero, norm_eq_zpow v (x.isUnit.map (splitProj (τ.comp σ))).ne_zero]

end GlobalTheory.Doubling.AbsSplit
