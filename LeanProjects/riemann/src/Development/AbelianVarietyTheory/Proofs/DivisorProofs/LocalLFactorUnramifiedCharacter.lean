import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarModelUnitaryAction
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
open Formalism.UG (IsUnifV qV)

noncomputable section

namespace GlobalTheory.SplitLval

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open Classical in

theorem aboveF_eq_pair {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl F} (t : E →ₐ[F] Fv F v) :
    aboveF (L := E) F v = {splitPrime t, splitPrime (t.comp σ)} := by
  classical
  ext u
  rw [mem_aboveF, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hu
    haveI := v.isMaximal
    have hm : u.asIdeal ∈ v.asIdeal.primesOver (𝓞 E) := ⟨u.isPrime, ⟨hu ▸ rfl⟩⟩
    rw [primesOver_eq_split h t] at hm
    rcases hm with e | e
    · exact Or.inl (HeightOneSpectrum.ext e)
    · exact Or.inr (HeightOneSpectrum.ext e)
  · rintro (rfl | rfl) <;> exact splitPrime_under _

theorem val_splitPrime_eq_chrW (χ : Chr F E) {v : Pl F} (t : E →ₐ[F] Fv F v) (hu : UnrAt χ (splitPrime t))
    (ϖ : (Fv F v)ˣ) (hϖ : IsUnifV F v ϖ.1) : val χ (splitPrime t) = chrW χ t ϖ := by
  rw [chrW, MonoidHom.comp_apply]
  refine (hu.locChar_eq_val ?_).symm
  show Valued.v (complMap (splitPrime_under t) (ϖ : Fv F v)) = _
  rw [GlobalTheory.LFun.SplitTie.valued_complMap t (splitPrime_under t)]
  exact hϖ

theorem npow_splitPrime {v : Pl F} (t : E →ₐ[F] Fv F v) (z : ℂ) : GlobalTheory.LFun.npow (splitPrime t) z = (qV F v : ℂ) ^ z := by
  rw [GlobalTheory.LFun.npow, ← GlobalTheory.LFun.SplitTie.qV_splitPrime t]; rfl

theorem Lv_charFam_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (χ : Chr F E) (d : ℕ), ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ d →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), (∀ w ∈ aboveF (L := E) F v, UnrAt χ w) → ∀ (ϖ : (Fv F v)ˣ), IsUnifV F v ϖ.1 → ∀ s : ℂ,
      Lv (charFam χ) v s = (1 - (chrW χ t ϖ : ℂ) * (qV F v : ℂ) ^ (-s))⁻¹ * (1 - (chrW χ t ϖ : ℂ)⁻¹ * (qV F v : ℂ) ^ (-s))⁻¹ := by
  intro F E _ _ _ _ _ σ h χ d hχ v t hunr ϖ hϖ s
  classical
  have e := aboveF_eq_pair h t
  have hne : splitPrime t ≠ splitPrime (t.comp σ) := (splitPrime_comp_ne h t).symm
  have h1 : UnrAt χ (splitPrime t) := hunr _ (by rw [e]; simp)
  have h2 : UnrAt χ (splitPrime (t.comp σ)) := hunr _ (by rw [e]; simp)
  have v1 := val_splitPrime_eq_chrW χ t h1 ϖ hϖ
  have v2 := val_splitPrime_eq_chrW χ (t.comp σ) h2 ϖ hϖ
  rw [GlobalTheory.OppLagr.chrW_comp h χ hχ t, MonoidHom.inv_apply] at v2
  rw [Lv, e, Finset.prod_pair hne, locL, locL, charFam_of_unrAt h1, charFam_of_unrAt h2, eulerFac_singleton,
    eulerFac_singleton, v1, v2, npow_splitPrime, npow_splitPrime, Units.val_inv_eq_inv_val]

end GlobalTheory.SplitLval

end
