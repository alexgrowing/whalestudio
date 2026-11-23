import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterUnramifiedExponent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_character_unramified_exponent : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ (χ : Chr F E), IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ 0 →
    ∀ (k : InfinitePlace F → ℤ) (d : ℕ), HasExp B.emb χ k → (∀ w, (d : ℤ) < |k w|) → ∀ T : Finset (Pl F), UnrOff χ (T : Set (Pl F)) →
    (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ T → ¬ UnrAt χ w) → ∀ z : ℤ, -(d : ℤ) ≤ 2 * z →
      ∃ c : ℂ, c ≠ 0 ∧ GlobalTheory.Cont.HolValueAt (charL χ (T : Set (Pl F))) (z : ℂ) c := by
  first | exact @GlobalTheory.BotLValue.charL_holValueAt_ne_zero | exact GlobalTheory.BotLValue.charL_holValueAt_ne_zero | (intros; apply GlobalTheory.BotLValue.charL_holValueAt_ne_zero <;> assumption)
