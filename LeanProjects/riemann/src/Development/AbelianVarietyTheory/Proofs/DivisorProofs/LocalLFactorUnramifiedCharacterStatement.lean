import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLFactorUnramifiedCharacter
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
open Formalism.UG (IsUnifV qV)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_l_factor_unramified_character : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (χ : Chr F E) (d : ℕ), ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ d →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), (∀ w ∈ aboveF (L := E) F v, UnrAt χ w) → ∀ (ϖ : (Fv F v)ˣ), IsUnifV F v ϖ.1 → ∀ s : ℂ,
      Lv (charFam χ) v s = (1 - (chrW χ t ϖ : ℂ) * (qV F v : ℂ) ^ (-s))⁻¹ * (1 - (chrW χ t ϖ : ℂ)⁻¹ * (qV F v : ℂ) ^ (-s))⁻¹ := by
  first | exact @GlobalTheory.SplitLval.Lv_charFam_split | exact GlobalTheory.SplitLval.Lv_charFam_split | (intros; apply GlobalTheory.SplitLval.Lv_charFam_split <;> assumption)
