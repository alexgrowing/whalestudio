import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorCharacterIdentity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_factor_character_identity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ t : (AE F E)ˣ, GlobalTheory.ThK.LemF.fac X.β (((b + 2 : ℕ) : ℝ) / 2) t *
      ((X.ν (Units.map (cA σ : AE F E →* AE F E) t) : ℂ) *
        ((absE F E (Units.map (cA σ : AE F E →* AE F E) t) : ℝ) : ℂ) ^ ((b + 2 - a') / 2))⁻¹ =
      GlobalTheory.ThK.LemF.fac X.α ((a' : ℝ) / 2) t := by
  first | exact @GlobalTheory.ConeLawAChar.fac_div_conj | exact GlobalTheory.ConeLawAChar.fac_div_conj | (intros; apply GlobalTheory.ConeLawAChar.fac_div_conj <;> assumption)
