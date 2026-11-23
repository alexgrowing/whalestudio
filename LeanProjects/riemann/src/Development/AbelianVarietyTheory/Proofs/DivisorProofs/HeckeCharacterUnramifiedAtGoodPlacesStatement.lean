import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterUnramifiedAtGoodPlaces
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_character_unramified_at_good_places : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ χ : (AE F E)ˣ →* ℂˣ, Continuous (fun t => ((χ t : ℂˣ) : ℂ)) → (∀ x : Eˣ, χ (Units.map (inclR (F := F) (AF F)).toMonoidHom x) = 1) → (∀ v, X.Good v → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → (∀ x, χ (locIdele F w x) = GlobalTheory.CtTyp.twAbs X.α ((a' : ℝ) / 2) (locIdele F w x)) ∨ ∀ x, χ (locIdele F w x) = GlobalTheory.CtTyp.twAbs X.β ((a : ℝ) / 2) (locIdele F w x)) → χ = GlobalTheory.CtTyp.twAbs X.α ((a' : ℝ) / 2) ∨ χ = GlobalTheory.CtTyp.twAbs X.β ((a : ℝ) / 2) := by
  first | exact @GlobalTheory.CtTypGlob.eq_or_eq | exact GlobalTheory.CtTypGlob.eq_or_eq | (intros; apply GlobalTheory.CtTypGlob.eq_or_eq <;> assumption)
