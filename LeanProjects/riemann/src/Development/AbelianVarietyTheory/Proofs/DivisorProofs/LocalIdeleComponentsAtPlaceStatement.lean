import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdeleComponentsAtPlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFirstApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptQ
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_idele_components_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ v : Pl F, SplitsFully E v → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v →
  ∃ (t : E →ₐ[F] Fv F v) (e : (w.adicCompletion E)ˣ → (Fv F v)ˣ),
    (∀ x, piW t ((locIdele F w x : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (e x : Fv F v)) ∧
    (∀ x, piW (t.comp σ) ((locIdele F w x : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1) ∧
    (∀ x, At (evFin F v) (((locIdele F w x : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1)) ∧
    (∀ (χ : Chr F E) x, ((chrW χ t (e x) : ℂˣ) : ℂ) = (χ (locIdele F w x) : ℂ)) ∧
    ∀ x (z : ℂ), GlobalTheory.SplitFlip.apow (e x) z = (((absE F E (locIdele F w x) : ℝ≥0) : ℝ) : ℂ) ^ z := by
  first | exact @GlobalTheory.SplitCoord.local_coords | exact GlobalTheory.SplitCoord.local_coords | (intros; apply GlobalTheory.SplitCoord.local_coords <;> assumption)
