import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarSkewScalingIdele
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabAtPair
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_skew_scaling_idele : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ e, σ (σ e) = e) (v : Pl F) (t : (AE F E)ˣ), t ∈ idelesAt E (evFin F v) →
    ∀ ν : Measure (skewAt σ (evFin F v)), ν.IsAddHaarMeasure →
      ν.map (normSmul hσ (t⁻¹ : (AE F E)ˣ).1) = absE F E t • ν := by
  first | exact @GlobalTheory.ThK.LemF.QuotInv.map_normSmul_inv | exact GlobalTheory.ThK.LemF.QuotInv.map_normSmul_inv | (intros; apply GlobalTheory.ThK.LemF.QuotInv.map_normSmul_inv <;> assumption)
