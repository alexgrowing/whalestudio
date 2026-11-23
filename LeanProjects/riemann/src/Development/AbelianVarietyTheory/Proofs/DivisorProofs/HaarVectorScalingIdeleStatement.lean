import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarVectorScalingIdele
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabAtPair
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_vector_scaling_idele : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (m : ℕ) (v : Pl F)
    (t : (AE F E)ˣ), t ∈ idelesAt E (evFin F v) → ∀ ν : Measure (vecAt F E m (evFin F v)), ν.IsAddHaarMeasure →
      ν.map (vecAtSmul (cA σ (t⁻¹ : (AE F E)ˣ).1)) = (absE F E t ^ m) • ν := by
  first | exact @GlobalTheory.ThK.LemF.QuotInv.map_vecAtSmul_cA_inv | exact GlobalTheory.ThK.LemF.QuotInv.map_vecAtSmul_cA_inv | (intros; apply GlobalTheory.ThK.LemF.QuotInv.map_vecAtSmul_cA_inv <;> assumption)
