import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanUnitHeightBound
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_unit_height_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∃ C : ℝ, ∀ (p : UA σ X.J × UA σ W.J) (u : Matrix (Fin n) (Fin d) (AE F E)), IsArchUnit (M.co.e u) → ∃ c : ℝ, 0 ≤ c ∧ c ≤ C * ((ht p.1 : ℝ) * ht p.2) ∧ ∃ w, IsArchUnit w ∧ M.co.e (actAB (cA σ) p u) = realAd F c • w := by
  first | exact @GlobalTheory.ThetaDecay.archUnit_act_bound | exact GlobalTheory.ThetaDecay.archUnit_act_bound | (intros; apply GlobalTheory.ThetaDecay.archUnit_act_bound <;> assumption)
