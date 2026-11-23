import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinSeriesMeasurable
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_series_measurable : GlobalTheory.ThK.KP → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {n : ℕ} (X : Spc F E n) (r s' : ℕ), B.IsGood σ → X.IsHerm σ B r s' →
    ∀ K : Subgroup (UA σ X.J), IsStab B K → ∀ (x : Fin n → E) (Eis : ℂ → UA σ X.J → ℂ), GlobalTheory.ConeSmall.IsEisSer K x Eis →
    ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → Measurable (Eis s) := by
  first | exact @GlobalTheory.ConeSmallMeas.eis_measurable | exact GlobalTheory.ConeSmallMeas.eis_measurable | (intros; apply GlobalTheory.ConeSmallMeas.eis_measurable <;> assumption)
