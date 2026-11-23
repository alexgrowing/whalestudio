import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaNonsplitIsotropicLine
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_nonsplit_isotropic_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d : ℕ) (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (x : Fin d → E), x ≠ 0 → form σ W.J x x = 0 →
    ∀ (v : Pl F), IsEmpty (E →ₐ[F] Fv F v) → ∀ g ∈ UAt σ W (evFin F v),
      ∃ k ∈ KAt σ W v, ∃ t : (AE F E)ˣ, mat (g * k⁻¹) *ᵥ incV F x = t.1 • incV F x := by
  first | exact @GlobalTheory.InertLineTrans.exists_stab_line | exact GlobalTheory.InertLineTrans.exists_stab_line | (intros; apply GlobalTheory.InertLineTrans.exists_stab_line <;> assumption)
