import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicLeviUnipotentSplit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_levi_unipotent_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {n d₁ : ℕ} (W : Spc F E n) (W₁ : Spc F E d₁) (H' : Plane E n d₁) (r s i₀ i₁ : ℕ), IsCMExt F E σ →
    W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ (p : UA σ W.J) (t : (AE F E)ˣ), mat p *ᵥ incV F H'.x = t.1 • incV F H'.x →
    ∃ n ∈ unip σ W H', ∃ m₁ : UA σ W.J, IsLevi (W₁ := W₁) H' t 1 m₁ ∧ ∃ (h₁ : UA σ W₁.J) (m₂ : UA σ W.J),
      IsLevi (W₁ := W₁) H' 1 h₁ m₂ ∧ p = n * m₁ * m₂ := by
  first | exact @GlobalTheory.StabLineLevi.stab_line_eq_unip_mul_levi | exact GlobalTheory.StabLineLevi.stab_line_eq_unip_mul_levi | (intros; apply GlobalTheory.StabLineLevi.stab_line_eq_unip_mul_levi <;> assumption)
