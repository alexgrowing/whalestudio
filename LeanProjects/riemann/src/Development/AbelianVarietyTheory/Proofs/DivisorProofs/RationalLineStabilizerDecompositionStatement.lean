import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLineStabilizerDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_line_stabilizer_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) {n d₁ : ℕ} (W : Spc F E n) (W₁ : Spc F E d₁) (H' : Plane E n d₁) (r s i₀ i₁ : ℕ), IsCMExt F E σ →
    W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ p ∈ ratU σ W.J, ∀ t : (AE F E)ˣ, mat p *ᵥ incV F H'.x = t.1 • incV F H'.x →
    ∃ u ∈ unip σ W H', ∃ h₁ ∈ ratU σ W₁.J, ∃ m : UA σ W.J, IsLevi (W₁ := W₁) H' t h₁ m ∧ p = u * m := by
  first | exact @GlobalTheory.RatStabLevi.rat_levi_dec | exact GlobalTheory.RatStabLevi.rat_levi_dec | (intros; apply GlobalTheory.RatStabLevi.rat_levi_dec <;> assumption)
