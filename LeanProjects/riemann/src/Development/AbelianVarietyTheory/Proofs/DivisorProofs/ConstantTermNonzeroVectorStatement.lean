import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermNonzeroVector
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_nonzero_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (n d₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E d₁) (H' : Plane E n d₁) (i₀ i₁ r s : ℕ),
    W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ (c : E) (hc : c ≠ 0) (f : UA σ W.J → ℂ), IsCT H' f 0 →
      (Matrix.of fun i (_ : Fin 1) => H'.x i) ≠ 0 ∧
      Formalism.UG.cT (σ : E →+* E) (Matrix.of fun i (_ : Fin 1) => H'.x i) * (c • W.J.map σ) * (Matrix.of fun i (_ : Fin 1) => H'.x i) = 0 ∧
      IsConstTerm σ (c • W.J.map σ) (Matrix.of fun i (_ : Fin 1) => H'.x i) (fun x => f ((toGAd hσ W.J hc).symm x)) 0 := by
  first | exact @GlobalTheory.LineCT.isConstTerm_line | exact GlobalTheory.LineCT.isConstTerm_line | (intros; apply GlobalTheory.LineCT.isConstTerm_line <;> assumption)
