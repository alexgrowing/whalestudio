import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd

open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.ThK.CuspTransfer

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def emb (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} (W : Spc F E n) (W₁ : Spc F E n₁) {c : E} (hc : c ≠ 0)
    (M : UA σ W₁.J → UA σ W.J) (y : GAd σ (c • W₁.J.map σ)) : GAd σ (c • W.J.map σ) :=
  GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc (M ((GlobalTheory.ThK.SquareIntegrability.toGAd hσ W₁.J hc).symm y))

def IsInd (hσ : ∀ x, σ (σ x) = x) {n n₁ r : ℕ} (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) {c : E} (hc : c ≠ 0)
    (X : Matrix (Fin n) (Fin (r + 1)) E) (M : UA σ W₁.J → UA σ W.J) (χ : Chr F E) (Kc : Set (GAd σ (c • W.J.map σ)))
    {d : ℕ} (ψs : Fin d → GAd σ (c • W₁.J.map σ) → ℂ) (a : Fin d → GAd σ (c • W.J.map σ) → ℂ)
    (Ψ : GAd σ (c • W.J.map σ) → ℂ) : Prop :=
  (∀ g, ∃ u ∈ GlobalTheory.StdPar.unip σ (c • W.J.map σ) X {0}, ∃ t m y, ∃ k ∈ Kc, IsLevi (W₁ := W₁) H t 1 m ∧
    g = u * GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc m * emb hσ W W₁ hc M y * k) ∧
  ∀ u ∈ GlobalTheory.StdPar.unip σ (c • W.J.map σ) X {0}, ∀ t m y, ∀ k ∈ Kc, IsLevi (W₁ := W₁) H t 1 m →
    Ψ (u * GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc m * emb hσ W W₁ hc M y * k) = (χ t : ℂ) * ∑ i, ψs i y * a i k

end GlobalTheory.ThK.CuspTransfer

end
