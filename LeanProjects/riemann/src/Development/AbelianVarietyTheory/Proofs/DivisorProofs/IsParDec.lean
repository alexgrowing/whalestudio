import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInd

open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.ThK.InducedCons

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def IsParDec (hσ : ∀ x, σ (σ x) = x) {n n₁ r : ℕ} (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) {c : E} (hc : c ≠ 0)
    (X : Matrix (Fin n) (Fin (r + 1)) E) (M : UA σ W₁.J → UA σ W.J) (t : (AE F E)ˣ) (y : GAd σ (c • W₁.J.map σ))
    (g : GAd σ (c • W.J.map σ)) : Prop :=
  ∃ u ∈ GlobalTheory.StdPar.unip σ (c • W.J.map σ) X {0}, ∃ m, IsLevi (W₁ := W₁) H t 1 m ∧
    g = u * GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc m * GlobalTheory.ThK.CuspTransfer.emb hσ W W₁ hc M y

end GlobalTheory.ThK.InducedCons

end
