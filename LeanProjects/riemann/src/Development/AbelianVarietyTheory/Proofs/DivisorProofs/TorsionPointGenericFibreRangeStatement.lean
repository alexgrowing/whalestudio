import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointGenericFibreRange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompReixMemAdm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.DblBox
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_pair_compatible_embedding : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ →
    ∀ X₂ : Spc F E (n + n), X₂.J = dblGram finSumFinEquiv X.J →
    ∀ i : UA σ X.J × UA σ X.J →* UA σ X₂.J, (∀ g g', mat (i (g, g')) = blkMat finSumFinEquiv (mat g) (mat g')) →
    ∀ (Mb : Model σ X₂ W) (χ χ' : Chr F E) (omb : Rep σ X₂ W) (r₂ s₂ : ℕ), IsPair B Mb χ χ' omb r₂ s₂ r₁ s₁ → IsBoxCo M.co Mb.co →
    ∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), ∀ (g₁ g₂ : UA σ X.J) (h : UA σ W.J), ∃ a : ℂ,
      omb (i (g₁, g₂), h) (bx φ₁ (cj φ₂)) = a • bx (om (g₁, h) φ₁) (cj (om (g₂, h) φ₂)) := by
  first | exact @GlobalTheory.DblBoxCoef.weil_bx_prop | exact GlobalTheory.DblBoxCoef.weil_bx_prop | (intros; apply GlobalTheory.DblBoxCoef.weil_bx_prop <;> assumption)
