import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitBasisCompl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.HermPlaneComplSig

theorem isHerm_complement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ r s : ℕ),
    B.IsGood σ → Y.IsHerm σ B r s → H.IsAdapted σ B Y Y₁ i₀ i₁ → 1 ≤ s ∧ Y₁.IsHerm σ B (r - 1) (s - 1) := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H i₀ i₁ r s hB hY hH
  have h1 := GlobalTheory.HermPlaneCompl.isHerm_compl hB hY hH
  refine ⟨?_, h1⟩
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have a := (hY.sig w).1
  have b := (h1.sig w).1
  have c := hH.rank
  omega

end GlobalTheory.HermPlaneComplSig
