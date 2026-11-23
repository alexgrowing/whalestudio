import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets Filter Topology

noncomputable section

def SliceBranches.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u p : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → VarBranch J (d + 1) p) (ord : Fin m → ℕ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes → p ∈ zeroSet W →
    (∃ N ∈ 𝓝 p, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∃ N ∈ 𝓝 p, ∀ b, zeroSet W ∩ N ⊆ (γ b).slice) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) →
    (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) →
    ∀ (U : Set (Fin n → ℂ)) (Λ : (Fin n → ℂ) → Set (Matrix (Fin d) (Fin n) ℂ)),
      IsOpen U → zeroSet W ⊆ closure (zeroSet W ∩ U) → (∀ q ∈ zeroSet W ∩ U, Dense (Λ q)) →
        ∃ q ∈ zeroSet W ∩ U, ∃ L ∈ Λ q, ∃ c : Fin m → VarBranch (sliceIdeal J L q) 1 q,
          (∃ N ∈ 𝓝 q, zeroSet (sliceIdeal J L q) ∩ N ⊆ ⋃ b, (c b).image) ∧
          (∀ b b', b ≠ b' → (c b).image ∩ (c b').image ⊆ {x | linEval u x = 0}) ∧
          ∀ b, VanishesToOrder (fun t => linEval u ((c b).toFun t)) (c b).radius (ord b)

end

end GroundTheory.Heights₂.Heights
