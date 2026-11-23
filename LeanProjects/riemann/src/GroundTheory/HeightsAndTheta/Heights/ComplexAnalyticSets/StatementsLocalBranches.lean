import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.EqZeroOfMemZeroLocusLineOriginIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology Matrix

noncomputable section

def BranchesToGoodPosition.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u p : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → GroundTheory.Heights₂.Heights.VarBranch J (d + 1) p) (ord : Fin m → ℕ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes →
    p ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W →
    (∃ N ∈ 𝓝 p, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∃ N ∈ 𝓝 p, ∀ b, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ N ⊆ (γ b).slice) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | GroundTheory.Heights₂.Heights.linEval u x = 0}) →
    (∀ b, GroundTheory.Heights₂.Heights.VanishesToOrder
      (fun t => GroundTheory.Heights₂.Heights.linEval u ((γ b).toFun t)) (γ b).radius (ord b)) →
      ∃ (q : Fin n → ℂ) (π : Matrix (Fin d) (Fin n) ℂ) (U : Set (Fin n → ℂ)) (V : Set (Fin d → ℂ))
        (ρ : ℝ), GoodPosition J W u q π U V ρ (∑ b, ord b)

def GoodPositionToBranches.Statement : Prop :=
  ∀ (n e : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u p : Fin n → ℂ)
    (π : Matrix (Fin e) (Fin n) ℂ) (U : Set (Fin n → ℂ)) (V : Set (Fin e → ℂ)) (ρ : ℝ) (N : ℕ),
    IsAffVariety J (e + 1) → linForm u ∉ J → W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes →
    GoodPosition J W u p π U V ρ N →
      ∃ (q : Fin n → ℂ) (m : ℕ) (γ : Fin m → GroundTheory.Heights₂.Heights.VarBranch J (e + 1) q)
        (ord : Fin m → ℕ),
        q ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∧
        (∃ N' ∈ 𝓝 q, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J ∩ N' ⊆ ⋃ b, (γ b).image) ∧
        (∃ N' ∈ 𝓝 q, ∀ b, GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ N' ⊆ (γ b).slice) ∧
        (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | GroundTheory.Heights₂.Heights.linEval u x = 0}) ∧
        (∀ b, GroundTheory.Heights₂.Heights.VanishesToOrder
          (fun t => GroundTheory.Heights₂.Heights.linEval u ((γ b).toFun t)) (γ b).radius (ord b)) ∧
        ∑ b, ord b = N

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
