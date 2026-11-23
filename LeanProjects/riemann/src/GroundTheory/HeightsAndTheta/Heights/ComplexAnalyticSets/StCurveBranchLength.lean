import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets Filter Topology

noncomputable section

def CurveBranchLength.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (u q : Fin n → ℂ) (m : ℕ)
    (c : Fin m → VarBranch I 1 q) (ord : Fin m → ℕ),
    IsRadicalAt I q →
    (∃ N ∈ 𝓝 q, zeroSet I ∩ N ⊆ ⋃ b, (c b).image) →
    (∀ b b', b ≠ b' → (c b).image ∩ (c b').image ⊆ {x | linEval u x = 0}) →
    (∀ b, VanishesToOrder (fun t => linEval u ((c b).toFun t)) (c b).radius (ord b)) →
      localMult (I ⊔ Ideal.span {linForm u}) (RingHom.ker (eval q)) = ∑ b, ord b

end

end GroundTheory.Heights₂.Heights
