import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFujitaVanishing
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAmpleOfGenTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def FujitaOne.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (I : IFamily F ι) (V : Ideal (MRingOver F ι))
    (M : Type) [AddCommGroup M] [Module (MRingOver F ι) M] [Module F M] [IsScalarTower F (MRingOver F ι) M]
    (𝓜 : (K → ℤ) → Submodule F M),
    IsFieldIntersection I → IsMultiHomogIdeal V →
    Module.Finite (MRingOver F ι) M → KH.IsMGraded F ι 𝓜 → V ≤ Module.annihilator (MRingOver F ι) M →
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ N : K → ℤ, KH.NefOnF I V N →
      ∀ i : ℕ, 1 ≤ i → Subsingleton (KH.cechHc ι 𝓜 ((fun _ => (m : ℤ)) + N) i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
