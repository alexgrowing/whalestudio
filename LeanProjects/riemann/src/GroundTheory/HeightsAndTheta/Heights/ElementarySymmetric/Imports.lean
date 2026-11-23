import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StFujitaDevissage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def FujitaVanishingPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (I : IFamily F ι) (P : Ideal (MRingOver F ι)),
    IsFieldIntersection I → IsMultiProjPrime P →
    (∀ W : Ideal (MRingOver F ι), P < W →
      ∀ (M : Type) [AddCommGroup M] [Module (MRingOver F ι) M] [Module F M]
        [IsScalarTower F (MRingOver F ι) M] (𝓜 : (K → ℤ) → Submodule F M),
        Module.Finite (MRingOver F ι) M → KH.IsMGraded F ι 𝓜 → W ≤ Module.annihilator (MRingOver F ι) M →
        ∀ e : K → ℤ, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ N : K → ℤ, KH.NefOnF I P N → ∀ i : ℕ, 1 ≤ i →
          Subsingleton (KH.cechHc ι 𝓜 (e + ((fun _ => (m : ℤ)) + N)) i)) →
    (∀ e : K → ℤ, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ N : K → ℤ, KH.NefOnF I P N → ∀ i : ℕ, 2 ≤ i →
      Subsingleton (KH.cechHc ι (KH.quotPart F P) (e + ((fun _ => (m : ℤ)) + N)) i)) →
    ∀ e : K → ℤ, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ N : K → ℤ, KH.NefOnF I P N →
      Subsingleton (KH.cechHc ι (KH.quotPart F P) (e + ((fun _ => (m : ℤ)) + N)) 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
