import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GeneratedModOfSubsingleton
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def FujitaVanishing.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (I : IFamily F ι) (V : Ideal (MRingOver F ι)) (H : K → ℤ)
    (M : Type) [AddCommGroup M] [Module (MRingOver F ι) M] [Module F M] [IsScalarTower F (MRingOver F ι) M]
    (𝓜 : (K → ℤ) → Submodule F M),
    IsFieldIntersection I → IsMultiHomogIdeal V → H1GenAmple F V H →
    Module.Finite (MRingOver F ι) M → KH.IsMGraded F ι 𝓜 → V ≤ Module.annihilator (MRingOver F ι) M →
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ N : K → ℤ, KH.NefOnF I V N →
      ∀ i : ℕ, 1 ≤ i → Subsingleton (KH.cechHc ι 𝓜 (m • H + N) i)

theorem le_annihilator_quotient {R : Type} [CommRing R] (V : Ideal R) :
    V ≤ Module.annihilator R (R ⧸ V) := by
  intro x hx
  rw [Module.mem_annihilator]
  intro z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact V.mul_mem_right r hx

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
