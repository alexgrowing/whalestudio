import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeSubIffSum
open DividedPowers CrystallineSemistableComparison.Pb

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.LatCplB

structure LCS {N : Type} [AddCommGroup N] (c : ℕ) (G : AddSubgroup N) : Prop where
  hs : ∀ x ∈ G, (∀ n : ℕ, ∃ y ∈ G, x = (c ^ n) • y) → x = 0
  pc : ∀ s : ℕ → N, (∀ n, s n ∈ G) → (∀ n, ∃ y ∈ G, s (n + 1) - s n = (c ^ n) • y) →
    ∃ L ∈ G, ∀ n, ∃ y ∈ G, s n - L = (c ^ n) • y

section Conv
variable {R : Type} [CommRing R] (c : ℕ)

end Conv

section Concrete
open Lat
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

noncomputable def qn (l M i : ℕ) : ℚ := ((i.factorial : ℚ))⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ i

def T (k : ℕ) : Submodule W (A f ξ l M) := Submodule.span W (dpA f ξ l M '' {i | k ≤ i})

theorem smul_def' (u : W) (x : A f ξ l M) : u • x = ofW f ξ l M u * x := rfl

theorem ι_smul (u : W) (x : A f ξ l M) : ι f ξ l M (u • x) = f u * ι f ξ l M x := by
  rw [smul_def', map_mul, ι_ofW]

end Concrete

end GlobalTheory.CompanionTheory.LatCplB
