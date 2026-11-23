import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationLTorsionFreeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemLatticeSubIffSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFiltrationComapSpanPowStatement

set_option autoImplicit false

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatAdicClosedB

section
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

noncomputable def q (l M i : ℕ) : ℚ := (i.factorial : ℚ)⁻¹ * (((l : ℚ) ^ M)⁻¹) ^ i

def S (j : ℕ) : AddSubgroup B :=
  AddSubgroup.closure {b | ∃ (w : W) (i : ℕ), j ≤ i ∧ b = f w * Lat.dpE f ξ l M i}

theorem ι_mem (x : Lat.A f ξ l M) : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M :=
  Subtype.prop (show ↥(Lat.sub f ξ l M) from x)

end

end GlobalTheory.CompanionTheory.LatAdicClosedB
