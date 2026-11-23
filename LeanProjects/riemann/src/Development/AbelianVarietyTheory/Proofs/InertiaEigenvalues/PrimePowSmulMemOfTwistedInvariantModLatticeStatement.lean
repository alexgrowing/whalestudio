import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowSmulMemOfTwistedInvariantModLattice
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_pow_smul_mem_of_twistedInvariant_mod_lattice : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ J : Finset ℤ, HTBasis act χ (Gj K m) U (J : Set ℤ) → ∀ (i : ℤ), i ∉ J → ∀ M : AddSubgroup (Fin r → PadicComplex l), ball l r ⊆ (M : Set _) → (∀ x ∈ M, (l : PadicComplex l) • x ∈ ball l r) → ∀ y : Fin r → PadicComplex l, (∀ σ ∈ Gj K m, twAct act χ i U σ y - y ∈ M) → (l : PadicComplex l) ^ (2 + max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i)))) • y ∈ M := by
  first | exact @GlobalTheory.FrameInv.pow_smul_mem_of_invariant_mod | exact GlobalTheory.FrameInv.pow_smul_mem_of_invariant_mod | (intros; apply GlobalTheory.FrameInv.pow_smul_mem_of_invariant_mod <;> assumption)
