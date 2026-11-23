import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UnitaryRootEmbedding
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UpperTriangular

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot

namespace GlobalTheory.CompanionTheory.SwapRoot.Unip

variable {L : Type} [Field L] {n : ℕ}

noncomputable def UT (A : Matrix (Fin n) (Fin n) L) : Prop :=
  _root_.UpperTheory.Reformulated.B.UpperTriangular.UT A

theorem UT.mul {A B : Matrix (Fin n) (Fin n) L} (hA : UT A) (hB : UT B) : UT (A * B) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with h | h
    · rw [hA.1 i k h, zero_mul]
    · rw [hB.1 k j (lt_of_lt_of_le hij h), mul_zero]
  · rw [Matrix.mul_apply, Fintype.sum_eq_single i]
    · rw [hA.2, hB.2, one_mul]
    · intro k hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hA.1 i k h, zero_mul]
      · rw [hB.1 k i h, mul_zero]

def pn (n a b : ℕ) : ℕ :=
  if b = a then a + 1 else if b = a + 1 then a else
    if b = n - 2 - a then n - 1 - a else if b = n - 1 - a then n - 2 - a else b

theorem pn_lt {a b : ℕ} (h : 2 * (a + 2) ≤ n) (hb : b < n) : pn n a b < n := by
  unfold pn; split_ifs <;> omega

def pF (a : ℕ) (h : 2 * (a + 2) ≤ n) (b : Fin n) : Fin n := ⟨pn n a b.val, pn_lt h b.2⟩

theorem sR_uR_mul_unip : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (v : GU σ n), IsUnipU v →
    ∃ y : L, ∀ x : L, ∃ b : GU σ n, IsUnipU b ∧
      sR σ hσ a h * uR σ hσ a h x * v = b * (sR σ hσ a h * uR σ hσ a h (x + y)) :=
  _root_.UpperTheory.Reformulated.B.AntidiagonalWeylElement.sR_uR_mul_unip

end GlobalTheory.CompanionTheory.SwapRoot.Unip

end
