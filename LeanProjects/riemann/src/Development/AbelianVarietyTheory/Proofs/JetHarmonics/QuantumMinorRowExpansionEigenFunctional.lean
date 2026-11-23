import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowExp
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorEqUnitSmulOfRangeEqStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem qminor_row_step_under_functional : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (n t : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (a b : Fin (t + 1) → Fin n) (a' b' : Fin t → Fin n) (a0 b0 : Fin n) (p : ℂ), Formalism.REAL.GlRel E → Function.Injective a → Function.Injective b → Function.Injective a' → Function.Injective b' → Set.range a = insert a0 (Set.range a') → a0 ∉ Set.range a' → Set.range b = insert b0 (Set.range b') → b0 ∉ Set.range b' → a0 ∉ Set.range b → (∀ j v, l (E a0 (b j) v) = (if b j = b0 then p else 0) • l v) → ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ u v, l (Formalism.REAL.qminor E a b u v) = (e * p) • l (Formalism.REAL.qminor E a' b' u v) := by
  intro M Wp _ _ _ _ n t E l a b a' b' a0 b0 p hE ha hb ha' hb' hra ha0 hrb hb0 hab hl
  have hA : Function.Injective (Fin.cons a0 a' : Fin (t + 1) → Fin n) :=
    Fin.cons_injective_iff.2 ⟨ha0, ha'⟩
  have hB : Function.Injective (Fin.cons b0 b' : Fin (t + 1) → Fin n) :=
    Fin.cons_injective_iff.2 ⟨hb0, hb'⟩
  have hrB : Set.range b = Set.range (Fin.cons b0 b' : Fin (t + 1) → Fin n) := by
    rw [Fin.range_cons]; exact hrb
  obtain ⟨e, he, hq⟩ := GlobalTheory.T.quantumMinor_eq_unit_smul_of_range_eq (Module.End ℂ M) n (t + 1) E a (Fin.cons a0 a') b (Fin.cons b0 b') hE
    ha hA hb hB (by rw [Fin.range_cons]; exact hra) hrB
  refine ⟨e, he, fun u v => ?_⟩
  have key : ∀ (j : Fin (t + 1)) (w : ℂ) (x : M),
      l (Formalism.REAL.Tm E w a0 ((Fin.cons b0 b' : Fin (t + 1) → Fin n) j) x) = (if j = 0 then p else 0) • l x := by
    intro j w x
    have hmem : (Fin.cons b0 b' : Fin (t + 1) → Fin n) j ∈ Set.range b := by
      rw [hrB]; exact ⟨j, rfl⟩
    have hne : a0 ≠ (Fin.cons b0 b' : Fin (t + 1) → Fin n) j := fun h => hab (h ▸ hmem)
    obtain ⟨k, hk⟩ := hmem
    have hiff : b k = b0 ↔ j = 0 := by
      rw [hk]
      exact ⟨fun h => hB (by simpa using h), fun h => by subst h; rfl⟩
    unfold Formalism.REAL.Tm
    rw [if_neg hne, zero_add, ← hk, hl k x]
    simp only [hiff]
  rw [hq u, quantum_minor_row_expansion.1 (Module.End ℂ M) n t E hE, LinearMap.smul_apply, map_smul, LinearMap.sum_apply,
    map_sum, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero, mul_smul]
  · congr 1
    have h0 := key 0
    simp only [Fin.cons_zero, if_true] at h0
    simp only [Fin.val_zero, pow_zero, Int.cast_one, one_mul, Module.End.mul_apply, Fin.cons_zero, h0,
      Fin.succAbove_zero]
    rfl
  · intro j _
    rw [← zsmul_eq_mul, LinearMap.smul_apply, map_zsmul, Module.End.mul_apply, Fin.cons_zero, key,
      if_neg (Fin.succ_ne_zero j), zero_smul, smul_zero]

end GlobalTheory
