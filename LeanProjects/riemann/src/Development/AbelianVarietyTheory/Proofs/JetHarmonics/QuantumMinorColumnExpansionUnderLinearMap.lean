import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialFirstColumn.FirstColumnSplitBijective
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CapStepCol

theorem exists_perm_of_range_eq {n t : ℕ} (a a₂ : Fin t → Fin n) (ha : Function.Injective a)
    (h : Set.range a = Set.range a₂) : ∃ τ : Equiv.Perm (Fin t), a = a₂ ∘ τ := by
  have h1 : ∀ i, ∃ j, a₂ j = a i := fun i => by
    have : a i ∈ Set.range a₂ := h ▸ Set.mem_range_self i
    exact this
  choose f hf using h1
  have hinj : Function.Injective f := fun i j hij => ha (by rw [← hf i, ← hf j, hij])
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), ?_⟩
  funext i
  simp [hf]

theorem norm_sign {t : ℕ} (τ : Equiv.Perm (Fin t)) :
    ‖(((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ)‖ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]

theorem cap_step_col : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (n t : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (a b : Fin (t + 1) → Fin n) (a' b' : Fin t → Fin n) (a0 b0 : Fin n) (p : ℂ), Formalism.REAL.GlRel E → Function.Injective a → Function.Injective b → Function.Injective a' → Function.Injective b' → Set.range a = insert a0 (Set.range a') → a0 ∉ Set.range a' → Set.range b = insert b0 (Set.range b') → b0 ∉ Set.range b' → b0 ∉ Set.range a → (∀ j v, l (E (a j) b0 v) = (if a j = a0 then p else 0) • l v) → ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ u v, l (Formalism.REAL.qminor E a b u v) = (e * p) • l (Formalism.REAL.qminor E a' b' (u - 1) v) := by
  intro M Wp _ _ _ _ n t E l a b a' b' a0 b0 p hE ha hb ha' hb' hra ha0 hrb hb0 hba hl
  obtain ⟨σ, hσ⟩ := exists_perm_of_range_eq a (Fin.cons a0 a' : Fin (t + 1) → Fin n) ha
    (by rw [hra, Fin.range_cons])
  obtain ⟨τ, hτ⟩ := exists_perm_of_range_eq b (Fin.cons b0 b' : Fin (t + 1) → Fin n) hb
    (by rw [hrb, Fin.range_cons])
  refine ⟨(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ), ?_, ?_⟩
  · rw [norm_mul, norm_sign, norm_sign, one_mul]
  intro u v
  have hT : ∀ (j : Fin (t + 1)) (w : M),
      l (Formalism.REAL.Tm E u ((Fin.cons a0 a' : Fin (t + 1) → Fin n) j) b0 w) =
        (if j = 0 then p else 0) • l w := by
    intro j w
    have hmem : (Fin.cons a0 a' : Fin (t + 1) → Fin n) j ∈ Set.range a := by
      rw [hra, ← Fin.range_cons]; exact Set.mem_range_self j
    obtain ⟨i, hi⟩ := hmem
    have hne : a i ≠ b0 := fun h => hba ⟨i, h⟩
    have hiff : a i = a0 ↔ j = 0 := by
      rw [hi]
      refine Fin.cases ?_ (fun k => ?_) j
      · simp
      · simp only [Fin.cons_succ, Fin.succ_ne_zero, iff_false]
        exact fun h => ha0 ⟨k, h⟩
    rw [← hi, Formalism.REAL.Tm, if_neg hne, zero_add, hl]
    simp only [hiff]
  have key : l (Formalism.REAL.qminor E (Fin.cons a0 a' : Fin (t + 1) → Fin n)
      (Fin.cons b0 b' : Fin (t + 1) → Fin n) u v) = p • l (Formalism.REAL.qminor E a' b' (u - 1) v) := by
    rw [PI.QmColExpWork.expFirst, LinearMap.sum_apply, map_sum, Finset.sum_eq_single 0]
    · have e1 : (Fin.cons a0 a' : Fin (t + 1) → Fin n) ∘ (0 : Fin (t + 1)).succAbove = a' := by
        funext k; simp
      have e2 : (Fin.cons b0 b' : Fin (t + 1) → Fin n) ∘ Fin.succ = b' := by
        funext k; simp
      rw [e1, e2]
      simp only [Fin.val_zero, pow_zero, Int.cast_one, one_mul, Module.End.mul_apply]
      have := hT 0 (Formalism.REAL.qminor E a' b' (u - 1) v)
      simpa using this
    · intro j _ hj
      rw [Module.End.mul_apply, Module.End.intCast_apply, map_zsmul, Module.End.mul_apply,
        Fin.cons_zero, hT, if_neg hj, zero_smul, smul_zero]
    · simp
  rw [hσ, hτ, Formalism.REAL.quantumMinorRowSkew_holds, Formalism.REAL.quantumMinorColSkew_holds _ _ _ E hE,
    Module.End.mul_apply, Module.End.mul_apply, Module.End.intCast_apply,
    Module.End.intCast_apply, map_zsmul, map_zsmul, key, mul_smul, mul_smul,
    Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]

end GlobalTheory.CapStepCol
