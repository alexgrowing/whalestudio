import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.PurElim

noncomputable section

open MvPolynomial Classical

namespace PI.FJMB

variable {σ : Type*}

private theorem fin_zero_lt_of_ne_zero {k : ℕ} (i : Fin (k + 1)) (hi : i ≠ 0) : (0 : Fin (k + 1)) < i := by
  revert hi
  refine Fin.cases ?_ ?_ i
  · intro h
    exact absurd rfl h
  · intro j _
    exact Fin.succ_pos j

private theorem aeval_fill_sub_multiple_of_zeroth_line {m n : ℕ} (ι : Fin (m + 1) × Fin n → σ) (hι : Function.Injective ι)
    (f : MvPolynomial σ ℂ) (hf : ∀ b : Fin (m + 1), 0 < b → PI.FJM.bRow ι 0 b f = 0)
    (M : Fin (m + 1) → Fin n → ℂ) (p : σ → ℂ) (c : Fin n) :
    ∀ S : Finset (Fin (m + 1)), (0 : Fin (m + 1)) ∉ S →
      aeval (fill ι (fun i k => if i ∈ S then M i k - M i c / M 0 c * M 0 k else M i k) p) f =
        aeval (fill ι M p) f := by
  intro S
  refine Finset.induction_on S ?_ ?_
  · intro _
    simp
  · intro b S hb ih hS
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hS (Finset.mem_insert_self _ _)
    have hS0 : (0 : Fin (m + 1)) ∉ S := fun h => hS (Finset.mem_insert_of_mem h)
    rw [← ih hS0]
    have hfun : (fun i k => if i ∈ insert b S then M i k - M i c / M 0 c * M 0 k else M i k) =
        rowAddM (fun i k => if i ∈ S then M i k - M i c / M 0 c * M 0 k else M i k) 0 b
          (-(M b c / M 0 c)) := by
      funext i k
      by_cases hib : i = b
      · subst hib
        simp [rowAddM, hb, hS0] <;> ring
      · simp [rowAddM, hib]
    rw [hfun]
    exact row_inv ι hι 0 b (Ne.symm hb0) f (hf b (fin_zero_lt_of_ne_zero b hb0)) _ p _

private theorem aeval_fill_column_elimination {m n : ℕ} (ι : Fin m × Fin (n + 1) → σ) (hι : Function.Injective ι)
    (f : MvPolynomial σ ℂ) (hf : ∀ d : Fin (n + 1), 0 < d → PI.FJM.bCol ι 0 d f = 0)
    (M : Fin m → Fin (n + 1) → ℂ) (p : σ → ℂ) (r : Fin m) :
    ∀ T : Finset (Fin (n + 1)), (0 : Fin (n + 1)) ∉ T →
      aeval (fill ι (fun i k => if k ∈ T then M i k - M r k / M r 0 * M i 0 else M i k) p) f =
        aeval (fill ι M p) f := by
  intro T
  refine Finset.induction_on T ?_ ?_
  · intro _
    simp
  · intro b T hb ih hT
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hT (Finset.mem_insert_self _ _)
    have hT0 : (0 : Fin (n + 1)) ∉ T := fun h => hT (Finset.mem_insert_of_mem h)
    rw [← ih hT0]
    have hfun : (fun i k => if k ∈ insert b T then M i k - M r k / M r 0 * M i 0 else M i k) =
        colAddM (fun i k => if k ∈ T then M i k - M r k / M r 0 * M i 0 else M i k) 0 b
          (-(M r b / M r 0)) := by
      funext i k
      by_cases hkb : k = b
      · subst hkb
        simp [colAddM, hb, hT0] <;> ring
      · simp [colAddM, hkb]
    rw [hfun]
    exact col_inv ι hι 0 b (Ne.symm hb0) f (hf b (fin_zero_lt_of_ne_zero b hb0)) _ p _

theorem elim_step {m n : ℕ} (ι : Fin (m + 1) × Fin (n + 1) → σ) (hι : Function.Injective ι)
    (f : MvPolynomial σ ℂ) (hf : HWB ι f) (hg : aeval (killS (edge ι)) f = 0) : f = 0 := by
  haveI : Infinite ℂ := Infinite.of_injective (Nat.cast : ℕ → ℂ) Nat.cast_injective
  have key : ∀ y : σ → ℂ, y (ι (0, 0)) ≠ 0 → aeval y f = 0 := by
    intro y hc
    let M : Fin (m + 1) → Fin (n + 1) → ℂ := fun i k => y (ι (i, k))
    let M1 : Fin (m + 1) → Fin (n + 1) → ℂ := fun i k =>
      if i ∈ Finset.univ.erase (0 : Fin (m + 1)) then M i k - M i 0 / M 0 0 * M 0 k else M i k
    let M2 : Fin (m + 1) → Fin (n + 1) → ℂ := fun i k =>
      if k ∈ Finset.univ.erase (0 : Fin (n + 1)) then M1 i k - M1 0 k / M1 0 0 * M1 i 0 else M1 i k
    have hy : fill ι M y = y := by
      funext v
      by_cases hv : ∃ x, ι x = v
      · obtain ⟨x, rfl⟩ := hv
        exact fill_ι hι M y x
      · push_neg at hv
        exact fill_not ι M y v hv
    have h1 : aeval (fill ι M1 y) f = aeval (fill ι M y) f :=
      aeval_fill_sub_multiple_of_zeroth_line ι hι f (fun b hb => hf.1 0 b hb) M y 0 (Finset.univ.erase 0) (by simp)
    have h2 : aeval (fill ι M2 y) f = aeval (fill ι M1 y) f :=
      aeval_fill_column_elimination ι hι f (fun d hd => hf.2 0 d hd) M1 y 0 (Finset.univ.erase 0) (by simp)
    have hvan : ∀ v ∈ edge ι, fill ι M2 y v = 0 := by
      intro v hv
      simp only [edge, Set.mem_setOf_eq] at hv
      rcases hv with ⟨l, rfl⟩ | ⟨j, rfl⟩
      · rw [fill_ι hι]
        simp [M2, M1, M]
        all_goals first
          | (field_simp; done)
          | (field_simp; ring)
          | (rw [div_mul_cancel₀ _ hc, sub_self])
          | simp [hc]
      · rw [fill_ι hι]
        simp [M2, M1, M]
        all_goals first
          | (field_simp; done)
          | (field_simp; ring)
          | (rw [div_mul_cancel₀ _ hc, sub_self])
          | simp [hc]
    have h3 := aeval_killS_of_zero (edge ι) (fill ι M2 y) hvan f
    rw [hg, map_zero] at h3
    calc aeval y f = aeval (fill ι M y) f := by rw [hy]
      _ = aeval (fill ι M1 y) f := h1.symm
      _ = aeval (fill ι M2 y) f := h2.symm
      _ = 0 := h3.symm
  have hmul : f * X (ι (0, 0)) = 0 := by
    apply MvPolynomial.funext
    intro y
    rw [map_mul, MvPolynomial.eval_X, map_zero]
    by_cases hy0 : y (ι (0, 0)) = 0
    · rw [hy0, mul_zero]
    · have e : MvPolynomial.eval y f = aeval y f := by
        first
          | rfl
          | simp [MvPolynomial.coe_aeval_eq_eval]
      rw [e, key y hy0, zero_mul]
  exact (mul_eq_zero.mp hmul).resolve_right (MvPolynomial.X_ne_zero _)

theorem diag_zero : ∀ (m n : ℕ) (ι : Fin m × Fin n → σ), Function.Injective ι → ∀ f : MvPolynomial σ ℂ,
    HWB ι f → aeval (killS (offD ι)) f = 0 → f = 0 := by
  intro m
  induction m with
  | zero =>
    intro n ι _ f _ hg
    have hempty : offD ι = ∅ := by
      ext v
      simp only [offD, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨i, _, _, _⟩
      exact Fin.elim0 i
    rw [hempty, aeval_killS_empty] at hg
    exact hg
  | succ m ih =>
    intro n
    cases n with
    | zero =>
      intro ι _ f _ hg
      have hempty : offD ι = ∅ := by
        ext v
        simp only [offD, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨_, k, _, _⟩
        exact Fin.elim0 k
      rw [hempty, aeval_killS_empty] at hg
      exact hg
    | succ n =>
      intro ι hι f hf hg
      have hinj : Function.Injective (fun x : Fin m × Fin n => ι (x.1.succ, x.2.succ)) := by
        intro x y hxy
        have h := hι hxy
        simp only [Prod.mk.injEq, Fin.succ_inj] at h
        exact Prod.ext h.1 h.2
      apply elim_step ι hι f hf
      apply ih n (fun x : Fin m × Fin n => ι (x.1.succ, x.2.succ)) hinj _ (hwb_restrict ι hι f hf)
      rw [aeval_killS_union, offD_step ι hι]
      exact hg

end PI.FJMB
