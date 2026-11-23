import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PieriRules.KTypeIntDomStatement

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

def lowCompLin {n : ℕ} (μ : Fin n → ℝ) : ℝ :=
  ∑ c : Fin n, ((c : ℕ) : ℝ) * μ c

theorem lowComp_tensAct_apply {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*}
    [Fintype ι] {n : ℕ} (A : Fin n → Fin n → Module.End ℂ V) (M : Fin n → Fin n → Matrix ι ι ℂ)
    (a b : Fin n) (x : PiLp 2 (fun _ : ι => V)) (i : ι) :
    tensAct A M a b x i = A a b (x i) + ∑ j, M a b i j • x j := by
  simp [tensAct]

theorem lowComp_entry_wt {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {ε : Fin n → Bool}
    {M : Fin n → Fin n → Matrix ι ι ℂ} {γ : ι → Fin n → ℝ}
    (hM : Formalism.REAL.KRel ε M) (hd : ∀ a, M a a = Matrix.diagonal fun i => ((γ i a : ℝ) : ℂ))
    {a b : Fin n} (hab : a < b) (he : ε a = ε b) {j k : ι} (hne : M a b j k ≠ 0) (c : Fin n) :
    γ k c = γ j c + ((if c = b then 1 else 0) - (if c = a then 1 else 0)) := by
  have h := congrFun (congrFun (hM a b c c he rfl) j) k
  rw [hd c] at h
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have hba : b ≠ a := ne_of_gt hab
  have key : ((γ k c : ℝ) : ℂ) - ((γ j c : ℝ) : ℂ) =
      (((if c = b then 1 else 0) - (if c = a then 1 else 0) : ℝ) : ℂ) := by
    by_cases hcb : c = b
    · subst hcb
      have hca : ¬ c = a := hba
      simp only [if_neg hca, ite_true, Matrix.zero_apply, sub_zero] at h
      simp only [if_neg hca]
      apply mul_left_cancel₀ hne
      push_cast
      linear_combination h
    · by_cases hca : c = a
      · subst hca
        simp only [if_neg (Ne.symm hcb), ite_true, Matrix.zero_apply, zero_sub] at h
        simp only [if_neg hcb]
        apply mul_left_cancel₀ hne
        push_cast
        linear_combination h
      · simp only [if_neg (Ne.symm hcb), if_neg hca, Matrix.zero_apply, sub_zero] at h
        simp only [if_neg hcb, if_neg hca]
        apply mul_left_cancel₀ hne
        push_cast
        linear_combination h
  have key' : ((γ k c - γ j c : ℝ) : ℂ) =
      (((if c = b then 1 else 0) - (if c = a then 1 else 0) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub (γ k c)]; exact key
  have := Complex.ofReal_injective key'
  linarith

theorem lowComp_lin_entry {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {ε : Fin n → Bool}
    {M : Fin n → Fin n → Matrix ι ι ℂ} {γ : ι → Fin n → ℝ}
    (hM : Formalism.REAL.KRel ε M) (hd : ∀ a, M a a = Matrix.diagonal fun i => ((γ i a : ℝ) : ℂ))
    {a b : Fin n} (hab : a < b) (he : ε a = ε b) {j k : ι} (hne : M a b j k ≠ 0) :
    lowCompLin (γ k) = lowCompLin (γ j) + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
  have hk := lowComp_entry_wt hM hd hab he hne
  unfold lowCompLin
  simp only [hk, mul_add, mul_sub, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

theorem lowComp : LowCompStatement := by
  intro V _ _ n ε A ι _ _ M γ hM hd ν x hx hhw
  classical
  obtain ⟨hwt, hup⟩ := hhw
  set S : Finset ι := Finset.univ.filter (fun i => x i ≠ 0) with hS
  have hSne : S.Nonempty := by
    by_contra h
    apply hx
    ext i
    by_contra hi
    exact h ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa using hi⟩⟩
  obtain ⟨i0, hi0, hmax⟩ := S.exists_max_image (fun i => lowCompLin (γ i)) hSne
  refine ⟨γ i0, ⟨i0, rfl, (Finset.mem_filter.1 hi0).2⟩, ?_⟩
  intro j hj
  constructor
  · intro c
    have h := congrArg (fun y : PiLp 2 (fun _ : ι => V) => y j) (hwt c)
    simp only [lowComp_tensAct_apply, hd c, Matrix.diagonal_apply, ite_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, PiLp.smul_apply] at h
    rw [Pi.sub_apply, Complex.ofReal_sub, sub_smul, ← h, hj]
    abel
  · intro a b hab he
    have h := congrArg (fun y : PiLp 2 (fun _ : ι => V) => y j) (hup a b hab he)
    simp only [lowComp_tensAct_apply, PiLp.zero_apply] at h
    have hsum : ∑ k, M a b j k • x k = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_cases hne : M a b j k = 0
      · simp [hne]
      · have hxk : x k = 0 := by
          by_contra hxk
          have hle := hmax k (Finset.mem_filter.2 ⟨Finset.mem_univ _, hxk⟩)
          have hl := lowComp_lin_entry hM hd hab he hne
          rw [hj] at hl
          have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
          linarith
        simp [hxk]
    rw [hsum, add_zero] at h
    exact h

end ReciprocityTheory.ChartRestriction.DS.HW
