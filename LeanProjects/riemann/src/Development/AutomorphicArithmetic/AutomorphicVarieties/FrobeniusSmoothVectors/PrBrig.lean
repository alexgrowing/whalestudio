import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PresDefs

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem upT_mul {K : Type} [CommRing K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} (hA : UpT A) (hB : UpT B) :
    UpT (A * B) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rcases lt_or_ge c i with hc | hc
  · rw [hA i c hc, zero_mul]
  · rw [hB c j (lt_of_lt_of_le h hc), mul_zero]

private theorem upT_of_comm {K : Type} [Field K] {n : ℕ} {T Z : Matrix (Fin n) (Fin n) K} (hT : UpT T)
    (hd : ∀ i j, i ≠ j → T i i ≠ T j j) (h : UpT (T * Z - Z * T)) : UpT Z := by
  have key : ∀ m : ℕ, ∀ i j : Fin n, n - i.val + j.val = m → j < i → Z i j = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i j hm hji
      have h0 := h i j hji
      have hji' : j.val < i.val := hji
      rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single i, Finset.sum_eq_single j] at h0
      · have h1 : (T i i - T j j) * Z i j = 0 := by linear_combination h0
        exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 (hd i j hji.ne'))
      · intro c _ hc
        rcases lt_or_gt_of_ne hc with hc | hc
        · have hc' : c.val < j.val := hc
          rw [ih (n - i.val + c.val) (by omega) i c rfl (hc.trans hji), zero_mul]
        · rw [hT c j hc, mul_zero]
      · simp
      · intro c _ hc
        rcases lt_or_gt_of_ne hc with hc | hc
        · rw [hT i c hc, zero_mul]
        · have hc' : i.val < c.val := hc
          have := c.isLt
          rw [ih (n - c.val + j.val) (by omega) c j rfl (hji.trans hc), mul_zero]
      · simp
  exact fun i j hij => key _ i j rfl hij

theorem UpperTheory.V.Fr.pr_brig :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}, ∀ (K : Type) [Field K] (ρ : NRep F n K) (B : Box F n K), B.Of ρ → ρ.Good → ∀ (v : F.V) (Y : Matrix (Fin n) (Fin n) K), (∀ s, B.ad (F.loc v s) Y - Y ∈ B.b v) → Y ∈ B.b v := by
  intro l _ k _ F n K _ ρ B hOf hG v Y hY
  obtain ⟨s, hs⟩ := hG.ψd v
  have hT := B.tri v s
  have hr : (B.r (F.loc v s)).right = 1 := (B.nu _).trans (F.loc0 v s).2
  have hres : (B.r (F.loc v s)).mat = ρ.r (F.loc0 v s) := hOf.res (F.loc0 v s)
  have h1 : UpT ((B.g v : Matrix (Fin n) (Fin n) K) * ((B.r (F.loc v s)).adFun Y - Y) *
      (((B.g v)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := hY s
  show UpT ((B.g v : Matrix (Fin n) (Fin n) K) * Y * (((B.g v)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
  refine upT_of_comm hT (fun i j hij => ?_) ?_
  · rw [hres, hOf.psi, hOf.psi]
    exact fun e => hs i j hij (Units.ext e)
  · convert upT_mul h1 hT using 1
    simp only [GG.adFun, hr, if_true, GG.mat, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
      Units.inv_mul_cancel_left]
