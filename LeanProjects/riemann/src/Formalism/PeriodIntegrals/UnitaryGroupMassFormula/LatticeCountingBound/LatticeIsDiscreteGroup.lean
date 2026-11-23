import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.SepDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.LatticeIsometry

noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

open PI.LatCountG

theorem hsN_nonneg' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsN A := by
  unfold hsN
  exact Real.sqrt_nonneg _

theorem lattice_is_discrete_group : LatIsG := by
  intro I x
  obtain ⟨Λ, h1, h2, h3⟩ := PI.UnitaryGroupMassFormula.LSC.lattice_isometry I x
  exact ⟨Λ, h1, h2, h3⟩

theorem gram_nonneg (hDM : PI.UnitaryGroupMassFormula.LSC.DetMono) (I : Formalism.MainNotions.S.AutInst) (z : I.GA) (v : InfinitePlace I.F) {j : ℕ}
    (b : Fin j → Fin I.n → I.E) : 0 ≤ ((gramV I z v b).det).re := by
  let C : Matrix (Fin I.n) (Fin j) ℂ := Matrix.of fun i a => coordV I z v (b a) i
  have hG : gramV I z v b = Cᴴ * C := by
    ext a c
    simp [gramV, C, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hG]
  exact (hDM I.n j C 1 1 zero_le_one (fun w => by simp)).1

theorem ht_eq (I : Formalism.MainNotions.S.AutInst) {z : I.GA} (s : Sub I z) :
    ht I s = (∏ v, ((gramV I z v s.b).det).re) / (idx I s.B s.b : ℝ) := rfl

theorem tau_pow_le_ht (hDM : PI.UnitaryGroupMassFormula.LSC.DetMono) (I : Formalism.MainNotions.S.AutInst) (z : I.GA) (hz : 0 < tau1 I z) (s : Sub I z) :
    tau1 I z ^ (2 * I.f * s.j) ≤ ht I s ∧ idx I s.B s.b ≠ 0 := by
  have hf : 0 < I.f := Module.finrank_pos
  have hj : 0 < s.j := s.j_pos
  have hN : (0 : ℝ) < 2 * (I.f : ℝ) * (s.j : ℝ) := by
    have : (0 : ℝ) < I.f := by exact_mod_cast hf
    have : (0 : ℝ) < s.j := by exact_mod_cast hj
    positivity
  have hht : ∀ t : Sub I z, 0 ≤ ht I t := by
    intro t
    rw [ht_eq]
    exact div_nonneg (Finset.prod_nonneg fun v _ => gram_nonneg hDM I z v t.b) (Nat.cast_nonneg _)
  have hsize : ∀ t : Sub I z, 0 ≤ size I t := fun t => Real.rpow_nonneg (hht t) _
  have hle : tau1 I z ≤ size I s :=
    (min_le_right _ _).trans (ciInf_le ⟨0, by rintro _ ⟨t, rfl⟩; exact hsize t⟩ s)
  have hpow : size I s ^ (2 * I.f * s.j) = ht I s := by
    unfold size
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hht s)]
    push_cast
    rw [one_div_mul_cancel hN.ne', Real.rpow_one]
  refine ⟨?_, ?_⟩
  · calc tau1 I z ^ (2 * I.f * s.j) ≤ size I s ^ (2 * I.f * s.j) := pow_le_pow_left₀ hz.le hle _
      _ = ht I s := hpow
  · intro h0
    have h1 : ht I s = 0 := by
      rw [ht_eq, h0]
      simp
    have hs0 : size I s = 0 := by
      unfold size
      rw [h1, Real.zero_rpow (one_div_pos.2 hN).ne']
    linarith

theorem separation_of_points : SepOf := by
  intro hLat hDual hCh hArch hIdx hNP hDM _hCard I x y hx hy δ hδ hmap
  obtain ⟨Λ, hFG, hspan, hΛ⟩ := hLat I y
  obtain ⟨k, u, b', hk, hu, hind1, hspan1, hb', hind2, hperp, hspan2⟩ := hCh I y δ hδ
  have huΛ : ∀ c, u c ∈ Λ := fun c => by
    have := hu c
    rw [hΛ] at this
    exact this
  have hbΛ : ∀ a, b' a ∈ Λ := fun a => by
    have := hb' a
    rw [hΛ] at this
    exact this
  let s₁ : Sub I x :=
    { j := k
      j_pos := hk
      b := fun c => δ *ᵥ u c
      b_ind := hind1
      B := imSub I Λ δ
      B_lat := by
        intro z hz
        obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hz
        exact hmap w (by rw [hΛ]; exact hw)
      b_mem := fun c => Submodule.mem_map.2 ⟨u c, huΛ c, rfl⟩
      B_span := by
        intro z hz
        obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hz
        exact hspan1 w }
  let s₂ : Sub I y :=
    { j := k
      j_pos := hk
      b := b'
      b_ind := hind2
      B := perpSub I Λ δ
      B_lat := by
        intro z hz
        rw [hΛ]
        exact (Submodule.mem_inf.1 hz).1
      b_mem := fun a => Submodule.mem_inf.2 ⟨hbΛ a, hperp a⟩
      B_span := fun z hz => hspan2 z (Submodule.mem_inf.1 hz).2 }
  obtain ⟨h1, hi1⟩ := tau_pow_le_ht hDM I x hx s₁
  obtain ⟨h2, hi2⟩ := tau_pow_le_ht hDM I y hy s₂
  rw [ht_eq] at h1 h2
  change tau1 I x ^ (2 * I.f * k) ≤ (∏ v, ((gramV I x v (fun c => δ *ᵥ u c)).det).re) /
    (idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) : ℝ) at h1
  change tau1 I y ^ (2 * I.f * k) ≤ (∏ v, ((gramV I y v b').det).re) / (idx I (perpSub I Λ δ) b' : ℝ) at h2
  change idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) ≠ 0 at hi1
  change idx I (perpSub I Λ δ) b' ≠ 0 at hi2
  have hdualΛ : ∀ w, (∀ w' ∈ Λ, hf I w' w ∈ (algebraMap (𝓞 I.E) I.E).range) → w ∈ Λ := by
    intro w hw
    have := hDual I y w (by rw [hΛ]; exact hw)
    rw [hΛ] at this
    exact this
  have hN := hIdx I Λ hFG hspan hdualΛ δ k u b' huΛ hind1 hspan1 hbΛ hind2 hperp hspan2 hi1 hi2
  have hNP' := hNP I (pairM I b' u).det
  have hi1' : (0 : ℝ) < idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) := by exact_mod_cast Nat.pos_of_ne_zero hi1
  have hi2' : (0 : ℝ) < idx I (perpSub I Λ δ) b' := by exact_mod_cast Nat.pos_of_ne_zero hi2
  have hHp : 0 ≤ ∏ v, hsN (amat I x y v δ) := Finset.prod_nonneg fun v _ => hsN_nonneg' _
  have key : ((tau1 I x * tau1 I y) ^ I.f) ^ (2 * k) ≤ (∏ v, hsN (amat I x y v δ)) ^ (2 * k) := by
    rw [← pow_mul, mul_pow, show I.f * (2 * k) = 2 * I.f * k by ring]
    calc tau1 I x ^ (2 * I.f * k) * tau1 I y ^ (2 * I.f * k)
        ≤ ((∏ v, ((gramV I x v (fun c => δ *ᵥ u c)).det).re) / (idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) : ℝ)) *
          ((∏ v, ((gramV I y v b').det).re) / (idx I (perpSub I Λ δ) b' : ℝ)) :=
          mul_le_mul h1 h2 (pow_nonneg (hy.le) _) ((pow_nonneg hx.le _).trans h1)
      _ = (∏ v, (((gramV I x v (fun c => δ *ᵥ u c)).det).re * ((gramV I y v b').det).re)) /
          ((idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) : ℝ) * (idx I (perpSub I Λ δ) b' : ℝ)) := by
          rw [Finset.prod_mul_distrib, div_mul_div_comm]
      _ ≤ (∏ v, (hsN (amat I x y v δ) ^ (2 * k) * ‖I.φ v (pairM I b' u).det‖ ^ 2)) /
          ((idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) : ℝ) * (idx I (perpSub I Λ δ) b' : ℝ)) := by
          apply div_le_div_of_nonneg_right _ (mul_pos hi1' hi2').le
          exact Finset.prod_le_prod (fun v _ => mul_nonneg (gram_nonneg hDM I x v _) (gram_nonneg hDM I y v _))
            (fun v _ => hArch I x y δ k u b' v hind1 hspan1 hind2 hperp)
      _ = (∏ v, hsN (amat I x y v δ)) ^ (2 * k) * |((Algebra.norm ℚ (pairM I b' u).det : ℚ) : ℝ)| /
          ((idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) : ℝ) * (idx I (perpSub I Λ δ) b' : ℝ)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow, hNP']
      _ ≤ (∏ v, hsN (amat I x y v δ)) ^ (2 * k) := by
          rw [div_le_iff₀ (mul_pos hi1' hi2')]
          exact mul_le_mul_of_nonneg_left hN (pow_nonneg hHp _)
  exact le_of_pow_le_pow_left₀ (by omega) hHp key

end PI.UnitaryGroupMassFormula.LCG
