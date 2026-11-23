import Formalism.FrobeniusBaseCase.FrobeniusBaseCaseProofs.CoeffFrobOfNotDvd
import Formalism.FrobeniusBaseCase.FrobeniusBaseCaseProofs.HasUniqueFixedPoint

open MvPowerSeries

namespace Formalism.BaseCaseIdentities

noncomputable section

open Classical

variable {k : Type*} [Field k] {Z C : Type*}

theorem hasWt_term [Fintype Z] {v : AddValuation k (WithTop ℝ)} {r w : ℝ} {M : ℕ} (hM : 1 ≤ M)
    (x : Z → k) (h : HasWt v r w (∑ d, MvPowerSeries.C (x d) * X d ^ M)) (d : Z) :
    HasWt v r w (MvPowerSeries.C (x d) * X d ^ M) := by
  intro A
  rw [coeff_C_mul, coeff_X_pow]
  split_ifs with hA
  · subst hA
    have h1 := h (Finsupp.single d M)
    rw [coeff_sum_C_mul_X_pow] at h1
    have h2 : (∑ e, if Finsupp.single d M = Finsupp.single e M then x e else 0) = x d := by
      rw [Finset.sum_eq_single d]
      · simp
      · intro e _ hne
        rw [if_neg]
        intro heq
        exact hne ((Finsupp.single_left_inj (by omega)).1 heq).symm
      · simp
    rw [h2] at h1
    simpa using h1
  · simp

theorem hasWt_pow_sub_frob [Fintype Z] {v : AddValuation k (WithTop ℝ)} {r w : ℝ} {l e M : ℕ}
    (hl : l.Prime) (hv : v (l : k) = 1) (he : 1 ≤ e) (hM : 1 ≤ M)
    (x : Z → k) (h : HasWt v r w (∑ d, MvPowerSeries.C (x d) * X d ^ M)) :
    HasWt v r (1 + ((l ^ e : ℕ) : ℝ) * w)
      ((∑ d, MvPowerSeries.C (x d) * X d ^ M) ^ (l ^ e)
        - frob (l ^ e) (∑ d, MvPowerSeries.C (x d) * X d ^ M)) := by
  have h1 := hasWt_sum_pow_sub hl hv he Finset.univ (fun d _ => hasWt_term hM x h d)
  rw [frob_sum_X (Nat.one_le_pow _ _ hl.pos) hM]
  have h2 : ∀ d, (MvPowerSeries.C (x d) * X d ^ M : MvPowerSeries Z k) ^ (l ^ e)
      = MvPowerSeries.C (x d ^ (l ^ e)) * X d ^ (l ^ e * M) := by
    intro d
    rw [mul_pow, ← map_pow, ← pow_mul, mul_comm M]
  simpa only [h2] using h1

namespace Data

variable [Fintype Z] [Fintype C] (D : Data k Z C)

theorem lR : (3 : ℝ) ≤ (D.l : ℝ) := by exact_mod_cast D.l_ge

theorem two_K : 2 * D.K = D.i + 1 := by
  obtain ⟨n, hn⟩ := D.i_odd
  simp only [K, Kn]
  omega

theorem K_pos : 1 ≤ D.K := by
  have := D.two_K
  omega

theorem q_pos : 1 ≤ D.q := Nat.one_le_pow _ _ D.l_prime.pos

theorem q_odd : Odd D.q := by
  have : Odd D.l := D.l_prime.odd_of_ne_two (by have := D.l_ge; omega)
  exact this.pow

theorem l_ne : (D.l : k) ≠ 0 := by
  intro h
  have h1 := D.v_l
  rw [h, AddValuation.map_zero] at h1
  exact WithTop.top_ne_one h1

theorem v_l_inv : D.v (D.l : k)⁻¹ = ((-1 : ℝ) : WithTop ℝ) := by
  have h1 : D.v ((D.l : k) * (D.l : k)⁻¹) = 0 := by
    rw [mul_inv_cancel₀ D.l_ne, AddValuation.map_one]
  rw [AddValuation.map_mul, D.v_l] at h1
  induction h : D.v (D.l : k)⁻¹ using WithTop.recTopCoe with
  | top => rw [h] at h1; simp at h1
  | coe y =>
    rw [h] at h1
    have h2 : ((1 + y : ℝ) : WithTop ℝ) = ((0 : ℝ) : WithTop ℝ) := by
      rw [WithTop.coe_add]; exact h1
    have h3 : 1 + y = 0 := WithTop.coe_injective h2
    have : y = -1 := by linarith
    rw [this]

theorem v_neg_l_inv : D.v (-(D.l : k)⁻¹) = ((-1 : ℝ) : WithTop ℝ) := by
  rw [AddValuation.map_neg, D.v_l_inv]

theorem zvec_eq_zero {c : C} (hc : D.lev c ≠ 0) : D.zvec c = 0 := by
  unfold zvec
  apply Finset.sum_eq_zero
  intro d _
  rw [if_neg]
  rintro rfl
  exact hc (D.ι_lev d)

theorem wt_zvec (c : C) : D.Wt D.rad (D.zvec c) := by
  unfold zvec
  apply HasWt.sum
  intro d _
  split_ifs
  · exact HasWt.X d
  · exact HasWt.zero

theorem m_succ (s : ℕ) (b : C) : D.m (s + 1) b = MvPowerSeries.C (-(D.l : k)⁻¹) *
    ∑ c, frob D.q (D.m s c) * MvPowerSeries.C (D.g c b) := rfl

theorem q_cast : (D.q : ℝ) = qnum D.l := by simp [q, qnum]

theorem q_rho : qnum D.l * rho D.l = 1 + rho D.l := by
  have := sqMulIdentity_statement D.l (by have := D.l_ge; omega)
  linarith

theorem wt_m (s : ℕ) (c : C) : D.Wt (rho D.l + qnum D.l ^ s * sg D.l D.i) (D.m s c) := by
  induction s generalizing c with
  | zero =>
    rw [pow_zero, one_mul]
    exact D.wt_zvec c
  | succ s ih =>
    rw [m_succ]
    have h1 : ∀ c', D.Wt (0 + (D.q : ℝ) * (rho D.l + qnum D.l ^ s * sg D.l D.i))
        (frob D.q (D.m s c') * MvPowerSeries.C (D.g c' c)) := fun c' =>
      HasWt.mul_C (by simpa using D.g_int c' c) (HasWt.frob (ih c') D.q)
    have h2 := HasWt.C_mul (le_of_eq D.v_neg_l_inv.symm)
      (HasWt.sum Finset.univ (fun c' _ => h1 c'))
    refine HasWt.mono ?_ h2
    rw [D.q_cast, pow_succ]
    have := D.q_rho
    nlinarith

theorem sg_pos : 0 < sg D.l D.i := by
  unfold sg
  have := D.lR
  positivity

theorem wt_m_rho (s : ℕ) (c : C) : D.Wt (rho D.l) (D.m s c) := by
  refine HasWt.mono ?_ (D.wt_m s c)
  have h1 := D.sg_pos
  have h2 : 0 < qnum D.l ^ s := by
    unfold qnum
    have := D.lR
    positivity
  nlinarith [mul_pos h2 h1]

theorem m_closed (s : ℕ) (hs : s < D.K) :
    ∃ P : C → Z → k, (∀ c d, 0 ≤ D.v (P c d)) ∧ (∀ c, D.lev c ≠ s → ∀ d, P c d = 0) ∧
    ∀ c, D.m s c = MvPowerSeries.C ((-1) ^ s * ((D.l : k) ^ eNum D.l s)⁻¹) *
      ∑ d, MvPowerSeries.C (P c d) * X d ^ (D.q ^ s) := by
  have hl2 : 2 ≤ D.l := by have := D.l_ge; omega
  induction s with
  | zero =>
    refine ⟨fun c d => if D.ι d = c then 1 else 0, ?_, ?_, ?_⟩
    · intro c d
      show 0 ≤ D.v (if D.ι d = c then 1 else 0)
      split_ifs <;> simp
    · intro c hc d
      show (if D.ι d = c then (1 : k) else 0) = 0
      rw [if_neg]
      rintro rfl
      exact hc (D.ι_lev d)
    · intro c
      have h0 : eNum D.l 0 = 0 := (identity_e D.l 0 hl2).1
      rw [h0]
      show D.zvec c = _
      unfold zvec
      simp only [pow_zero, inv_one, mul_one, map_one, one_mul, pow_one]
      refine Finset.sum_congr rfl fun d _ => ?_
      split_ifs <;> simp
  | succ s ih =>
    obtain ⟨P, hP1, hP2, hP3⟩ := ih (by omega)
    refine ⟨fun b d => ∑ c, P c d ^ D.q * D.g c b, ?_, ?_, ?_⟩
    · intro b d
      apply AddValuation.map_le_sum
      intro c _
      rw [AddValuation.map_mul, AddValuation.map_pow]
      exact add_nonneg (nsmul_nonneg (hP1 c d) _) (D.g_int c b)
    · intro b hb d
      apply Finset.sum_eq_zero
      intro c _
      by_cases hc : D.lev c = s
      · rw [D.g_supp c (by rw [hc]; exact hs) b (by rw [hc]; exact hb), mul_zero]
      · rw [hP2 c hc d, zero_pow (by have := D.q_pos; omega), zero_mul]
    · intro b
      rw [m_succ]
      obtain ⟨κ, hκ⟩ : ∃ κ : k, κ = (-1) ^ s * ((D.l : k) ^ eNum D.l s)⁻¹ := ⟨_, rfl⟩
      rw [← hκ] at hP3
      have hfr : ∀ c, frob D.q (D.m s c) =
          ∑ d, MvPowerSeries.C ((κ * P c d) ^ D.q) * X d ^ (D.q * D.q ^ s) := by
        intro c
        rw [hP3 c, Finset.mul_sum]
        have : ∀ d, (MvPowerSeries.C κ * (MvPowerSeries.C (P c d) * X d ^ (D.q ^ s)) :
            MvPowerSeries Z k) = MvPowerSeries.C (κ * P c d) * X d ^ (D.q ^ s) := by
          intro d
          rw [map_mul, mul_assoc]
        simp only [this]
        exact frob_sum_X D.q_pos (Nat.one_le_pow _ _ D.q_pos) _
      have hκ' : -(D.l : k)⁻¹ * κ ^ D.q = (-1) ^ (s + 1) * ((D.l : k) ^ eNum D.l (s + 1))⁻¹ := by
        have he : eNum D.l (s + 1) = 1 + D.q * eNum D.l s := (identity_e D.l s hl2).2.1
        have hsign : ((-1 : k)) ^ (s * D.q) = (-1) ^ s := by
          rw [mul_comm, pow_mul, D.q_odd.neg_one_pow]
        rw [he, hκ, mul_pow, ← pow_mul, hsign, inv_pow, ← pow_mul, pow_succ, pow_add, pow_one,
          mul_inv, mul_comm (eNum D.l s) D.q]
        ring
      rw [← hκ']
      simp only [hfr, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [map_sum, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← pow_succ', mul_pow]
      simp only [map_mul, map_neg, map_pow]
      ring

theorem chainI_holds : D.ChainI := fun s hs => ⟨D.m_closed s hs, D.wt_m s⟩

theorem m_eq_zero {s : ℕ} (hs : s < D.K) {c : C} (hc : D.lev c ≠ s) : D.m s c = 0 := by
  obtain ⟨P, _, hP2, hP3⟩ := D.m_closed s hs
  rw [hP3 c]
  simp [hP2 c hc]

theorem ord_m {s : ℕ} (hs : s < D.K) (c : C) : OrdGE 1 (D.m s c) := by
  obtain ⟨P, _, _, hP3⟩ := D.m_closed s hs
  rw [hP3 c]
  apply OrdGE.C_mul
  apply OrdGE.sum
  intro d _
  apply OrdGE.C_mul
  exact OrdGE.mono (Nat.one_le_pow _ _ D.q_pos) (OrdGE.pow (OrdGE.X d) _)

theorem wt_m_pow_sub_frob {s : ℕ} (hs : s < D.K) (c : C) :
    D.Wt (1 + qnum D.l * rho D.l) (D.m s c ^ D.q - frob D.q (D.m s c)) := by
  obtain ⟨P, _, _, hP3⟩ := D.m_closed s hs
  have hw := D.wt_m_rho s c
  obtain ⟨κ, hκ⟩ : ∃ κ : k, κ = (-1) ^ s * ((D.l : k) ^ eNum D.l s)⁻¹ := ⟨_, rfl⟩
  rw [← hκ] at hP3
  have h1 : D.m s c = ∑ d, MvPowerSeries.C (κ * P c d) * X d ^ (D.q ^ s) := by
    rw [hP3 c, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [map_mul, mul_assoc]
  rw [h1] at hw ⊢
  have := hasWt_pow_sub_frob D.l_prime D.v_l (le_refl 2 |>.trans' (by norm_num : 1 ≤ 2))
    (Nat.one_le_pow _ _ D.q_pos) _ hw
  rw [← D.q_cast]
  exact this

end Data

end

end Formalism.BaseCaseIdentities
