import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun

noncomputable section

open MeasureTheory NumberField MvPolynomial Filter Topology UpperTheory.ConvolutionTheory PositivityTheory.Rg.Fx

namespace UpperTheory.ConvolutionTheory.BW.Op

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
  (ev : PR K n →+* (H →L[ℂ] H)) (B : H →L[ℂ] H)

def am : H →L[ℂ] H := ev (C (X none))

def zm (α : Ix K n →₀ ℕ) : H →L[ℂ] H := ev (C (rename some (monomial α 1)))

def tp : MvPolynomial (Ix K n) ℂ →ₗ[ℂ] (H →L[ℂ] H) :=
  (basisMonomials (Ix K n) ℂ).constr ℂ fun α => B ^ α.degree * zm ev α

def yk (W : H →L[ℂ] H) (g : MvPolynomial (Pl K × Fin n) (MvPolynomial (Ix K n) ℂ)) : H →L[ℂ] H :=
  ∑ β ∈ g.support, tp ev B (g.coeff β) * ev (monomial β 1) * W

theorem tp_monomial (α : Ix K n →₀ ℕ) : tp ev B (monomial α 1) = B ^ α.degree * zm ev α := by
  have := (basisMonomials (Ix K n) ℂ).constr_basis ℂ (fun α => B ^ α.degree * zm ev α) α
  rwa [coe_basisMonomials] at this

theorem tp_eq (p : MvPolynomial (Ix K n) ℂ) :
    tp ev B p = ∑ α ∈ p.support, p.coeff α • (B ^ α.degree * zm ev α) := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← tp_monomial, ← map_smul, smul_monomial, smul_eq_mul, mul_one]

theorem ev_comm (a b : PR K n) : Commute (ev a) (ev b) := by
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]

theorem zm_zero : zm ev 0 = 1 := by simp [zm]

theorem zm_add (α β : Ix K n →₀ ℕ) : zm ev (α + β) = zm ev α * zm ev β := by
  rw [zm, zm, zm, ← map_mul, ← map_mul, ← map_mul, monomial_mul, one_mul]

theorem zm_single (x : Ix K n) : zm ev (Finsupp.single x 1) = ev (C (X (some x))) := by
  rw [zm, ← X, rename_X]

theorem deg_le {ι : Type} {d : ℕ} {p : MvPolynomial ι ℂ} (h : p.totalDegree ≤ d) {α : ι →₀ ℕ}
    (hα : α ∈ p.support) : α.degree ≤ d := by
  have := (le_totalDegree hα).trans h
  simpa [Finsupp.degree_apply, Finsupp.sum] using this

theorem comm_yk {T W : H →L[ℂ] H} {g : MvPolynomial (Pl K × Fin n) (MvPolynomial (Ix K n) ℂ)} (hB : Commute T B)
    (hW : Commute T W) (h1 : ∀ p, Commute T (ev (C p))) (h2 : ∀ β ∈ g.support, Commute T (ev (monomial β 1))) :
    Commute T (yk ev B W g) := by
  refine Commute.sum_right _ _ _ fun β hβ => (Commute.mul_right ?_ (h2 β hβ)).mul_right hW
  rw [tp_eq]
  exact Commute.sum_right _ _ _ fun α _ => ((hB.pow_right _).mul_right (h1 _)).smul_right _

theorem mono_norm : ∃ D : ℝ, 1 ≤ D ∧ ∀ α : Ix K n →₀ ℕ, ‖B ^ α.degree * zm ev α‖ ≤ D ^ α.degree := by
  have h1 : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have h0 : 0 ≤ ∑ x, ‖zm ev (Finsupp.single x 1)‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hz : ∀ (m : ℕ) (α : Ix K n →₀ ℕ), α.degree = m → ‖zm ev α‖ ≤ (1 + ∑ x, ‖zm ev (Finsupp.single x 1)‖) ^ m := by
    intro m α
    induction α using Finsupp.induction_linear generalizing m with
    | zero => rintro rfl; simpa [zm_zero] using h1
    | add a b ha hb =>
      rintro rfl
      rw [zm_add, map_add, pow_add]
      exact (norm_mul_le _ _).trans (mul_le_mul (ha _ rfl) (hb _ rfl) (norm_nonneg _) (by positivity))
    | single i e =>
      rintro rfl
      rw [Finsupp.degree_single]
      have hi := Finset.single_le_sum (f := fun x => ‖zm ev (Finsupp.single x 1)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
      induction e with
      | zero => simpa [zm_zero] using h1
      | succ e ih =>
        rw [Finsupp.single_add, zm_add, pow_succ]
        exact (norm_mul_le _ _).trans (mul_le_mul ih (by linarith) (norm_nonneg _) (by positivity))
  have hb : ∀ m : ℕ, ‖B ^ m‖ ≤ (1 + ‖B‖) ^ m := by
    intro m
    induction m with
    | zero => simpa using h1
    | succ m ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul ih (by linarith) (norm_nonneg _) (by positivity))
  refine ⟨(1 + ‖B‖) * (1 + ∑ x, ‖zm ev (Finsupp.single x 1)‖), ?_, fun α => ?_⟩
  · nlinarith [norm_nonneg B, mul_nonneg (norm_nonneg B) h0]
  · rw [mul_pow]
    exact (norm_mul_le _ _).trans (mul_le_mul (hb _) (hz _ α rfl) (norm_nonneg _) (by positivity))

theorem yk_norm (W : H →L[ℂ] H) (G : ℕ → MvPolynomial (Pl K × Fin n) (MvPolynomial (Ix K n) ℂ))
    (s : Finset ((Pl K × Fin n) →₀ ℕ)) (K₀ : ℝ) (hs : ∀ k, (G k).support ⊆ s)
    (hG : ∀ k β, ((G k).coeff β).totalDegree ≤ k ∧ l1 ((G k).coeff β) ≤ K₀ ^ (k + 1) / k.factorial) :
    ∃ c x : ℝ, 0 ≤ c ∧ 1 ≤ x ∧ ∀ k, ‖yk ev B W (G k)‖ ≤ c * (x ^ k / k.factorial) := by
  obtain ⟨D, hD, hb⟩ := mono_norm ev B
  have ht : ∀ (k : ℕ) (p : MvPolynomial (Ix K n) ℂ), p.totalDegree ≤ k → ‖tp ev B p‖ ≤ l1 p * D ^ k := by
    intro k p hp
    rw [tp_eq, l1, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α hα => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left ((hb α).trans (pow_le_pow_right₀ hD (deg_le hp hα))) (norm_nonneg _)
  set E : ℝ := |K₀| + 1 with hE
  have hE1 : 1 ≤ E := by have := abs_nonneg K₀; linarith
  have hM : 0 ≤ ∑ β ∈ s, ‖ev (monomial β 1) * W‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨E * ∑ β ∈ s, ‖ev (monomial β 1) * W‖, E * D, by positivity, by nlinarith, fun k => ?_⟩
  have h3 : K₀ ^ (k + 1) ≤ E ^ (k + 1) :=
    (le_abs_self _).trans (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) _)
  calc ‖yk ev B W (G k)‖ ≤ ∑ β ∈ (G k).support, E ^ (k + 1) / k.factorial * D ^ k * ‖ev (monomial β 1) * W‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
        rw [mul_assoc]
        refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((ht k _ (hG k β).1).trans ?_) (norm_nonneg _))
        exact mul_le_mul_of_nonneg_right ((hG k β).2.trans (by gcongr)) (by positivity)
    _ ≤ ∑ β ∈ s, E ^ (k + 1) / k.factorial * D ^ k * ‖ev (monomial β 1) * W‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (hs k) fun _ _ _ => by positivity
    _ = _ := by rw [← Finset.mul_sum, mul_pow]; ring

theorem tail {V : Type} [NormedAddCommGroup V] [CompleteSpace V] (y : ℕ → V) (c x : ℝ) (hc : 0 ≤ c) (hx : 1 ≤ x)
    (h : ∀ k, ‖y k‖ ≤ c * (x ^ k / k.factorial)) (M : ℝ) (hM : 0 ≤ M) :
    Summable y ∧ ∃ C' : ℝ, ∀ d : ℕ, ‖∑ k ∈ Finset.range (d + 1), y k - ∑' k, y k‖ * M ≤ C' ^ (d + 1) / d.factorial := by
  have hs := Real.summable_pow_div_factorial x
  have hy : Summable y := Summable.of_norm_bounded (hs.mul_left c) h
  have hs0 : 0 ≤ ∑' k : ℕ, x ^ k / (k.factorial : ℝ) := tsum_nonneg fun _ => by positivity
  set e := ∑' k : ℕ, x ^ k / (k.factorial : ℝ) with he
  refine ⟨hy, (c * e * M + 1) * x, fun d => ?_⟩
  rw [← hy.sum_add_tsum_nat_add (d + 1), sub_add_cancel_left, norm_neg]
  have h1 : ‖∑' k, y (k + (d + 1))‖ ≤ c * (x ^ (d + 1) / d.factorial) * e := by
    refine tsum_of_norm_bounded (hs.hasSum.mul_left _) fun k => (h _).trans ?_
    rw [mul_assoc, div_mul_div_comm, ← pow_add, add_comm k]
    refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) (by positivity) ?_) hc
    have := (Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add d k)).trans
      (Nat.factorial_le (show d + k ≤ d + 1 + k by omega))
    exact_mod_cast this
  have h0 : 0 ≤ c * e * M := by positivity
  have h7 : c * e * M ≤ (c * e * M + 1) ^ (d + 1) :=
    (by linarith : c * e * M ≤ c * e * M + 1).trans (le_self_pow₀ (by linarith) (Nat.succ_ne_zero d))
  calc _ ≤ c * (x ^ (d + 1) / d.factorial) * e * M := mul_le_mul_of_nonneg_right h1 hM
    _ = c * e * M * x ^ (d + 1) / d.factorial := by ring
    _ ≤ (c * e * M + 1) ^ (d + 1) * x ^ (d + 1) / d.factorial := by gcongr
    _ = _ := by rw [mul_pow]

variable {ev B}

theorem fix_mul (hB : ∀ R, Commute B (ev R)) {W T : H →L[ℂ] H} (hW : am ev * B * W = W) (h1 : Commute T (am ev)) (h2 : Commute T B) :
    am ev * B * (T * W) = T * W := by
  rw [← mul_assoc, ← (h1.mul_right h2).eq, mul_assoc, hW]

theorem fix_pow (hB : ∀ R, Commute B (ev R)) {W : H →L[ℂ] H} (hW : am ev * B * W = W) (a : ℕ) :
    am ev ^ a * (B ^ a * W) = W := by
  have hc : Commute (am ev) B := (hB _).symm
  rw [← mul_assoc, ← hc.mul_pow]
  induction a with
  | zero => simp
  | succ a ih => rw [pow_succ, mul_assoc, hW, ih]

theorem trunc_mul (hc : ∀ c : ℂ, ev (C (C c)) = c • 1) (hB : ∀ R, Commute B (ev R)) {W : H →L[ℂ] H} (hW : am ev * B * W = W)
    (G : ℕ → MvPolynomial (Pl K × Fin n) (MvPolynomial (Ix K n) ℂ)) (hG : ∀ k β, ((G k).coeff β).totalDegree ≤ k) (d : ℕ) :
    ev (trunc d G) * W = am ev ^ d * (am ev * ∑ k ∈ Finset.range (d + 1), yk ev B (B * W) (G k)) := by
  have h1 : ∀ (p : MvPolynomial (Ix K n) ℂ) (V : H →L[ℂ] H), p.totalDegree ≤ d → am ev * B * V = V →
      ev (C (homog d p)) * V = am ev ^ d * (tp ev B p * V) := by
    intro p V hp hV
    rw [homog, tp_eq, map_sum, map_sum, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    have hd := deg_le hp hα
    have e : rename some (monomial α (p.coeff α) : MvPolynomial (Ix K n) ℂ) = C (p.coeff α) * rename some (monomial α 1) := by
      rw [rename_monomial, rename_monomial, C_mul_monomial, mul_one]
    have e2 : am ev ^ d = am ev ^ (d - α.degree) * am ev ^ α.degree := by rw [← pow_add]; congr 1; omega
    have e3 := fix_pow hB (fix_mul hB hV (T := zm ev α) (ev_comm ev _ _) (hB _).symm) α.degree
    rw [e, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, hc, e2]
    simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_assoc, e3]
    rfl
  rw [trunc, map_sum, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [yk, map_sum, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  have hd : ((G k).coeff β).totalDegree ≤ d := (hG k β).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have e : (monomial β (homog d ((G k).coeff β)) : PR K n) = C (homog d ((G k).coeff β)) * monomial β 1 := by
    rw [C_mul_monomial, mul_one]
  have hA : Commute (am ev) (tp ev B ((G k).coeff β) * ev (monomial β 1)) := by
    refine Commute.mul_right ?_ (ev_comm ev _ _)
    rw [tp_eq]
    exact Commute.sum_right _ _ _ fun α _ => (((hB _).symm.pow_right _).mul_right (ev_comm ev _ _)).smul_right _
  rw [e, map_mul, mul_assoc, h1 _ _ hd (fix_mul hB hW (ev_comm ev _ _) (hB _).symm), ← mul_assoc (am ev), hA.eq,
    mul_assoc _ (am ev), ← mul_assoc (am ev), hW, mul_assoc]

end UpperTheory.ConvolutionTheory.BW.Op
