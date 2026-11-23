import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableProdPi

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.SiegelSum

theorem summable_pi_prod {J A : Type} [Fintype J] (f : J → A → ℝ) (h0 : ∀ j a, 0 ≤ f j a)
    (hs : ∀ j, Summable (f j)) : Summable fun n : J → A => ∏ j, f j (n j) := by
  first
  | exact @_root_.GlobalTheory.SummableProdPi.summable_prod_pi
  | exact _root_.GlobalTheory.SummableProdPi.summable_prod_pi
  | (apply _root_.GlobalTheory.SummableProdPi.summable_prod_pi <;> assumption)
  | (intros; apply _root_.GlobalTheory.SummableProdPi.summable_prod_pi <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SummableProdPi.summable_prod_pi <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SummableProdPi.summable_prod_pi ..)

theorem exists_mul_dotProduct_le {ι : Type} [Fintype ι] {Y : Matrix ι ι ℝ} (hY : Y.PosDef) :
    ∃ c > 0, ∀ x : ι → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Y *ᵥ x) := by
  have hc : Continuous fun x : ι → ℝ => x ⬝ᵥ (Y *ᵥ x) := by
    simp only [dotProduct, mulVec]
    fun_prop
  obtain ⟨c, hc0, hcl⟩ := (isCompact_sphere (0 : ι → ℝ) 1).exists_forall_le'
    hc.continuousOn (a := 0) (fun q hq => by
      have hx0 : q ≠ 0 := by
        intro h0
        simp [h0] at hq
      simpa using hY.dotProduct_mulVec_pos hx0)
  refine ⟨c / (Fintype.card ι + 1), by positivity, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h1 := hcl (‖x‖⁻¹ • x) (by simp [norm_smul, hn.ne'])
  simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1
  have h2 : c * ‖x‖ ^ 2 ≤ x ⬝ᵥ (Y *ᵥ x) := by
    have := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖x‖)
    refine this.trans_eq ?_
    field_simp
  have h3 : x ⬝ᵥ x ≤ (Fintype.card ι + 1) * ‖x‖ ^ 2 := by
    have : x ⬝ᵥ x ≤ ∑ _i : ι, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => by
      have := norm_le_pi_norm x i
      rw [Real.norm_eq_abs] at this
      rw [← sq, ← sq_abs]
      gcongr
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    nlinarith [sq_nonneg ‖x‖]
  calc c / (Fintype.card ι + 1) * (x ⬝ᵥ x) ≤ c / (Fintype.card ι + 1) *
        ((Fintype.card ι + 1) * ‖x‖ ^ 2) := by gcongr
    _ = c * ‖x‖ ^ 2 := by field_simp
    _ ≤ _ := h2

theorem exists_int_of_intM {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ} (hR : 0 < R)
    {x : Matrix κ ι ℚ} (hx : IntM ((R : ℚ) • x)) :
    ∃ n : κ → ι → ℤ, x = Matrix.of fun k i => (n k i : ℚ) / R := by
  have : ∀ k i, ∃ n : ℤ, (n : ℚ) = R * x k i := fun k i => by
    have := IsIntegrallyClosed.isIntegral_iff.1 (hx k i)
    simpa using this
  choose n hn using this
  refine ⟨n, ?_⟩
  ext k i
  have : (R : ℚ) ≠ 0 := by positivity
  simp only [of_apply, hn]
  field_simp

theorem exists_bound {κ ι : Type} [Fintype κ] [Fintype ι] {R : ℕ} (hR : 0 < R)
    {φ : Matrix κ ι ℚ → ℂ} (h : HasLevel R φ) : ∃ M, ∀ x, ‖φ x‖ ≤ M := by
  classical
  let g : (κ → ι → Fin (R * R)) → ℝ := fun r => ‖φ (Matrix.of fun k i => ((r k i : ℕ) : ℚ) / R)‖
  refine ⟨∑ r, g r, fun x => ?_⟩
  by_cases hx : φ x = 0
  · rw [hx, norm_zero]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨n, rfl⟩ := exists_int_of_intM hR (h.1 x hx)
  have hRR : (0 : ℤ) < (R : ℤ) * R := by positivity
  let r : κ → ι → Fin (R * R) := fun k i => ⟨(n k i % (R * R)).toNat, by
    have := Int.emod_lt_of_pos (n k i) hRR
    have := Int.emod_nonneg (n k i) hRR.ne'
    zify; rw [Int.toNat_of_nonneg this]; assumption⟩
  have key := h.2 (Matrix.of fun k i => ((r k i : ℕ) : ℚ) / R)
    (Matrix.of fun k i => ((n k i / (R * R) : ℤ) : ℚ)) (fun k i => isIntegral_algebraMap (x := n k i / (R * R)))
  have he : (Matrix.of fun k i => (n k i : ℚ) / R) =
      (Matrix.of fun k i => ((r k i : ℕ) : ℚ) / R) +
        (R : ℚ) • (Matrix.of fun k i => ((n k i / (R * R) : ℤ) : ℚ)) := by
    ext k i
    have h1 : (((r k i : ℕ) : ℤ)) = n k i % (R * R) :=
      Int.toNat_of_nonneg (Int.emod_nonneg (n k i) hRR.ne')
    have h2 := Int.emod_add_mul_ediv (n k i) (R * R)
    rw [← h1] at h2
    have h3 : ((r k i : ℕ) : ℚ) + R * R * ((n k i / (R * R) : ℤ) : ℚ) = n k i := by
      exact_mod_cast h2
    have : (R : ℚ) ≠ 0 := by positivity
    simp only [of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← h3]
    field_simp
  rw [he, key]
  exact Finset.single_le_sum (f := g) (fun _ _ => norm_nonneg _) (Finset.mem_univ r)

theorem sum_le_im {ι : Type} [Fintype ι] {τ : Matrix ι ι ℂ} {c S : ℝ}
    (hc : ∀ x : ι → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (τ.map Complex.im *ᵥ x)) (ζ : ι → ℂ)
    (hS : ∀ i, |(ζ i).im| ≤ S) (v : ι → ℚ) :
    ∑ i, (c * (v i : ℝ) ^ 2 - 2 * S * |(v i : ℝ)|) ≤
      (qv v ⬝ᵥ τ *ᵥ qv v + 2 * (qv v ⬝ᵥ ζ)).im := by
  have h1 : (qv v ⬝ᵥ τ *ᵥ qv v).im =
      (fun i => (v i : ℝ)) ⬝ᵥ (τ.map Complex.im *ᵥ fun i => (v i : ℝ)) := by
    simp [dotProduct, mulVec, qv, Complex.im_sum, Complex.re_sum]
  have h2 : (2 * (qv v ⬝ᵥ ζ)).im = ∑ i, 2 * ((v i : ℝ) * (ζ i).im) := by
    simp [dotProduct, qv, Complex.im_sum, Finset.mul_sum]
  rw [Complex.add_im, h1, h2, Finset.sum_sub_distrib, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  refine add_le_add (le_trans (le_of_eq ?_) (hc _)) (Finset.sum_le_sum fun i _ => ?_)
  · simp [dotProduct, Finset.mul_sum, sq]
  · have h3 := neg_abs_le ((v i : ℝ) * (ζ i).im)
    rw [abs_mul] at h3
    nlinarith [hS i, abs_nonneg (v i : ℝ)]

theorem summable_norm_thetaTerm : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (φ : Matrix κ ι ℚ → ℂ), IsSB φ → ∀ τ ∈ Siegel ι, ∀ ζ : κ → ι → ℂ, Summable fun x : Matrix κ ι ℚ => ‖φ x * cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) + 2 * (qv (x k) ⬝ᵥ ζ k)))‖ := by
  intro κ ι _ _ _ φ ⟨R, hR, h⟩ τ hτ ζ
  obtain ⟨M, hM⟩ := exists_bound hR h
  obtain ⟨c, hc0, hc⟩ := exists_mul_dotProduct_le hτ.2
  have hR0 : (R : ℝ) ≠ 0 := by positivity
  have hS : ∀ k i, |(ζ k i).im| ≤ ‖ζ‖ := fun k i =>
    (Complex.abs_im_le_norm _).trans ((norm_le_pi_norm (ζ k) i).trans (norm_le_pi_norm ζ k))
  let e : (κ → ι → ℤ) → Matrix κ ι ℚ := fun n => Matrix.of fun k i => (n k i : ℚ) / R
  have he : Function.Injective e := by
    intro m n hmn
    funext k i
    have h1 : (m k i : ℚ) / R = (n k i : ℚ) / R := congrFun (congrFun hmn k) i
    have : (R : ℚ) ≠ 0 := by positivity
    exact_mod_cast (div_left_inj' this).1 h1
  refine (he.summable_iff fun x hx => ?_).1 ?_
  · have : φ x = 0 := by
      by_contra h0
      obtain ⟨n, hn⟩ := exists_int_of_intM hR (h.1 x h0)
      exact hx ⟨n, hn.symm⟩
    simp [this]
  let f : ℤ → ℝ := fun n => Real.exp (-π * (c / R ^ 2 * n ^ 2 - 2 * (‖ζ‖ / R) * |n|))
  have hf : Summable f := by
    simpa [f] using summable_pow_mul_jacobiTheta₂_term_bound (‖ζ‖ / R)
      (T := c / R ^ 2) (by positivity) 0
  have hs : Summable fun n : κ → ι → ℤ => ∏ k, ∏ i, f (n k i) :=
    summable_pi_prod (fun (_ : κ) (m : ι → ℤ) => ∏ i, f (m i))
      (fun _ _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)
      fun _ => summable_pi_prod (fun _ => f) (fun _ _ => (Real.exp_pos _).le) fun _ => hf
  refine (hs.mul_left M).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
  simp only [Function.comp_apply, norm_mul]
  refine mul_le_mul (hM _) ?_ (norm_nonneg _) ((norm_nonneg _).trans (hM 0))
  simp only [f, ← Real.exp_sum, Complex.norm_exp, Real.exp_le_exp, ← Finset.mul_sum]
  have h1 : ∀ z : ℂ, (π * I * z).re = -π * z.im := fun z => by simp
  rw [h1, Complex.im_sum]
  refine mul_le_mul_of_nonpos_left (Finset.sum_le_sum fun k _ => ?_) (by linarith [Real.pi_pos])
  refine le_trans (le_of_eq ?_) (sum_le_im hc (ζ k) (hS k) (e n k))
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [e, of_apply, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, abs_div, Nat.abs_cast,
    Int.cast_abs]
  field_simp

end GlobalTheory.SW.SiegelSum
