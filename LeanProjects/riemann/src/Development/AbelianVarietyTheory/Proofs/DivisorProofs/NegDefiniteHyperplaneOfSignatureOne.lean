import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKCx
open scoped TensorProduct

namespace GlobalTheory.HermitianSignatureForms

section Forms

variable {n : ℕ}

def S (H : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) : ℂ := star x ⬝ᵥ H *ᵥ y

theorem S_conj (P D : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    S (Pᴴ * D * P) x y = S D (P *ᵥ x) (P *ᵥ y) := by
  unfold S
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

theorem S_smul_mat (c : ℂ) (H : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    S (c • H) x y = c * S H x y := by
  unfold S
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem S_smul_right (c : ℂ) (H : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    S H x (c • y) = c * S H x y := by
  unfold S
  rw [mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem S_smul_left (c : ℂ) (H : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    S H (c • x) y = (starRingEnd ℂ) c * S H x y := by
  unfold S
  rw [star_smul, smul_dotProduct, smul_eq_mul]; rfl

theorem S_sub_right (H : Matrix (Fin n) (Fin n) ℂ) (x y y' : Fin n → ℂ) :
    S H x (y - y') = S H x y - S H x y' := by
  unfold S
  rw [mulVec_sub, dotProduct_sub]

theorem S_sub_left (H : Matrix (Fin n) (Fin n) ℂ) (x x' y : Fin n → ℂ) :
    S H (x - x') y = S H x y - S H x' y := by
  unfold S
  rw [star_sub, sub_dotProduct]

theorem S_symm {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (x y : Fin n → ℂ) :
    S H y x = (starRingEnd ℂ) (S H x y) := by
  unfold S
  change _ = star _
  rw [← star_dotProduct_star, star_star, star_mulVec, hH.eq, ← dotProduct_mulVec]

theorem S_diag (d : Fin n → ℝ) (x : Fin n → ℂ) :
    (S (diagonal (fun i => (d i : ℂ))) x x).re = ∑ i, d i * ‖x i‖ ^ 2 := by
  unfold S
  simp only [dotProduct, mulVec_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp
  ring

theorem S_cont (H : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun xy : (Fin n → ℂ) × (Fin n → ℂ) => S H xy.1 xy.2 := by
  unfold S
  simp only [dotProduct, mulVec, Pi.star_apply]
  fun_prop

theorem bound_of_pos (q : (Fin n → ℂ) → ℝ) (hc : Continuous q)
    (hh : ∀ (t : ℝ) x, q ((t : ℂ) • x) = t ^ 2 * q x) (hp : ∀ x, x ≠ 0 → 0 < q x) :
    ∃ K : ℝ, ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 ≤ s → (∀ x, q (Y *ᵥ x) = s * q x) →
      ∀ a b, ‖Y a b‖ ≤ K * √s := by
  obtain ⟨ε, hε, h⟩ := (isCompact_sphere (0 : Fin n → ℂ) 1).exists_forall_le' (a := 0) hc.continuousOn
    (fun x hx => hp x (by rintro rfl; simp at hx))
  have key : ∀ x, ε * ‖x‖ ^ 2 ≤ q x := by
    intro x
    by_cases hx : x = 0
    · have := hh 0 x
      subst hx
      simp at this ⊢
      exact this.ge
    · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
      have h1 := h (((‖x‖⁻¹ : ℝ) : ℂ) • x) (by
        rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, norm_inv, norm_norm]
        exact inv_mul_cancel₀ hn.ne')
      rw [hh] at h1
      calc ε * ‖x‖ ^ 2 ≤ (‖x‖⁻¹ ^ 2 * q x) * ‖x‖ ^ 2 := by gcongr
        _ = q x := by field_simp
  obtain ⟨M, hM⟩ := (Set.finite_range fun b : Fin n => q (Pi.single b 1)).bddAbove
  refine ⟨√(M / ε), fun Y s hs hY a b => ?_⟩
  have h1 := key (Y *ᵥ Pi.single b 1)
  rw [hY] at h1
  have h2 : q (Pi.single b 1) ≤ M := hM ⟨b, rfl⟩
  have h3 : ‖Y a b‖ ≤ ‖Y *ᵥ Pi.single b 1‖ := by
    have := norm_le_pi_norm (Y *ᵥ Pi.single b 1) a
    simpa [mulVec_single_one] using this
  rw [← Real.sqrt_mul' _ hs]
  apply Real.le_sqrt_of_sq_le
  have h4 : ‖Y a b‖ ^ 2 ≤ ‖Y *ᵥ Pi.single b 1‖ ^ 2 := by gcongr
  have h5 : s * q (Pi.single b 1) ≤ s * M := by gcongr
  rw [div_mul_eq_mul_div, le_div_iff₀ hε]
  nlinarith

theorem S_sim {H Y : Matrix (Fin n) (Fin n) ℂ} {s : ℝ} (h : Yᴴ * H * Y = (s : ℂ) • H) (x y : Fin n → ℂ) :
    S H (Y *ᵥ x) (Y *ᵥ y) = s * S H x y := by
  rw [← S_conj, h, S_smul_mat]

theorem S_real_smul (H : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (x : Fin n → ℂ) :
    (S H ((t : ℂ) • x) ((t : ℂ) • x)).re = t ^ 2 * (S H x x).re := by
  rw [S_smul_left, S_smul_right]
  simp
  ring

theorem bound_neg (H : Matrix (Fin n) (Fin n) ℂ) (hneg : ∀ x, x ≠ 0 → (S H x x).re < 0) :
    ∃ K : ℝ, ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 ≤ s → Yᴴ * H * Y = (s : ℂ) • H →
      ∀ a b, ‖Y a b‖ ≤ K * √s := by
  obtain ⟨K, hK⟩ := bound_of_pos (fun x => -(S H x x).re)
    ((Complex.continuous_re.comp ((S_cont H).comp (continuous_id.prodMk continuous_id))).neg)
    (fun t x => by rw [S_real_smul]; ring) (fun x hx => neg_pos.2 (hneg x hx))
  refine ⟨K, fun Y s hs hY => hK Y s hs fun x => ?_⟩
  rw [S_sim hY]
  simp

theorem bound_hyp (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) (l : Fin n → ℂ)
    (hneg : ∀ x, x ≠ 0 → l ⬝ᵥ x = 0 → (S H x x).re < 0) (z : Fin n → ℂ) (hz : 0 < (S H z z).re) :
    ∃ K : ℝ, ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ), 0 < s → Yᴴ * H * Y = (s : ℂ) • H →
      (∃ c : ℂ, Y *ᵥ z = c • z) → ∀ a b, ‖Y a b‖ ≤ K * √s := by
  have him : ∀ x, (S H x x).im = 0 := fun x => by
    have := congrArg Complex.im (S_symm hH x x)
    simp at this
    linarith
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp [S] at hz
  have hl : l ⬝ᵥ z ≠ 0 := fun h => by linarith [hneg z hz0 h]
  obtain ⟨K, hK⟩ := bound_of_pos (fun x => 2 * Complex.normSq (S H z x) - (S H z z).re * (S H x x).re)
    (by
      have h1 : Continuous fun x => S H z x := (S_cont H).comp (continuous_const.prodMk continuous_id)
      have h2 : Continuous fun x => S H x x := (S_cont H).comp (continuous_id.prodMk continuous_id)
      have h3 := Complex.continuous_normSq.comp h1
      have h4 := Complex.continuous_re.comp h2
      exact (continuous_const.mul h3).sub (continuous_const.mul h4))
    (fun t x => by rw [S_real_smul, S_smul_right, map_mul, Complex.normSq_ofReal]; ring)
    (fun x hx => by
      set t : ℂ := (l ⬝ᵥ x) / (l ⬝ᵥ z) with ht
      have hu : l ⬝ᵥ (x - t • z) = 0 := by
        rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, ht, div_mul_cancel₀ _ hl, sub_self]
      by_cases h0 : x - t • z = 0
      · have hx' : x = t • z := sub_eq_zero.1 h0
        have ht0 : t ≠ 0 := by
          rintro h
          rw [h, zero_smul] at hx'
          exact hx hx'
        have htp : 0 < Complex.normSq t := Complex.normSq_pos.2 ht0
        clear_value t
        subst hx'
        rw [S_smul_left, S_smul_right, map_mul, ← mul_assoc ((starRingEnd ℂ) t), ← Complex.normSq_eq_conj_mul_self,
          Complex.normSq_apply (S H z z), him z]
        simp only [Complex.re_ofReal_mul]
        have := mul_pos htp (mul_pos hz hz)
        nlinarith
      · have h1 := hneg _ h0 hu
        rw [S_sub_left, S_sub_right, S_sub_right, S_smul_left, S_smul_left, S_smul_right, S_smul_right,
          S_symm hH z x] at h1
        simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, him z] at h1
        rw [Complex.normSq_apply]
        have h2 := mul_pos hz (neg_pos.2 h1)
        nlinarith [sq_nonneg ((S H z x).re - t.re * (S H z z).re), sq_nonneg ((S H z x).im - t.im * (S H z z).re),
          sq_nonneg (S H z x).re, sq_nonneg (S H z x).im])
  refine ⟨K, fun Y s hs hY ⟨c, hc⟩ => hK Y s hs.le fun x => ?_⟩
  have e1 := S_sim hY z z
  rw [hc, S_smul_left, S_smul_right, ← mul_assoc, ← Complex.normSq_eq_conj_mul_self] at e1
  have e2 : Complex.normSq c = s := by
    have := congrArg Complex.re e1
    simp only [Complex.re_ofReal_mul] at this
    exact mul_right_cancel₀ hz.ne' this
  have e3 := S_sim hY z x
  rw [hc, S_smul_left] at e3
  have e4 := congrArg Complex.normSq e3
  rw [map_mul, map_mul, Complex.normSq_conj, e2, Complex.normSq_ofReal, mul_assoc] at e4
  have e5 := mul_left_cancel₀ hs.ne' e4
  rw [S_sim hY, e5, Complex.re_ofReal_mul]
  ring

theorem exists_diag {h : Matrix (Fin n) (Fin n) ℂ} (hh : h.IsHermitian) (Z : Matrix (Fin n) (Fin n) ℂ)
    (hZ : IsUnit Z) : ∃ P : Matrix (Fin n) (Fin n) ℂ, (∀ x, P *ᵥ x = 0 → x = 0) ∧
      ∀ x, (S (Zᴴ * h * Z) x x).re = ∑ i, hh.eigenvalues i * ‖(P *ᵥ x) i‖ ^ 2 := by
  refine ⟨star (hh.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * Z, fun x hx => ?_, fun x => ?_⟩
  · have hU : IsUnit (star (hh.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * Z) :=
      (Unitary.isUnit_coe (U := hh.eigenvectorUnitary)).star.mul hZ
    exact (mulVec_injective_iff_isUnit.2 hU) (by rw [hx, mulVec_zero])
  · rw [← S_diag, ← S_conj]
    congr 2
    conv_lhs => rw [hh.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rw [conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose]
    simp only [mul_assoc]
    rfl

theorem eig_ne {h : Matrix (Fin n) (Fin n) ℂ} (hh : h.IsHermitian) (hd : h.det ≠ 0) (i : Fin n) :
    hh.eigenvalues i ≠ 0 := by
  rw [hh.det_eq_prod_eigenvalues, Finset.prod_ne_zero_iff] at hd
  simpa using hd i (Finset.mem_univ _)

theorem sum_neg (d : Fin n → ℝ) (x : Fin n → ℂ) (hx : x ≠ 0) (h : ∀ i, x i ≠ 0 → d i < 0) :
    ∑ i, d i * ‖x i‖ ^ 2 < 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hx
  have hj' : x j ≠ 0 := hj
  have : ∑ i, d i * ‖x i‖ ^ 2 < ∑ _i : Fin n, (0 : ℝ) := by
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
    · by_cases hi : x i = 0
      · simp [hi]
      · exact mul_nonpos_of_nonpos_of_nonneg (h i hi).le (sq_nonneg _)
    · exact mul_neg_of_neg_of_pos (h j hj') (by positivity)
  simpa using this

theorem neg_definite_of_signature_zero {h : Matrix (Fin n) (Fin n) ℂ} (hh : h.IsHermitian) (hd : h.det ≠ 0)
    (hs : sigPosH hh = 0) (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : IsUnit Z) (x : Fin n → ℂ) (hx : x ≠ 0) :
    (S (Zᴴ * h * Z) x x).re < 0 := by
  obtain ⟨P, hP, e⟩ := exists_diag hh Z hZ
  rw [e]
  refine sum_neg _ _ (fun h0 => hx (hP x h0)) fun i _ => ?_
  have := Fintype.card_eq_zero_iff.1 hs
  exact lt_of_le_of_ne (not_lt.1 fun hi => this.false ⟨i, hi⟩) (eig_ne hh hd i)

theorem neg_definite_hyperplane_of_signature_one {h : Matrix (Fin n) (Fin n) ℂ} (hh : h.IsHermitian) (hd : h.det ≠ 0)
    (hs : sigPosH hh = 1) (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : IsUnit Z) :
    ∃ l : Fin n → ℂ, ∀ x, x ≠ 0 → l ⬝ᵥ x = 0 → (S (Zᴴ * h * Z) x x).re < 0 := by
  obtain ⟨P, hP, e⟩ := exists_diag hh Z hZ
  obtain ⟨⟨i₀, hi₀⟩, hu⟩ := Fintype.card_eq_one_iff.1 hs
  refine ⟨P i₀, fun x hx hl => ?_⟩
  rw [e]
  refine sum_neg _ _ (fun h0 => hx (hP x h0)) fun i hi => ?_
  refine lt_of_le_of_ne (not_lt.1 fun hi' => hi ?_) (eig_ne hh hd i)
  have : i = i₀ := congrArg Subtype.val (hu ⟨i, hi'⟩)
  rw [this]
  exact hl

end Forms

section Algebra

variable {n : ℕ}

theorem rearr {h B B' Y C C' : Matrix (Fin n) (Fin n) ℂ} (hd : h.det ≠ 0) (hB : B * B' = 1) (hC : C * C' = 1)
    (s : ℂ) (hs : s ≠ 0) (e : Y * B * (h⁻¹ * Yᴴ * h) = s • C) :
    Yᴴ * (h * C') * Y = s • (h * B') := by
  have hu : IsUnit h.det := isUnit_iff_ne_zero.2 hd
  have h1 : h * h⁻¹ = 1 := mul_nonsing_inv h hu
  have e1 : Y * (s⁻¹ • (B * (h⁻¹ * Yᴴ * h) * C')) = 1 := by
    rw [Matrix.mul_smul, ← mul_assoc, ← mul_assoc, e, Matrix.smul_mul, hC, smul_smul, inv_mul_cancel₀ hs, one_smul]
  have e2 := mul_eq_one_comm.1 e1
  have hB' := mul_eq_one_comm.1 hB
  have e3 : B * (h⁻¹ * Yᴴ * h) * C' * Y = s • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← e2, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hs, one_smul]
  calc Yᴴ * (h * C') * Y = (h * h⁻¹) * Yᴴ * (h * C') * Y := by rw [h1, one_mul]
    _ = h * ((B' * B) * (h⁻¹ * Yᴴ * h) * C' * Y) := by rw [hB', one_mul]; simp only [mul_assoc]
    _ = h * B' * (B * (h⁻¹ * Yᴴ * h) * C' * Y) := by simp only [mul_assoc]
    _ = _ := by rw [e3, Matrix.mul_smul, mul_one]

end Algebra

variable {p : ℕ} [Fact p.Prime]

theorem psiR_tmul (G : HTGroup p) (w : InfinitePlace G.F) (r : ℝ) (x : G.C) :
    G.psiR w (r ⊗ₜ x) = (r : ℂ) • G.psi w x := by
  change algebraMap ℝ _ r * G.psi w x = _
  rw [← Algebra.smul_def]
  ext i j
  simp

theorem psiR_star (G : HTGroup p) (w : InfinitePlace G.F) (x : ℝ ⊗[ℚ] G.C) :
    G.psiR w (starT G.star ℝ x).unop = (G.gram w)⁻¹ * (G.psiR w x)ᴴ * G.gram w := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    rw [starT_tmul, psiR_tmul, psiR_tmul, G.psi_star, conjTranspose_smul]
    simp
  | add x y hx hy =>
    simp only [map_add, MulOpposite.unop_add, hx, hy, conjTranspose_add, mul_add, add_mul]

theorem herm_eq (G : HTGroup p) (w : InfinitePlace G.F) (β : G.Cˣ) (z : (ℝ ⊗[ℚ] G.C)ˣ) (hz : Triv G ℝ β z 1) :
    herm G w β = (G.psiR w z)ᴴ * G.gram w * G.psiR w z := by
  have h := congrArg (G.psiR w) hz
  have e : G.psiR w (inC G ℝ β) = G.psi w β := by
    change G.psiR w ((1 : ℝ) ⊗ₜ (β : G.C)) = _
    rw [psiR_tmul]; simp
  rw [map_mul, map_mul, psiR_star, e, Units.val_one, map_one, map_one, ← one_smul ℂ (1 : Matrix _ _ ℂ)] at h
  have := rearr (B' := G.psi w ((β⁻¹ : G.Cˣ) : G.C)) (G.gram_det w)
    (by rw [← map_mul, Units.mul_inv, map_one]) (mul_one 1) 1 one_ne_zero h
  rw [mul_one, one_smul] at this
  exact this.symm

theorem sim_eq (G : HTGroup p) (w : InfinitePlace G.F) (β : G.Cˣ) (y : grp G β) :
    (G.psi w (y.1.1 : G.C))ᴴ * herm G w β * G.psi w (y.1.1 : G.C) = ((((y.1.2 : ℚ) : ℝ)) : ℂ) • herm G w β := by
  have h := congrArg (G.psi w) y.2.1
  have e : G.psi w (algebraMap ℚ G.C (y.1.2 : ℚ) * β) = ((((y.1.2 : ℚ) : ℝ)) : ℂ) • G.psi w β := by
    rw [← Algebra.smul_def, map_rat_smul]
    ext i j
    simp [Rat.smul_def]
  rw [e, map_mul, map_mul, sh, G.psi_star] at h
  have hb : G.psi w β * G.psi w ((β⁻¹ : G.Cˣ) : G.C) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  exact rearr (G.gram_det w) hb hb _ (by exact_mod_cast y.1.2.ne_zero) h

theorem main (p : ℕ) [Fact p.Prime] (G : HTGroup p) (hG : IsSimple G) (v : InfinitePlace G.F)
    (hv : sigPosH (G.gram_herm v) = 1) (β : G.Cˣ) (_hβ : sh G (β : G.C) = β)
    (hT : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ (β : G.C) z 1) (z : Fin G.n → ℂ)
    (hz : 0 < (star z ⬝ᵥ herm G v β *ᵥ z).re) :
    ∃ K : ℝ, ∀ y : grp G β, FixL G v β y z → ∀ (w : InfinitePlace G.F) (a b : Fin G.n),
      ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b‖ ≤ K * √((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by
  obtain ⟨x, hx⟩ := hT
  have hpos : ∀ y : grp G β, (0 : ℝ) < ((y.1.2 : ℚ) : ℝ) := fun y => by exact_mod_cast y.2.2
  have hZ : ∀ w, IsUnit (G.psiR w x) := fun w => x.isUnit.map _
  have key : ∀ w : InfinitePlace G.F, ∃ K : ℝ, ∀ y : grp G β, FixL G v β y z → ∀ a b : Fin G.n,
      ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b‖ ≤ K * √((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by
    intro w
    rcases G.sig w with ⟨h1, -⟩ | ⟨h0, -⟩
    · obtain ⟨v₀, hu⟩ := Fintype.card_eq_one_iff.1 hG.2
      have hwv : w = v := congrArg Subtype.val ((hu ⟨w, h1⟩).trans (hu ⟨v, hv⟩).symm)
      subst hwv
      obtain ⟨l, hl⟩ := neg_definite_hyperplane_of_signature_one (G.gram_herm w) (G.gram_det w) h1 _ (hZ w)
      rw [← herm_eq G w β x hx] at hl
      have hH : (herm G w β).IsHermitian := by
        rw [herm_eq G w β x hx]
        exact isHermitian_conjTranspose_mul_mul _ (G.gram_herm w)
      obtain ⟨K, hK⟩ := bound_hyp _ hH l hl z hz
      exact ⟨K, fun y hy => hK _ _ (hpos y) (sim_eq G w β y) hy⟩
    · have hl := neg_definite_of_signature_zero (G.gram_herm w) (G.gram_det w) h0 _ (hZ w)
      rw [← herm_eq G w β x hx] at hl
      obtain ⟨K, hK⟩ := bound_neg _ hl
      exact ⟨K, fun y _ => hK _ _ (hpos y).le (sim_eq G w β y)⟩
  choose K hK using key
  obtain ⟨M, hM⟩ := (Set.finite_range K).bddAbove
  exact ⟨M, fun y hy w a b => (hK w y hy a b).trans
    (mul_le_mul_of_nonneg_right (hM ⟨w, rfl⟩) (Real.sqrt_nonneg _))⟩

end GlobalTheory.HermitianSignatureForms
