import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.HermProjRight

open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace PI.PolynomialProperness

namespace CoreW

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem herm_expand (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (c : ℝ) (a b : Fin n → ℂ) :
    herm H ((c : ℂ) • a - b) ((c : ℂ) • a - b) =
      (c : ℂ) * ((c : ℂ) * herm H a a) - (c : ℂ) * herm H a b - ((c : ℂ) * herm H b a - herm H b b) := by
  simp only [herm, Matrix.mulVec_sub, Matrix.mulVec_smul, star_sub, star_smul, dotProduct_sub,
    sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul, Complex.star_def,
    Complex.conj_ofReal]
  ring

theorem key_ineq (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (c : ℝ) (hc : 0 < c)
    (v y : Fin n → ℂ) (hvy : herm H v y = ((nsq v : ℝ) : ℂ)) (hyv : herm H y v = ((nsq v : ℝ) : ℂ))
    (hyy : (herm H y y).re ≤ c * nsq v) (hpos : 0 ≤ (herm H ((c : ℂ) • v - y) ((c : ℂ) • v - y)).re) :
    nsq v ≤ c * (herm H v v).re := by
  rw [herm_expand H hH c v y, hvy, hyv] at hpos
  simp only [Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re] at hpos
  nlinarith

theorem iso_right_inv (H s : Matrix (Fin n) (Fin n) ℂ) (hHH : H * H = 1) (hs : sᴴ * H * s = H) :
    s * (H * sᴴ * H) = 1 := by
  have h : H * sᴴ * H * s = 1 := by
    rw [mul_assoc, mul_assoc, ← mul_assoc sᴴ, hs, hHH]
  rw [← Matrix.inv_eq_left_inv h]
  exact Matrix.mul_nonsing_inv s (Matrix.isUnit_det_of_left_inverse h)

theorem psd_image (H s : Matrix (Fin n) (Fin n) ℂ) (hHH : H * H = 1) (hs : sᴴ * H * s = H)
    (m : ι → Fin n → ℂ) (hpsd : ∀ x, (∀ i, herm H x (m i) = 0) → 0 ≤ (herm H x x).re)
    (w : Fin n → ℂ) (hw : ∀ i, herm H w (s *ᵥ m i) = 0) : 0 ≤ (herm H w w).re := by
  have hsx : s *ᵥ ((H * sᴴ * H) *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, iso_right_inv H s hHH hs, Matrix.one_mulVec]
  have h1 : ∀ i, herm H ((H * sᴴ * H) *ᵥ w) (m i) = 0 := fun i => by
    rw [← herm_iso H s hs, hsx]
    exact hw i
  have h2 := hpsd _ h1
  rwa [← herm_iso H s hs, hsx] at h2

theorem gram_image (H s : Matrix (Fin n) (Fin n) ℂ) (hs : sᴴ * H * s = H) (m : ι → Fin n → ℂ) :
    gramOf H (fun i => s *ᵥ m i) = gramOf H m := by
  ext i j
  simp only [gramOf, Matrix.of_apply]
  exact herm_iso H s hs (m j) (m i)

theorem orth_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1)
    (Γi : Matrix ι ι ℂ) (q : ι → Fin n → ℂ) (hG : gramOf H q * Γi = 1) (R : ℝ) (hR : 0 ≤ R)
    (hq : ∀ k, eN (q k) ≤ R) (hpsd : ∀ w, (∀ i, herm H w (q i) = 0) → 0 ≤ (herm H w w).re)
    (v : Fin n → ℂ) (hv : ∀ j, herm H v (q j) = 0) :
    nsq v ≤ (1 + (Fintype.card ι : ℝ) * (∑ j, ∑ k, ‖Γi j k‖) * (R * R)) * (herm H v v).re := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ j, ∑ k, ‖Γi j k‖ := ⟨_, rfl⟩
  rw [← hA]
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => norm_nonneg _
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 1 + (Fintype.card ι : ℝ) * A * (R * R) := ⟨_, rfl⟩
  rw [← hcdef]
  have hc : 0 < c := by
    have := mul_nonneg (mul_nonneg (Nat.cast_nonneg (Fintype.card ι)) hA0) (mul_self_nonneg R)
    rw [hcdef]
    linarith
  obtain ⟨y, hy⟩ : ∃ y, y = H *ᵥ v := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y', y' = y - proj H Γi q y := ⟨_, rfl⟩
  have hy'q : ∀ j, herm H y' (q j) = 0 := fun j => by
    rw [hy']
    exact proj_orth H Γi q hG y j
  have hvy : herm H v y' = ((nsq v : ℝ) : ℂ) := by
    rw [hy', herm_sub_right H hH, herm_proj_right H hH Γi q y v hv, sub_zero, hy,
      herm_H_self H hH hHH]
  have hyv : herm H y' v = ((nsq v : ℝ) : ℂ) := by
    rw [← herm_conj H hH, hvy, Complex.conj_ofReal]
  have e1 : herm H y' (y - proj H Γi q y) = herm H y' y := by
    rw [herm_sub_right H hH, herm_proj_right H hH Γi q y y' hy'q, sub_zero]
  rw [← hy'] at e1
  have hey : eN y = eN v := by
    rw [hy]
    exact eN_H H hH hHH v
  have hpb := proj_bound H hH hHH Γi q R hR hq y
  rw [← hA, hey] at hpb
  have hey' : eN y' ≤ eN v * c := by
    calc eN y' ≤ eN y + eN (proj H Γi q y) := by
          rw [hy']
          exact eN_sub _ _
      _ ≤ eN v + (Fintype.card ι : ℝ) * (A * (eN v * R)) * R := by
          rw [hey]
          linarith
      _ = eN v * c := by
          rw [hcdef]
          ring
  have hyy : (herm H y' y').re ≤ c * nsq v := by
    calc (herm H y' y').re ≤ ‖herm H y' y'‖ := Complex.re_le_norm _
      _ = ‖herm H y' y‖ := by rw [e1]
      _ ≤ eN y' * eN y := herm_le H hH hHH y' y
      _ ≤ (eN v * c) * eN v := by
          rw [hey]
          exact mul_le_mul_of_nonneg_right hey' (eN_nonneg _)
      _ = c * nsq v := by
          rw [← eN_sq]
          ring
  have hpos : 0 ≤ (herm H ((c : ℂ) • v - y') ((c : ℂ) • v - y')).re := by
    apply hpsd
    intro i
    rw [herm_sub_left H, herm_smul_left H, hv i, hy'q i, mul_zero, sub_zero]
  exact key_ineq H hH c hc v y' hvy hyv hyy hpos

theorem final_alg (D R0 E K c X a b : ℝ) (hD0 : 0 ≤ D) (hK : 0 ≤ K) (hX : 0 ≤ X)
    (hc : c = 1 + D * K) (ha : a ≤ D ^ 2 * R0 ^ 2 * K * X) (hb : b ≤ c * (E ^ 2 * X)) :
    2 * a + 2 * b ≤ (2 * D ^ 2 * R0 ^ 2 + 2 * (1 + D) * E ^ 2) * (1 + K) ^ 2 * X := by
  subst hc
  have h1 : D ^ 2 * R0 ^ 2 * K * X ≤ D ^ 2 * R0 ^ 2 * (1 + K) ^ 2 * X := by
    have hk : K ≤ (1 + K) ^ 2 := by nlinarith
    have hp : 0 ≤ D ^ 2 * R0 ^ 2 * X := mul_nonneg (mul_nonneg (sq_nonneg D) (sq_nonneg R0)) hX
    nlinarith
  have h2 : (1 + D * K) * (E ^ 2 * X) ≤ (1 + D) * E ^ 2 * (1 + K) ^ 2 * X := by
    have hk : 1 + D * K ≤ (1 + D) * (1 + K) ^ 2 := by
      nlinarith [mul_nonneg hD0 hK, sq_nonneg K, mul_nonneg hD0 (sq_nonneg K)]
    have hp : 0 ≤ E ^ 2 * X := mul_nonneg (sq_nonneg E) hX
    nlinarith
  nlinarith

end CoreW

open CoreW

theorem isoCore : IsoCore := by
  intro n H ι _ _ m hH hHH hdet hpsd
  obtain ⟨Γi, hΓi⟩ : ∃ Γi, Γi = (gramOf H m)⁻¹ := ⟨_, rfl⟩
  have hG : gramOf H m * Γi = 1 := by
    rw [hΓi]
    exact Matrix.mul_nonsing_inv _ hdet
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ j, ∑ k, ‖Γi j k‖ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => norm_nonneg _
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (Fintype.card ι : ℝ) * A := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by
    rw [hD]
    exact mul_nonneg (Nat.cast_nonneg _) hA0
  have hAD : A ≤ D := by
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | h0
    · haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp h0
      have hA' : A = 0 := by
        rw [hA]
        simp
      rw [hA']
      exact hD0
    · have h1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast h0
      rw [hD]
      nlinarith
  obtain ⟨R0, hR0⟩ : ∃ R0 : ℝ, R0 = ∑ k, eN (m k) := ⟨_, rfl⟩
  have hR00 : 0 ≤ R0 := by
    rw [hR0]
    exact Finset.sum_nonneg fun k _ => eN_nonneg _
  have hmR : ∀ k, eN (m k) ≤ R0 := fun k => by
    rw [hR0]
    exact Finset.single_le_sum (f := fun k => eN (m k)) (fun k _ => eN_nonneg _) (Finset.mem_univ k)
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = 1 + (Fintype.card ι : ℝ) * A * (R0 * R0) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by
    have := mul_nonneg (mul_nonneg (Nat.cast_nonneg (Fintype.card ι)) hA0) (mul_self_nonneg R0)
    rw [hE]
    linarith
  refine ⟨2 * D ^ 2 * R0 ^ 2 + 2 * (1 + D) * E ^ 2, fun s hs K hK hsm x => ?_⟩
  obtain ⟨p, hp⟩ : ∃ p, p = proj H Γi m x := ⟨_, rfl⟩
  obtain ⟨xo, hxo⟩ : ∃ xo, xo = x - p := ⟨_, rfl⟩
  have hxo_orth : ∀ j, herm H xo (m j) = 0 := fun j => by
    rw [hxo, hp]
    exact proj_orth H Γi m hG x j
  have hsx : s *ᵥ x = s *ᵥ p + s *ᵥ xo := by
    rw [hxo, Matrix.mulVec_sub]
    abel
  have hX : 0 ≤ nsq x := by
    rw [← eN_sq]
    positivity

  have hcoef : ∑ i, ‖coef H Γi m x i‖ ≤ A * (eN x * R0) := by
    calc ∑ i, ‖coef H Γi m x i‖ ≤ ∑ i, ∑ k, ‖Γi i k‖ * (eN x * R0) :=
          Finset.sum_le_sum fun i _ => by
            show ‖∑ k, Γi i k * herm H x (m k)‖ ≤ _
            calc ‖∑ k, Γi i k * herm H x (m k)‖ ≤ ∑ k, ‖Γi i k * herm H x (m k)‖ :=
                  norm_sum_le _ _
              _ ≤ ∑ k, ‖Γi i k‖ * (eN x * R0) := Finset.sum_le_sum fun k _ => by
                  rw [norm_mul]
                  exact mul_le_mul_of_nonneg_left ((herm_le H hH hHH x (m k)).trans
                    (mul_le_mul_of_nonneg_left (hmR k) (eN_nonneg x))) (norm_nonneg _)
      _ = A * (eN x * R0) := by
          rw [hA, Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
  have hsK : ∀ k, eN (s *ᵥ m k) ≤ Real.sqrt K := fun k =>
    (le_abs_self _).trans (Real.abs_le_sqrt (by rw [eN_sq]; exact hsm k))
  have hsp : eN (s *ᵥ p) ≤ A * (eN x * R0) * Real.sqrt K := by
    have e : s *ᵥ p = ∑ i, coef H Γi m x i • (s *ᵥ m i) := by
      rw [hp, proj, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul]
    rw [e]
    calc eN (∑ i, coef H Γi m x i • (s *ᵥ m i)) ≤ ∑ i, eN (coef H Γi m x i • (s *ᵥ m i)) :=
          eN_sum _ _
      _ ≤ ∑ i, ‖coef H Γi m x i‖ * Real.sqrt K := Finset.sum_le_sum fun i _ => by
          rw [eN_smul]
          exact mul_le_mul_of_nonneg_left (hsK i) (norm_nonneg _)
      _ = (∑ i, ‖coef H Γi m x i‖) * Real.sqrt K := (Finset.sum_mul _ _ _).symm
      _ ≤ A * (eN x * R0) * Real.sqrt K := mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)
  have ha : nsq (s *ᵥ p) ≤ D ^ 2 * R0 ^ 2 * K * nsq x := by
    rw [← eN_sq, ← eN_sq x]
    have h1 : eN (s *ᵥ p) ^ 2 ≤ (A * (eN x * R0) * Real.sqrt K) ^ 2 :=
      pow_le_pow_left₀ (eN_nonneg _) hsp 2
    have h2 : (A * (eN x * R0) * Real.sqrt K) ^ 2 = A ^ 2 * R0 ^ 2 * K * eN x ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hK]
      ring
    have h3 : A ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hA0 hAD 2
    have h4 : 0 ≤ R0 ^ 2 * K * eN x ^ 2 := mul_nonneg (mul_nonneg (sq_nonneg _) hK) (sq_nonneg _)
    nlinarith

  have hGs : gramOf H (fun i => s *ᵥ m i) * Γi = 1 := by
    rw [gram_image H s hs m]
    exact hG
  have hpsd' : ∀ w, (∀ i, herm H w ((fun i => s *ᵥ m i) i) = 0) → 0 ≤ (herm H w w).re :=
    fun w hw => psd_image H s hHH hs m hpsd w hw
  have hv : ∀ j, herm H (s *ᵥ xo) ((fun i => s *ᵥ m i) j) = 0 := fun j => by
    show herm H (s *ᵥ xo) (s *ᵥ m j) = 0
    rw [herm_iso H s hs]
    exact hxo_orth j
  have hob := orth_bound H hH hHH Γi (fun i => s *ᵥ m i) hGs (Real.sqrt K) (Real.sqrt_nonneg _)
    hsK hpsd' (s *ᵥ xo) hv
  rw [Real.mul_self_sqrt hK, herm_iso H s hs, ← hA, ← hD] at hob
  have hpb := proj_bound H hH hHH Γi m R0 hR00 hmR x
  rw [← hA, ← hp] at hpb
  have hxoN : eN xo ≤ E * eN x := by
    calc eN xo ≤ eN x + eN p := by
          rw [hxo]
          exact eN_sub _ _
      _ ≤ eN x + (Fintype.card ι : ℝ) * (A * (eN x * R0)) * R0 := by linarith
      _ = E * eN x := by
          rw [hE]
          ring
  have hre : (herm H xo xo).re ≤ E ^ 2 * nsq x := by
    calc (herm H xo xo).re ≤ ‖herm H xo xo‖ := Complex.re_le_norm _
      _ ≤ eN xo * eN xo := herm_le H hH hHH xo xo
      _ ≤ (E * eN x) * (E * eN x) :=
          mul_le_mul hxoN hxoN (eN_nonneg _) (mul_nonneg hE0 (eN_nonneg _))
      _ = E ^ 2 * nsq x := by
          rw [← eN_sq x]
          ring
  have hb : nsq (s *ᵥ xo) ≤ (1 + D * K) * (E ^ 2 * nsq x) := by
    have hc0 : 0 ≤ 1 + D * K := by
      have := mul_nonneg hD0 hK
      linarith
    exact hob.trans (mul_le_mul_of_nonneg_left hre hc0)
  have hsum : nsq (s *ᵥ x) ≤ 2 * nsq (s *ᵥ p) + 2 * nsq (s *ᵥ xo) := by
    rw [hsx, ← eN_sq, ← eN_sq (s *ᵥ p), ← eN_sq (s *ᵥ xo)]
    have h1 := eN_add (s *ᵥ p) (s *ᵥ xo)
    have h2 := eN_nonneg (s *ᵥ p + s *ᵥ xo)
    nlinarith [sq_nonneg (eN (s *ᵥ p) - eN (s *ᵥ xo)), eN_nonneg (s *ᵥ p), eN_nonneg (s *ᵥ xo)]
  have hfin := final_alg D R0 E K (1 + D * K) (nsq x) (nsq (s *ᵥ p)) (nsq (s *ᵥ xo)) hD0 hK hX
    rfl ha hb
  linarith

end PI.PolynomialProperness
