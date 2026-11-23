import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.UnitriangularInversePolynomialBound

open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace PI.PolynomialProperness.CoreW

def eN {n : ℕ} (x : Fin n → ℂ) : ℝ := ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))‖

theorem eN_nonneg {n : ℕ} (x : Fin n → ℂ) : 0 ≤ eN x := norm_nonneg _

theorem eN_add {n : ℕ} (x y : Fin n → ℂ) : eN (x + y) ≤ eN x + eN y := by
  simp only [eN, WithLp.toLp_add]
  exact norm_add_le _ _

theorem eN_sub {n : ℕ} (x y : Fin n → ℂ) : eN (x - y) ≤ eN x + eN y := by
  simp only [eN, WithLp.toLp_sub]
  exact norm_sub_le _ _

theorem eN_smul {n : ℕ} (c : ℂ) (x : Fin n → ℂ) : eN (c • x) = ‖c‖ * eN x := by
  simp only [eN, WithLp.toLp_smul]
  exact norm_smul _ _

theorem eN_sum {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → Fin n → ℂ) :
    eN (∑ i ∈ s, f i) ≤ ∑ i ∈ s, eN (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eN]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (eN_add _ _).trans (add_le_add le_rfl ih)

theorem eN_sq {n : ℕ} (x : Fin n → ℂ) : eN x ^ 2 = nsq x := by
  rw [eN, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  simp [nsq, Complex.sq_norm]

theorem dot_le {n : ℕ} (w v : Fin n → ℂ) : ‖star w ⬝ᵥ v‖ ≤ eN w * eN v := by
  have e : star w ⬝ᵥ v =
      inner ℂ (WithLp.toLp 2 w : EuclideanSpace ℂ (Fin n)) (WithLp.toLp 2 v) := by
    simp [PiLp.inner_apply, dotProduct, RCLike.inner_apply, mul_comm]
  rw [e]
  exact norm_inner_le_norm _ _

theorem nsq_ofReal {n : ℕ} (x : Fin n → ℂ) : ((nsq x : ℝ) : ℂ) = star x ⬝ᵥ x := by
  simp [nsq, dotProduct, Complex.normSq_eq_conj_mul_self]

section form

variable {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)

theorem star_H_dot (hH : Hᴴ = H) (hHH : H * H = 1) (v : Fin n → ℂ) :
    star (H *ᵥ v) ⬝ᵥ (H *ᵥ v) = star v ⬝ᵥ v := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hH, hHH,
    Matrix.one_mulVec]

theorem nsq_H (hH : Hᴴ = H) (hHH : H * H = 1) (v : Fin n → ℂ) : nsq (H *ᵥ v) = nsq v := by
  have h : ((nsq (H *ᵥ v) : ℝ) : ℂ) = ((nsq v : ℝ) : ℂ) := by
    rw [nsq_ofReal, nsq_ofReal, star_H_dot H hH hHH v]
  exact_mod_cast h

theorem eN_H (hH : Hᴴ = H) (hHH : H * H = 1) (v : Fin n → ℂ) : eN (H *ᵥ v) = eN v := by
  have h : eN (H *ᵥ v) ^ 2 = eN v ^ 2 := by rw [eN_sq, eN_sq, nsq_H H hH hHH]
  exact (pow_left_inj₀ (eN_nonneg _) (eN_nonneg _) two_ne_zero).mp h

theorem herm_le (hH : Hᴴ = H) (hHH : H * H = 1) (v w : Fin n → ℂ) :
    ‖herm H v w‖ ≤ eN v * eN w := by
  unfold herm
  calc ‖star w ⬝ᵥ (H *ᵥ v)‖ ≤ eN w * eN (H *ᵥ v) := dot_le _ _
    _ = eN v * eN w := by rw [eN_H H hH hHH, mul_comm]

theorem herm_H_self (hH : Hᴴ = H) (hHH : H * H = 1) (v : Fin n → ℂ) :
    herm H v (H *ᵥ v) = ((nsq v : ℝ) : ℂ) := by
  unfold herm
  rw [star_H_dot H hH hHH, nsq_ofReal]

theorem herm_iso (s : Matrix (Fin n) (Fin n) ℂ) (hs : sᴴ * H * s = H) (v w : Fin n → ℂ) :
    herm H (s *ᵥ v) (s *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hs]

theorem herm_conj (hH : Hᴴ = H) (v w : Fin n → ℂ) : conj (herm H v w) = herm H w v := by
  unfold herm
  rw [← Complex.star_def, Matrix.star_dotProduct, star_star, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, hH]

theorem herm_sub_left (v v' w : Fin n → ℂ) : herm H (v - v') w = herm H v w - herm H v' w := by
  simp [herm, Matrix.mulVec_sub, dotProduct_sub]

theorem herm_smul_left (c : ℂ) (v w : Fin n → ℂ) : herm H (c • v) w = c * herm H v w := by
  simp [herm, Matrix.mulVec_smul, dotProduct_smul]

theorem herm_sum_left {ι : Type} [Fintype ι] (f : ι → Fin n → ℂ) (w : Fin n → ℂ) :
    herm H (∑ i, f i) w = ∑ i, herm H (f i) w := by
  simp [herm, Matrix.mulVec_sum, dotProduct_sum]

theorem herm_sub_right (hH : Hᴴ = H) (v w w' : Fin n → ℂ) :
    herm H v (w - w') = herm H v w - herm H v w' := by
  simp [herm, star_sub, sub_dotProduct]

theorem herm_smul_right (hH : Hᴴ = H) (c : ℂ) (v w : Fin n → ℂ) :
    herm H v (c • w) = conj c * herm H v w := by
  simp [herm, star_smul, smul_dotProduct]

theorem herm_sum_right (hH : Hᴴ = H) {ι : Type} [Fintype ι] (f : ι → Fin n → ℂ) (v : Fin n → ℂ) :
    herm H v (∑ i, f i) = ∑ i, herm H v (f i) := by
  simp [herm, star_sum, sum_dotProduct]

end form

section proj

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

def coef (H : Matrix (Fin n) (Fin n) ℂ) (Γi : Matrix ι ι ℂ) (p : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    ι → ℂ :=
  Γi *ᵥ fun k => herm H y (p k)

def proj (H : Matrix (Fin n) (Fin n) ℂ) (Γi : Matrix ι ι ℂ) (p : ι → Fin n → ℂ) (y : Fin n → ℂ) :
    Fin n → ℂ :=
  ∑ i, coef H Γi p y i • p i

theorem herm_proj_left (H : Matrix (Fin n) (Fin n) ℂ) (Γi : Matrix ι ι ℂ) (p : ι → Fin n → ℂ)
    (hG : gramOf H p * Γi = 1) (y : Fin n → ℂ) (j : ι) :
    herm H (proj H Γi p y) (p j) = herm H y (p j) := by
  unfold proj
  rw [herm_sum_left]
  simp only [herm_smul_left]
  have e : (∑ i, coef H Γi p y i * herm H (p i) (p j)) = (gramOf H p *ᵥ coef H Γi p y) j := by
    simp only [Matrix.mulVec, dotProduct, gramOf, Matrix.of_apply]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [e, coef, Matrix.mulVec_mulVec, hG, Matrix.one_mulVec]

theorem proj_orth (H : Matrix (Fin n) (Fin n) ℂ) (Γi : Matrix ι ι ℂ) (p : ι → Fin n → ℂ)
    (hG : gramOf H p * Γi = 1) (y : Fin n → ℂ) (j : ι) :
    herm H (y - proj H Γi p y) (p j) = 0 := by
  rw [herm_sub_left, herm_proj_left H Γi p hG y j, sub_self]

theorem herm_proj_right (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (Γi : Matrix ι ι ℂ)
    (p : ι → Fin n → ℂ) (y x : Fin n → ℂ) (hx : ∀ j, herm H x (p j) = 0) :
    herm H x (proj H Γi p y) = 0 := by
  unfold proj
  rw [herm_sum_right H hH]
  simp [herm_smul_right H hH, hx]

theorem lincomb_bound (c : ι → ℂ) (q : ι → Fin n → ℂ) (a R : ℝ) (_hR : 0 ≤ R)
    (hc : ∀ i, ‖c i‖ ≤ a) (hq : ∀ i, eN (q i) ≤ R) :
    eN (∑ i, c i • q i) ≤ (Fintype.card ι : ℝ) * a * R := by
  calc eN (∑ i, c i • q i) ≤ ∑ i, eN (c i • q i) := eN_sum _ _
    _ = ∑ i, ‖c i‖ * eN (q i) := by simp only [eN_smul]
    _ ≤ ∑ _i : ι, a * R := Finset.sum_le_sum (fun i _ =>
        mul_le_mul (hc i) (hq i) (eN_nonneg _) ((norm_nonneg _).trans (hc i)))
    _ = (Fintype.card ι : ℝ) * a * R := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

theorem coef_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1)
    (Γi : Matrix ι ι ℂ) (p : ι → Fin n → ℂ) (R : ℝ) (hp : ∀ k, eN (p k) ≤ R)
    (y : Fin n → ℂ) (i : ι) :
    ‖coef H Γi p y i‖ ≤ (∑ j, ∑ k, ‖Γi j k‖) * (eN y * R) := by
  have hb : ∀ k, ‖herm H y (p k)‖ ≤ eN y * R := fun k =>
    (herm_le H hH hHH y (p k)).trans (mul_le_mul_of_nonneg_left (hp k) (eN_nonneg _))
  unfold coef
  simp only [Matrix.mulVec, dotProduct]
  calc ‖∑ k, Γi i k * herm H y (p k)‖ ≤ ∑ k, ‖Γi i k * herm H y (p k)‖ := norm_sum_le _ _
    _ ≤ ∑ k, ‖Γi i k‖ * (eN y * R) := Finset.sum_le_sum (fun k _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hb k) (norm_nonneg _))
    _ = (∑ k, ‖Γi i k‖) * (eN y * R) := by rw [Finset.sum_mul]
    _ ≤ (∑ j, ∑ k, ‖Γi j k‖) * (eN y * R) := by
        apply mul_le_mul_of_nonneg_right _ ((norm_nonneg _).trans (hb i))
        exact Finset.single_le_sum (f := fun j => ∑ k, ‖Γi j k‖)
          (fun j _ => Finset.sum_nonneg (fun k _ => norm_nonneg _)) (Finset.mem_univ i)

theorem proj_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1)
    (Γi : Matrix ι ι ℂ) (p : ι → Fin n → ℂ) (R : ℝ) (hR : 0 ≤ R) (hp : ∀ k, eN (p k) ≤ R)
    (y : Fin n → ℂ) :
    eN (proj H Γi p y) ≤
      (Fintype.card ι : ℝ) * ((∑ j, ∑ k, ‖Γi j k‖) * (eN y * R)) * R :=
  lincomb_bound _ _ _ R hR (fun i => coef_bound H hH hHH Γi p R hp y i) hp

end proj

end PI.PolynomialProperness.CoreW
