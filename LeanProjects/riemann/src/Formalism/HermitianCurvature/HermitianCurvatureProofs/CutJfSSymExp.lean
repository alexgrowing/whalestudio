import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSSymDefs

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

lemma expS_summable {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Summable (fun m : ℕ => ((m.factorial : ℂ))⁻¹ • X ^ m) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  exact NormedSpace.expSeries_summable' X

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def mvL {n : ℕ} (y : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] (Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ y
      map_add' := fun M N => Matrix.add_mulVec M N y
      map_smul' := fun c M => Matrix.smul_mulVec c M y }

lemma mvL_apply {n : ℕ} (y : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) : mvL y M = M *ᵥ y := rfl

lemma exp_mulVec_sq {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) (h : X *ᵥ (X *ᵥ y) = 0) :
    NormedSpace.exp X *ᵥ y = y + X *ᵥ y := by
  have hs := expS_summable X
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  show (∑' m : ℕ, ((m.factorial : ℂ))⁻¹ • X ^ m) *ᵥ y = y + X *ᵥ y
  rw [← mvL_apply y, ContinuousLinearMap.map_tsum (mvL y) hs]
  rw [tsum_eq_sum (s := Finset.range 2) ?_]
  · simp [Finset.sum_range_succ, mvL_apply, Matrix.smul_mulVec]
  · intro m hm
    simp only [Finset.mem_range, not_lt] at hm
    rw [mvL_apply, Matrix.smul_mulVec]
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
    rw [pow_add, ← Matrix.mulVec_mulVec, pow_two, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero, smul_zero]

lemma exp_smul_mulVec_sq {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) (h : X *ᵥ (X *ᵥ y) = 0)
    (c : ℂ) : NormedSpace.exp (c • X) *ᵥ y = y + c • (X *ᵥ y) := by
  have h' : (c • X) *ᵥ ((c • X) *ᵥ y) = 0 := by
    rw [Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul, h, smul_zero, smul_zero]
  rw [exp_mulVec_sq (c • X) y h', Matrix.smul_mulVec]

lemma exp_smul_mulVec_fix {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) (h : X *ᵥ y = 0)
    (c : ℂ) : NormedSpace.exp (c • X) *ᵥ y = y := by
  have h2 : X *ᵥ (X *ᵥ y) = 0 := by rw [h, Matrix.mulVec_zero]
  rw [exp_smul_mulVec_sq X y h2 c, h, smul_zero, add_zero]

variable {k r : ℕ}

lemma hpk_star (i j : Fin (2 * r + k + 1)) : star (Hpk k r i j) = Hpk k r i j := by
  unfold Hpk
  split_ifs <;> simp

lemma hpk_symm (i j : Fin (2 * r + k + 1)) : Hpk k r i j = Hpk k r j i := by
  by_cases hij : i = j
  · subst hij
    rfl
  · have hji : ¬ j = i := fun h => hij h.symm
    unfold Hpk
    simp only [hij, hji, and_false, if_false]
    split_ifs <;> first | rfl | (exfalso; omega)

lemma herm_conj (y w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) y w = star (herm (Hpk k r) w y) := by
  simp only [herm, dotProduct, mulVec, star_sum, star_mul', star_star, Pi.star_apply, hpk_star,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hpk_symm j i]
  ring

lemma vmv_mulVec {n : ℕ} (u w y : Fin n → ℂ) : vecMulVec u w *ᵥ y = (w ⬝ᵥ y) • u := by
  ext i
  simp only [vecMulVec, mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma star_hpk_dot (v y : Fin (2 * r + k + 1) → ℂ) : star (Hpk k r *ᵥ v) ⬝ᵥ y = herm (Hpk k r) y v := by
  simp only [herm, dotProduct, mulVec, star_sum, star_mul', Pi.star_apply, hpk_star, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hpk_symm j i]
  ring

theorem xuv_mulVec (u v y : Fin (2 * r + k + 1) → ℂ) :
    Xuv k r u v *ᵥ y = herm (Hpk k r) y v • u - herm (Hpk k r) y u • v := by
  unfold Xuv
  rw [Matrix.sub_mulVec, vmv_mulVec, vmv_mulVec, star_hpk_dot, star_hpk_dot]

theorem xuv_inLie (u v : Fin (2 * r + k + 1) → ℂ) : B.inLie k r (Xuv k r u v) := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
  have e1 : star (Hpk k r *ᵥ u) = star u ᵥ* Hpk k r := by rw [Matrix.star_mulVec, hH]
  have e2 : star (Hpk k r *ᵥ v) = star v ᵥ* Hpk k r := by rw [Matrix.star_mulVec, hH]
  unfold B.inLie Xuv
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_vecMulVec, Matrix.conjTranspose_vecMulVec,
    star_star, star_star, Matrix.sub_mul, Matrix.mul_sub, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul,
    Matrix.mul_vecMulVec, Matrix.mul_vecMulVec, e1, e2]
  abel

lemma mat_eq_mulVec_bvec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : M i j = (M *ᵥ bvec j) i := by
  simp [bvec, Matrix.mulVec_single]

lemma herm_bvec_left (p : Fin (2 * r + k + 1)) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (bvec p) w = ∑ i, star (w i) * Hpk k r i p := by
  simp [herm, bvec, dotProduct, Matrix.mulVec_single]

lemma herm_bvec_bvec (p q : Fin (2 * r + k + 1)) : herm (Hpk k r) (bvec p) (bvec q) = Hpk k r q p := by
  rw [herm_bvec_left]
  simp [bvec, Pi.single_apply]

lemma hpk_col_eI (c : Fin r) (i : Fin (2 * r + k + 1)) :
    Hpk k r i (eI k r c) = if i = esI k r c then 1 else 0 := by
  have hc := c.isLt
  have hi := i.isLt
  unfold Hpk
  simp only [eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma hpk_col_esI (c : Fin r) (i : Fin (2 * r + k + 1)) :
    Hpk k r i (esI k r c) = if i = eI k r c then 1 else 0 := by
  have hc := c.isLt
  have hi := i.isLt
  unfold Hpk
  simp only [eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma herm_eI_left (c : Fin r) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (bvec (eI k r c)) w = star (w (esI k r c)) := by
  rw [herm_bvec_left]
  simp [hpk_col_eI]

lemma herm_esI_left (c : Fin r) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (bvec (esI k r c)) w = star (w (eI k r c)) := by
  rw [herm_bvec_left]
  simp [hpk_col_esI]

lemma hpk_eI_row_block (a : Fin r) (j : Fin (2 * r + k + 1)) (hj : r ≤ j.val) (hj' : j.val ≤ r + k) :
    Hpk k r (eI k r a) j = 0 := by
  have ha := a.isLt
  unfold Hpk
  simp only [eI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma hpk_eI_eI (a c : Fin r) : Hpk k r (eI k r a) (eI k r c) = 0 := by
  have ha := a.isLt
  have hc := c.isLt
  unfold Hpk
  simp only [eI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma one_mem_UWset (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z := by
  refine ⟨?_, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
  show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
  simp

theorem xuv_lieN (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) (v : Fin (2 * r + k + 1) → ℂ)
    (hv : ∀ b : Fin r, b.val ≤ a.val → v (esI k r b) = 0) :
    Xuv k r (bvec (eI k r a)) v ∈ lieOf (Sset k r z) := by
  intro t
  set X := Xuv k r (bvec (eI k r a)) v with hX
  have hXa : X *ᵥ bvec (eI k r a) = 0 := by
    rw [hX, xuv_mulVec, herm_eI_left, hv a le_rfl, herm_bvec_bvec, hpk_eI_eI]
    simp
  have hXc : ∀ c : Fin r, X *ᵥ bvec (eI k r c) = star (v (esI k r c)) • bvec (eI k r a) := by
    intro c
    rw [hX, xuv_mulVec, herm_eI_left, herm_bvec_bvec, hpk_eI_eI]
    simp
  have hXj : ∀ j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k →
      X *ᵥ bvec j = herm (Hpk k r) (bvec j) v • bvec (eI k r a) := by
    intro j hj hj'
    rw [hX, xuv_mulVec, herm_bvec_bvec, hpk_eI_row_block a j hj hj']
    simp
  refine ⟨1, one_mem_UWset z, NormedSpace.exp ((t : ℂ) • X), ⟨Formalism.FourierDecayAlt.P.B5.exp_mem (xuv_inLie _ _) t, ?_, ?_⟩,
    (Matrix.one_mul _).symm⟩
  · intro c i hci
    have e := exp_smul_mulVec_sq X (bvec (eI k r c)) (by rw [hXc, Matrix.mulVec_smul, hXa, smul_zero]) (t : ℂ)
    rw [show NormedSpace.exp ((t : ℂ) • X) i (eI k r c) = (NormedSpace.exp ((t : ℂ) • X) *ᵥ bvec (eI k r c)) i
      from mat_eq_mulVec_bvec _ _ _, e, hXc]
    have hz : star (v (esI k r c)) * bvec (eI k r a) i = 0 := by
      by_cases hca : c.val ≤ a.val
      · rw [hv c hca]; simp
      · have : i ≠ eI k r a := by
          intro h; rw [h] at hci; simp only [eI] at hci; omega
        simp [bvec, Pi.single_apply, this]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz, mul_zero, add_zero]
    simp [bvec, Pi.single_apply]
  · intro i j hj hj' hi
    have e := exp_smul_mulVec_sq X (bvec j) (by rw [hXj j hj hj', Matrix.mulVec_smul, hXa, smul_zero]) (t : ℂ)
    rw [show NormedSpace.exp ((t : ℂ) • X) i j = (NormedSpace.exp ((t : ℂ) • X) *ᵥ bvec j) i
      from mat_eq_mulVec_bvec _ _ _, e, hXj j hj hj']
    have : i ≠ eI k r a := by
      intro h; rw [h] at hi; simp only [eI] at hi; omega
    simp [bvec, Pi.single_apply, this]

theorem xuv_lieW (z u v : Fin (2 * r + k + 1) → ℂ) (hu : inWb k r u) (hv : inWb k r v)
    (huz : herm (Hpk k r) u z = 0) (hvz : herm (Hpk k r) v z = 0) :
    Xuv k r u v ∈ lieOf (UWset k r z) := by
  intro t
  set X := Xuv k r u v with hX
  have hes : ∀ (w : Fin (2 * r + k + 1) → ℂ), inWb k r w → ∀ c : Fin r, w (esI k r c) = 0 := by
    intro w hw c; exact hw _ (Or.inr (by simp only [esI]; omega))
  have hei : ∀ (w : Fin (2 * r + k + 1) → ℂ), inWb k r w → ∀ c : Fin r, w (eI k r c) = 0 := by
    intro w hw c; exact hw _ (Or.inl (by simp only [eI]; omega))
  refine ⟨Formalism.FourierDecayAlt.P.B5.exp_mem (xuv_inLie _ _) t, fun c => ⟨?_, ?_⟩, ?_⟩
  · refine exp_smul_mulVec_fix X _ ?_ _
    rw [hX, xuv_mulVec, herm_eI_left, herm_eI_left, hes v hv, hes u hu]; simp
  · refine exp_smul_mulVec_fix X _ ?_ _
    rw [hX, xuv_mulVec, herm_esI_left, herm_esI_left, hei v hv, hei u hu]; simp
  · refine exp_smul_mulVec_fix X _ ?_ _
    rw [hX, xuv_mulVec, herm_conj z v, herm_conj z u, hvz, huz]; simp

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
