import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InductiveHeisenbergInputs

noncomputable section

open Matrix MeasureTheory
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace FormulaFAux

def sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩

theorem sg_val (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (sg k r i).val = if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val := by
  unfold sg; split_ifs <;> rfl

theorem sg_sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : sg k r (sg k r i) = i := by
  apply Fin.ext; rw [sg_val, sg_val]; split_ifs <;> omega

theorem hpk_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = sg k r i then (if i.val = r + k then -1 else 1) else 0 := by
  have key : j = sg k r i ↔ j.val = (if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val) := by
    rw [← sg_val, Fin.ext_iff]
  unfold Hpk
  simp only [key, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_mulVec (k r : ℕ) (w : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ w) i = (if i.val = r + k then -1 else 1) * w (sg k r i) := by
  simp [mulVec, dotProduct, hpk_apply]

theorem star_hpk_dot (k r : ℕ) (u w : Fin (2 * r + k + 1) → ℂ) :
    star (Hpk k r *ᵥ u) ⬝ᵥ (Hpk k r *ᵥ w) = star u ⬝ᵥ w := by
  simp only [dotProduct, Pi.star_apply, hpk_mulVec]
  calc ∑ i, star ((if i.val = r + k then -1 else 1 : ℂ) * u (sg k r i)) * ((if i.val = r + k then -1 else 1) * w (sg k r i))
      = ∑ i, star (u (sg k r i)) * w (sg k r i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
    _ = ∑ i, star (u i) * w i :=
        Fintype.sum_equiv (Function.Involutive.toPerm _ (sg_sg k r)) _ _ (fun i => rfl)

abbrev cc : ℂ := ((Real.sqrt 2)⁻¹ : ℂ)

theorem cc_sq : cc * cc = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have h0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    intro h'; rw [h', zero_pow two_ne_zero] at h; norm_num at h
  simp only [cc]; field_simp; rw [h]

def aF (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (t : Fin (r + 1)) : ℂ :=
  if h : t.val < r then y (eI k r ⟨t.val, h⟩) else cc * (y (wI k r 0) - y (wI k r (Fin.last k)))

def aF' (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (t : Fin (r + 1)) : ℂ :=
  if h : t.val < r then y (esI k r ⟨t.val, h⟩) else cc * (y (wI k r 0) + y (wI k r (Fin.last k)))

theorem levPos_inj (k r' : ℕ) : Function.Injective (levPos k 1 r') := by
  intro i j h; simp only [levPos, Fin.ext_iff] at h; exact Fin.ext (by omega)

theorem lift_levPos (k r' : ℕ) (v : Fin (2 * r' + k + 1) → ℂ) (i : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' v (levPos k 1 r' i) = v i := by
  unfold liftVec; rw [dif_pos (by simp only [levPos]; omega)]; congr 1

theorem lift_zero (k r' : ℕ) (v : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (1 + r') + k + 1))
    (hp : p ∉ Set.range (levPos k 1 r')) : liftVec k 1 r' v p = 0 := by
  simp only [liftVec]; rw [dif_neg]; rintro ⟨h1, h2⟩
  exact hp ⟨⟨p.val - 1, by omega⟩, Fin.ext (by simp [levPos]; omega)⟩

theorem lift_dot (k r' : ℕ) (u v : Fin (2 * r' + k + 1) → ℂ) :
    star (liftVec k 1 r' u) ⬝ᵥ liftVec k 1 r' v = star u ⬝ᵥ v := by
  simp only [dotProduct, Pi.star_apply]
  symm
  refine Fintype.sum_of_injective _ (levPos_inj k r') _ _ (fun p hp => ?_) (fun i => ?_)
  · rw [lift_zero _ _ v _ hp, mul_zero]
  · rw [lift_levPos, lift_levPos]

theorem gram_det (m : ℕ) (Mx : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (c : ℂ) (x a : ℕ → ℂ)
    (h00 : Mx 0 0 = 1 + c) (h0j : ∀ j : Fin m, Mx 0 j.succ = star (x j))
    (hj0 : ∀ j : Fin m, Mx j.succ 0 = x j)
    (hij : ∀ i j : Fin m, Mx i.succ j.succ = (if i = j then 1 else 0) + a i * star (a j)) :
    Mx.det = (1 + c - ∑ j ∈ Finset.range m, star (x j) * x j) * (1 + ∑ j ∈ Finset.range m, star (a j) * a j) +
      (∑ j ∈ Finset.range m, star (x j) * a j) * (∑ j ∈ Finset.range m, star (a j) * x j) := by
  let al : Fin (m + 1) → ℂ := Fin.cases 1 (fun _ => 0)
  let xh : Fin (m + 1) → ℂ := Fin.cases 0 (fun j => x j)
  let ah : Fin (m + 1) → ℂ := Fin.cases 0 (fun j => a j)
  let U : Matrix (Fin (m + 1)) (Fin 3) ℂ := Matrix.of fun i q => ![al i, xh i, ah i] q
  let V : Matrix (Fin 3) (Fin (m + 1)) ℂ := Matrix.of fun q j => ![c * al j + star (xh j), al j, star (ah j)] q
  have hM : Mx = 1 + U * V := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [h00, U, V, al, xh, ah, Matrix.mul_apply, Fin.sum_univ_three]
    · simp [h0j, U, V, al, xh, ah, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, (Fin.succ_ne_zero j).symm]
    · simp [hj0, U, V, al, xh, ah, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]
    · simp [hij, U, V, al, xh, ah, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Fin.succ_inj]
  rw [hM, det_one_add_mul_comm, det_fin_three]
  simp only [← Fin.sum_univ_eq_sum_range]
  simp [U, V, al, xh, ah, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  ring

end FormulaFAux

end ReciprocityTheory.ChartRestriction.DS.Xi
