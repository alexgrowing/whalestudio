import Mathlib
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuAdapt

section general

variable {ι : Type*} [Fintype ι]

theorem herm_add_left (H : Matrix ι ι ℂ) (x y w : ι → ℂ) : herm H (x + y) w = herm H x w + herm H y w := by
  simp [herm, mulVec_add, dotProduct_add]

theorem herm_sub_left (H : Matrix ι ι ℂ) (x y w : ι → ℂ) : herm H (x - y) w = herm H x w - herm H y w := by
  simp [herm, mulVec_sub, dotProduct_sub]

theorem herm_smul_left (H : Matrix ι ι ℂ) (a : ℂ) (x w : ι → ℂ) : herm H (a • x) w = a * herm H x w := by
  simp [herm, mulVec_smul, dotProduct_smul]

theorem herm_add_right (H : Matrix ι ι ℂ) (x y w : ι → ℂ) : herm H w (x + y) = herm H w x + herm H w y := by
  simp [herm, add_dotProduct]

theorem herm_sub_right (H : Matrix ι ι ℂ) (x y w : ι → ℂ) : herm H w (x - y) = herm H w x - herm H w y := by
  simp [herm, sub_dotProduct]

theorem herm_smul_right (H : Matrix ι ι ℂ) (a : ℂ) (x w : ι → ℂ) :
    herm H w (a • x) = star a * herm H w x := by
  simp [herm, smul_dotProduct]

theorem herm_neg_left (H : Matrix ι ι ℂ) (x w : ι → ℂ) : herm H (-x) w = - herm H x w := by
  simp [herm, mulVec_neg]

theorem herm_neg_right (H : Matrix ι ι ℂ) (x w : ι → ℂ) : herm H w (-x) = - herm H w x := by
  simp [herm]

theorem star_herm {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (x y : ι → ℂ) : star (herm H x y) = herm H y x := by
  unfold herm
  rw [← star_dotProduct_star, star_star, star_mulVec, hH, ← dotProduct_mulVec]

theorem herm_mulVec (H g : Matrix ι ι ℂ) (x y : ι → ℂ) :
    herm H (g *ᵥ x) (g *ᵥ y) = herm (gᴴ * H * g) x y := by
  unfold herm
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

variable [DecidableEq ι]

theorem herm_single (H : Matrix ι ι ℂ) (i j : ι) : herm H (Pi.single j 1) (Pi.single i 1) = H i j := by
  simp [herm, ← Pi.single_star]

theorem mem_UH_of_herm {H g : Matrix ι ι ℂ} (h : ∀ x y, herm H (g *ᵥ x) (g *ᵥ y) = herm H x y) :
    gᴴ * H * g = H := by
  ext i j
  rw [← herm_single (gᴴ * H * g), ← herm_mulVec, h, herm_single]

theorem refl_iso {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (v : ι → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hvv : herm H v v = c + star c) (x y : ι → ℂ) :
    herm H (x - (c⁻¹ * herm H x v) • v) (y - (c⁻¹ * herm H y v) • v) = herm H x y := by
  have hd : star c ≠ 0 := by simpa using hc
  simp only [herm_sub_left, herm_sub_right, herm_smul_left, herm_smul_right]
  rw [hvv, star_mul', star_herm hH, star_inv₀]
  generalize herm H x v = t
  generalize herm H v y = w
  generalize herm H x y = e
  generalize star c = d at hd ⊢
  field_simp
  ring

theorem exists_refl {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (u z : ι → ℂ) (huz : herm H u u = herm H z z)
    (hc : herm H u u - herm H u z ≠ 0) :
    ∃ γ : Matrix ι ι ℂ, γᴴ * H * γ = H ∧ γ *ᵥ u = z ∧
      ∀ x, herm H x u = 0 → herm H x z = 0 → γ *ᵥ x = x := by
  set v := u - z with hv
  set c := herm H u v with hcdef
  have hc0 : c ≠ 0 := by rwa [hcdef, hv, herm_sub_right]
  have hsc0 : star c ≠ 0 := by simpa using hc0
  have hvv : herm H v v = c + star c := by
    rw [hcdef, star_herm hH, hv]
    simp only [herm_sub_left, herm_sub_right]
    rw [huz]; ring
  have act : ∀ x, (1 - c⁻¹ • vecMulVec v (star v ᵥ* H)) *ᵥ x = x - (c⁻¹ * herm H x v) • v := by
    intro x
    rw [sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, ← dotProduct_mulVec]
    congr 1
    ext i
    simp [herm]
    ring
  refine ⟨1 - c⁻¹ • vecMulVec v (star v ᵥ* H), ?_, ?_, ?_⟩
  · apply mem_UH_of_herm
    intro x y
    rw [act, act]
    exact refl_iso hH v c hc0 hvv x y
  · rw [act, ← hcdef, inv_mul_cancel₀ hc0, one_smul, hv]; abel
  · intro x h1 h2
    rw [act, hv, herm_sub_right, h1, h2]; simp

theorem exists_move {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (u z : ι → ℂ) (huz : herm H u u = herm H z z)
    (h0 : herm H u u ≠ 0) :
    ∃ γ : Matrix ι ι ℂ, γᴴ * H * γ = H ∧ γ *ᵥ u = z ∧
      ∀ x, herm H x u = 0 → herm H x z = 0 → γ *ᵥ x = x := by
  by_cases hc : herm H u u - herm H u z = 0
  · obtain ⟨γ₁, a1, b1, c1⟩ := exists_refl hH u (-u) (by rw [herm_neg_left, herm_neg_right, neg_neg])
      (by rw [herm_neg_right]; intro h; apply h0; linear_combination h / 2)
    obtain ⟨γ₂, a2, b2, c2⟩ := exists_refl hH (-u) z (by rw [herm_neg_left, herm_neg_right, neg_neg, huz])
      (by
        rw [herm_neg_left, herm_neg_left, herm_neg_right]; intro h; apply h0
        linear_combination h / 2 + hc / 2)
    refine ⟨γ₂ * γ₁, ?_, ?_, ?_⟩
    · rw [conjTranspose_mul]
      calc γ₁ᴴ * γ₂ᴴ * H * (γ₂ * γ₁) = γ₁ᴴ * (γ₂ᴴ * H * γ₂) * γ₁ := by simp only [Matrix.mul_assoc]
        _ = H := by rw [a2, a1]
    · rw [← mulVec_mulVec, b1, b2]
    · intro x h1 h2
      rw [← mulVec_mulVec, c1 x h1 (by rw [herm_neg_right, h1, neg_zero]),
        c2 x (by rw [herm_neg_right, h1, neg_zero]) h2]
  · exact exists_refl hH u z huz hc

end general

def s2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

theorem star_inv_sqrt_two_bis : star s2 = s2 := by simp [s2]

theorem inv_sqrt_two_mul_self_bis : s2 * s2 = 1 / 2 := by
  unfold s2
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num

def col (k r : ℕ) (j : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) → ℂ :=
  if j.val = r then s2 • (bvec (wI k r 0) + bvec (wI k r (Fin.last k)))
  else if j.val = r + k then s2 • (bvec (wI k r 0) - bvec (wI k r (Fin.last k)))
  else bvec j

def G0 (k r : ℕ) : Mat (2 * r + k + 1) := Matrix.of fun i j => col k r j i

theorem unitary_adapted_basis_apply_basis (k r : ℕ) (j : Fin (2 * r + k + 1)) : G0 k r *ᵥ bvec j = col k r j := by
  ext i
  simp [G0, bvec]

theorem herm_bvec {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) : herm H (bvec j) (bvec i) = H i j :=
  herm_single H i j

theorem unitary_adapted_basis_entry (k r : ℕ) (H : Mat (2 * r + k + 1)) (i j : Fin (2 * r + k + 1)) :
    ((G0 k r)ᴴ * H * G0 k r) i j = herm H (col k r j) (col k r i) := by
  rw [← herm_bvec ((G0 k r)ᴴ * H * G0 k r), ← herm_mulVec, unitary_adapted_basis_apply_basis, unitary_adapted_basis_apply_basis]

theorem unitary_adapted_basis_is_unitary (k r : ℕ) (hk : 1 ≤ k) : (G0 k r)ᴴ * G0 k r = 1 := by
  have : (G0 k r)ᴴ * G0 k r = (G0 k r)ᴴ * 1 * G0 k r := by rw [Matrix.mul_one]
  rw [this]
  ext i j
  rw [unitary_adapted_basis_entry]
  have hs := inv_sqrt_two_mul_self_bis
  unfold col
  split_ifs <;>
    simp only [herm_smul_left, herm_smul_right, herm_add_left, herm_add_right, herm_sub_left, herm_sub_right,
      herm_bvec, star_inv_sqrt_two_bis, Matrix.one_apply, Fin.ext_iff, wI, Fin.val_zero, Fin.val_last] <;>
    split_ifs <;>
    first
      | (exfalso; omega)
      | linear_combination 2 * hs
      | ring

section entries

variable {k r : ℕ} {i j : Fin (2 * r + k + 1)}

theorem Hpk_val (i j : Fin (2 * r + k + 1)) : Hpk k r i j =
    if i.val < r ∧ i.val + j.val = 2 * r + k then 1
    else if j.val < r ∧ i.val + j.val = 2 * r + k then 1
    else if r ≤ i.val ∧ i.val ≤ r + k ∧ i.val = j.val then (if i.val = r + k then -1 else 1)
    else 0 := by
  simp only [Hpk, Fin.ext_iff]

theorem Hq_val (i j : Fin (2 * r + k + 1)) : Hq k r i j =
    if i.val ≤ r ∨ r + k ≤ i.val then (if i.val + j.val = 2 * r + k then 1 else 0)
    else if i.val = j.val then 1 else 0 := by
  simp only [Hq, outer, Fin.ext_iff]

theorem A_pp (hk : 1 ≤ k) (hi : i.val = r) (hj : j.val = r) : Hpk k r i j = 1 := by
  rw [Hpk_val]; split_ifs <;> first | (exfalso; omega) | rfl

theorem A_qq (hk : 1 ≤ k) (hi : i.val = r + k) (hj : j.val = r + k) : Hpk k r i j = -1 := by
  rw [Hpk_val]; split_ifs <;> first | (exfalso; omega) | rfl

theorem A_zp (hk : 1 ≤ k) (hi : i.val ≠ r) (hj : j.val = r) : Hpk k r i j = 0 := by
  rw [Hpk_val]; split_ifs <;> first | (exfalso; omega) | rfl

theorem A_pz (hk : 1 ≤ k) (hi : i.val = r) (hj : j.val ≠ r) : Hpk k r i j = 0 := by
  rw [Hpk_val]; split_ifs <;> first | (exfalso; omega) | rfl

theorem A_zq (hk : 1 ≤ k) (hi : i.val ≠ r + k) (hj : j.val = r + k) : Hpk k r i j = 0 := by
  rw [Hpk_val]; split_ifs <;> first | (exfalso; omega) | rfl

theorem A_qz (hk : 1 ≤ k) (hi : i.val = r + k) (hj : j.val ≠ r + k) : Hpk k r i j = 0 := by
  rw [Hpk_val]; split_ifs <;> first | (exfalso; omega) | rfl

theorem Q_pq (hi : i.val = r) (hj : j.val = r + k) : Hq k r i j = 1 := by
  rw [Hq_val]; split_ifs <;> first | (exfalso; omega) | rfl

theorem Q_qp (hi : i.val = r + k) (hj : j.val = r) : Hq k r i j = 1 := by
  rw [Hq_val]; split_ifs <;> first | (exfalso; omega) | rfl

theorem Q_pz (hi : i.val = r) (hj : j.val ≠ r + k) : Hq k r i j = 0 := by
  rw [Hq_val]; split_ifs <;> first | (exfalso; omega) | rfl

theorem Q_qz (hi : i.val = r + k) (hj : j.val ≠ r) : Hq k r i j = 0 := by
  rw [Hq_val]; split_ifs <;> first | (exfalso; omega) | rfl

theorem Q_zp (hi : i.val ≠ r + k) (hi' : i.val ≠ r) (hj : j.val = r) : Hq k r i j = 0 := by
  rw [Hq_val]; split_ifs <;> first | (exfalso; omega) | rfl

theorem Q_zq (hi : i.val ≠ r) (hi' : i.val ≠ r + k) (hj : j.val = r + k) : Hq k r i j = 0 := by
  rw [Hq_val]; split_ifs <;> first | (exfalso; omega) | rfl

theorem Q_eq_A (hi : i.val ≠ r) (hi' : i.val ≠ r + k) (hj : j.val ≠ r) (hj' : j.val ≠ r + k) :
    Hq k r i j = Hpk k r i j := by
  have := i.isLt
  have := j.isLt
  rw [Hq_val, Hpk_val]; split_ifs <;> first | (exfalso; omega) | rfl

theorem col_p (hj : j.val = r) :
    col k r j = s2 • (bvec (wI k r 0) + bvec (wI k r (Fin.last k))) := by
  rw [col, if_pos hj]

theorem col_q (hk : 1 ≤ k) (hj : j.val = r + k) :
    col k r j = s2 • (bvec (wI k r 0) - bvec (wI k r (Fin.last k))) := by
  rw [col, if_neg (by omega), if_pos hj]

theorem col_o (hj : j.val ≠ r) (hj' : j.val ≠ r + k) : col k r j = bvec j := by
  rw [col, if_neg hj, if_neg hj']

end entries

theorem unitary_adapted_basis_transforms_form (k r : ℕ) (hk : 1 ≤ k) : (G0 k r)ᴴ * Hpk k r * G0 k r = Hq k r := by
  ext i j
  rw [unitary_adapted_basis_entry]
  have hs := inv_sqrt_two_mul_self_bis
  have hP : (wI k r 0).val = r := by simp [wI]
  have hQ : (wI k r (Fin.last k)).val = r + k := by simp [wI]
  have hPQ : (wI k r 0).val ≠ r + k := by omega
  have hQP : (wI k r (Fin.last k)).val ≠ r := by omega
  have e1 := A_pp hk hP hP
  have e2 := A_qq hk hQ hQ
  have e3 := A_pz hk hP hQP
  have e4 := A_zp hk hQP hP
  by_cases hjp : j.val = r
  · rw [col_p hjp]
    by_cases hip : i.val = r
    · rw [col_p hip]
      have q : Hq k r i j = 0 := Q_pz hip (by omega)
      simp only [herm_smul_left, herm_smul_right, herm_add_left, herm_add_right, herm_bvec, star_inv_sqrt_two_bis, e1, e2, e3, e4, q]
      ring
    · by_cases hiq : i.val = r + k
      · rw [col_q hk hiq]
        have q : Hq k r i j = 1 := Q_qp hiq hjp
        simp only [herm_smul_left, herm_smul_right, herm_add_left, herm_sub_right, herm_add_right, herm_bvec, star_inv_sqrt_two_bis, e1, e2, e3, e4, q]
        linear_combination 2 * hs
      · rw [col_o hip hiq]
        have q : Hq k r i j = 0 := Q_zp hiq hip hjp
        simp only [herm_smul_left, herm_add_left, herm_bvec, A_zp hk hip hP, A_zq hk hiq hQ, q]
        ring
  · by_cases hjq : j.val = r + k
    · rw [col_q hk hjq]
      by_cases hip : i.val = r
      · rw [col_p hip]
        have q : Hq k r i j = 1 := Q_pq hip hjq
        simp only [herm_smul_left, herm_smul_right, herm_sub_left, herm_add_right, herm_bvec, star_inv_sqrt_two_bis, e1, e2, e3, e4, q]
        linear_combination 2 * hs
      · by_cases hiq : i.val = r + k
        · rw [col_q hk hiq]
          have q : Hq k r i j = 0 := Q_qz hiq hjp
          simp only [herm_smul_left, herm_smul_right, herm_sub_left, herm_sub_right, herm_bvec, star_inv_sqrt_two_bis, e1, e2, e3, e4, q]
          ring
        · rw [col_o hip hiq]
          have q : Hq k r i j = 0 := Q_zq hip hiq hjq
          simp only [herm_smul_left, herm_sub_left, herm_bvec, A_zp hk hip hP, A_zq hk hiq hQ, q]
          ring
    · rw [col_o hjp hjq]
      by_cases hip : i.val = r
      · rw [col_p hip]
        have q : Hq k r i j = 0 := Q_pz hip hjq
        simp only [herm_smul_right, herm_add_right, herm_bvec, star_inv_sqrt_two_bis, A_pz hk hP hjp, A_qz hk hQ hjq, q]
        ring
      · by_cases hiq : i.val = r + k
        · rw [col_q hk hiq]
          have q : Hq k r i j = 0 := Q_qz hiq hjp
          simp only [herm_smul_right, herm_sub_right, herm_bvec, star_inv_sqrt_two_bis, A_pz hk hP hjp, A_qz hk hQ hjq, q]
          ring
        · rw [col_o hip hiq, herm_bvec, Q_eq_A hip hiq hjp hjq]

theorem Hpk_herm (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  simp only [conjTranspose_apply, Hpk, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | simp

theorem herm_outer (k r : ℕ) (i : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val)
    (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) : herm (Hpk k r) (bvec i) z = 0 := by
  unfold herm dotProduct
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j.val < r ∨ r + k < j.val
  · simp [hz j hj]
  · have : Hpk k r j i = 0 := by
      have := i.isLt
      simp only [Hpk, Fin.ext_iff]
      split_ifs <;> first | (exfalso; omega) | rfl
    simp [bvec, this]

theorem adaptExists : AdaptExists := by
  intro k r hk
  refine ⟨⟨G0 k r, unitary_adapted_basis_is_unitary k r hk, unitary_adapted_basis_transforms_form k r hk⟩, ?_⟩
  intro z hz hT
  set ρ : ℝ := Real.sqrt (Tz k r z / 2) with hρ
  have hρ0 : 0 < ρ := Real.sqrt_pos.mpr (by linarith)
  have hρ2 : (ρ : ℂ) * ρ = (Tz k r z : ℂ) / 2 := by
    rw [← Complex.ofReal_mul, hρ, Real.mul_self_sqrt (by linarith)]
    push_cast; ring
  set u : Fin (2 * r + k + 1) → ℂ := ((ρ : ℂ) * (2 * s2)) • bvec (wI k r (Fin.last k)) with hu
  have hzz : herm (Hpk k r) z z = -(Tz k r z : ℂ) := by
    have h := star_herm (Hpk_herm k r) z z
    have h' : ((herm (Hpk k r) z z).re : ℂ) = herm (Hpk k r) z z := Complex.conj_eq_iff_re.mp h
    rw [← h']; simp [Tz]
  have hww : Hpk k r (wI k r (Fin.last k)) (wI k r (Fin.last k)) = -1 :=
    A_qq hk (by simp [wI]) (by simp [wI])
  have huu : herm (Hpk k r) u u = -(Tz k r z : ℂ) := by
    have h2 : star (2 : ℂ) = 2 := by simp
    have h3 : star (ρ : ℂ) = ρ := by simp
    rw [hu, herm_smul_left, herm_smul_right, herm_bvec, hww, star_mul', star_mul', star_inv_sqrt_two_bis, h2, h3]
    linear_combination (-4 * (ρ : ℂ) * ρ) * inv_sqrt_two_mul_self_bis - 2 * hρ2
  have huW : inWb k r u := by
    intro i hi
    have : i ≠ wI k r (Fin.last k) := by
      intro h
      rw [h] at hi
      simp only [wI, Fin.val_last] at hi
      omega
    simp [hu, bvec, this]
  obtain ⟨γ, hγ, hγu, hfix⟩ := exists_move (Hpk_herm k r) u z (by rw [huu, hzz])
    (by rw [huu]; exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hT.ne'))
  have hout : ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → (γ * G0 k r) *ᵥ bvec i = bvec i := by
    intro i hi
    rw [← mulVec_mulVec, unitary_adapted_basis_apply_basis, col, if_neg (by omega), if_neg (by omega)]
    exact hfix _ (herm_outer k r i hi u huW) (herm_outer k r i hi z hz)
  refine ⟨γ * G0 k r, ?_, ?_, ρ, hρ0, ?_⟩
  · rw [conjTranspose_mul, ← unitary_adapted_basis_transforms_form k r hk]
    conv_rhs => rw [← hγ]
    simp only [Matrix.mul_assoc]
  · intro a
    have := a.isLt
    exact ⟨hout _ (by simp only [eI]; omega), hout _ (by simp only [esI]; omega)⟩
  · rw [← hγu, ← mulVec_mulVec, ← mulVec_smul]
    congr 1
    rw [mulVec_sub, unitary_adapted_basis_apply_basis, unitary_adapted_basis_apply_basis, col_p (by simp [wI]), col_q hk (by simp [wI]), hu]
    module

end GlobalTheory.CompanionTheory.BmuAdapt
