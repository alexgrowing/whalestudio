import Formalism.HermitianCurvature.HermitianCurvatureProofs.QQMemAdjAlgCpt
import Formalism.FormalDegreeBessel.FormalDegreeRatio.ReverseCauchySchwarzHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GNonneg

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Form

variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)

theorem hb_add_left (x y w : Fin m → ℂ) : herm H (x + y) w = herm H x w + herm H y w := by
  simp only [herm, Matrix.mulVec_add, dotProduct_add]

theorem hb_sub_left (x y w : Fin m → ℂ) : herm H (x - y) w = herm H x w - herm H y w := by
  simp only [herm, Matrix.mulVec_sub, dotProduct_sub]

theorem hb_smul_left (c : ℂ) (x w : Fin m → ℂ) : herm H (c • x) w = c * herm H x w := by
  simp only [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hb_add_right (x w w' : Fin m → ℂ) : herm H x (w + w') = herm H x w + herm H x w' := by
  simp only [herm, star_add, add_dotProduct]

theorem hb_sub_right (x w w' : Fin m → ℂ) : herm H x (w - w') = herm H x w - herm H x w' := by
  simp only [herm, star_sub, sub_dotProduct]

theorem hb_smul_right (c : ℂ) (x w : Fin m → ℂ) : herm H x (c • w) = star c * herm H x w := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]

theorem hb_symm (hH : Hᴴ = H) (x y : Fin m → ℂ) : herm H y x = star (herm H x y) := by
  simp only [herm]
  rw [star_dotProduct, Matrix.star_mulVec, hH, Matrix.dotProduct_mulVec]

theorem hb_UH {g : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ UH H) (x y : Fin m → ℂ) :
    herm H (g *ᵥ x) (g *ᵥ y) = herm H x y := by
  have hg' : gᴴ * H * g = H := hg
  simp only [herm]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']

theorem hb_self_real (hH : Hᴴ = H) (x : Fin m → ℂ) : herm H x x = ((herm H x x).re : ℂ) := by
  have h := hb_symm H hH x x
  exact (Complex.conj_eq_iff_re.mp (by simpa [Complex.star_def] using h.symm)).symm

theorem hb_expand (u v : Fin m → ℂ) (s : ℂ) :
    herm H (u + s • v) (u + s • v) =
      herm H u u + star s * herm H u v + s * herm H v u + s * star s * herm H v v := by
  rw [hb_add_left, hb_add_right, hb_add_right, hb_smul_left, hb_smul_left, hb_smul_right,
    hb_smul_right]
  ring

end Form

section Wb

variable {k r : ℕ}

theorem hpk_herm (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Hpk]
  rcases i with ⟨a, ha⟩
  rcases j with ⟨b, hb⟩
  simp only [Fin.mk.injEq]
  split_ifs <;> first | (exfalso; omega) | simp

theorem inWb_add {x y : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) (hy : inWb k r y) : inWb k r (x + y) := by
  intro i hi
  simp only [Pi.add_apply, hx i hi, hy i hi, add_zero]

theorem inWb_sub {x y : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) (hy : inWb k r y) : inWb k r (x - y) := by
  intro i hi
  simp only [Pi.sub_apply, hx i hi, hy i hi, sub_zero]

theorem inWb_smul (c : ℂ) {x : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) : inWb k r (c • x) := by
  intro i hi
  simp only [Pi.smul_apply, hx i hi, smul_zero]

theorem perp_nonneg {b v : Fin (2 * r + k + 1) → ℂ} (hb : inWb k r b) (hbn : (herm (Hpk k r) b b).re < 0)
    (hv : inWb k r v) (hvb : herm (Hpk k r) v b = 0) : 0 ≤ (herm (Hpk k r) v v).re := by
  by_contra hneg
  push_neg at hneg
  have h := reverse_cauchy_schwarz_holds k r v b hv hb hneg hbn
  have h0 : herm (Hpk k r) b v = 0 := by rw [hb_symm _ (hpk_herm k r) v b, hvb, star_zero]
  rw [h0, map_zero] at h
  have h1 : 0 < Tz k r v := by unfold Tz; linarith
  have h2 : 0 < Tz k r b := by unfold Tz; linarith
  nlinarith [mul_pos h1 h2]

theorem norm_perp_le {b u v : Fin (2 * r + k + 1) → ℂ} (hb : inWb k r b) (hbn : (herm (Hpk k r) b b).re < 0)
    (hu : inWb k r u) (hv : inWb k r v) (hub : herm (Hpk k r) u b = 0) (hvb : herm (Hpk k r) v b = 0) :
    ‖herm (Hpk k r) u v‖ ≤ (herm (Hpk k r) u u).re + (herm (Hpk k r) v v).re := by
  set H := Hpk k r
  have hvu : herm H v u = star (herm H u v) := hb_symm H (hpk_herm k r) u v
  have key : ∀ s : ℂ, s * star s = 1 →
      0 ≤ (herm H u u).re + (herm H v v).re + (star s * herm H u v + s * star (herm H u v)).re := by
    intro s hs
    have hw : inWb k r (u + s • v) := inWb_add hu (inWb_smul s hv)
    have hwb : herm H (u + s • v) b = 0 := by rw [hb_add_left, hb_smul_left, hub, hvb]; ring
    have h0 := perp_nonneg hb hbn hw hwb
    rw [hb_expand, hvu, hs, one_mul] at h0
    simp only [Complex.add_re] at h0 ⊢
    linarith
  set X := herm H u v
  have k1 := key 1 (by simp)
  have k2 := key (-1) (by simp)
  have k3 := key Complex.I (by simp [Complex.star_def])
  have k4 := key (-Complex.I) (by simp [Complex.star_def])
  simp only [Complex.star_def, map_one, map_neg, Complex.conj_I, one_mul, neg_mul, neg_neg, Complex.add_re,
    Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, zero_mul,
    one_mul, sub_zero, zero_sub, mul_neg, neg_zero] at k1 k2 k3 k4
  have hre : |X.re| ≤ ((herm H u u).re + (herm H v v).re) / 2 := by
    rw [abs_le]; constructor <;> linarith
  have him : |X.im| ≤ ((herm H u u).re + (herm H v v).re) / 2 := by
    rw [abs_le]; constructor <;> linarith
  calc ‖X‖ ≤ |X.re| + |X.im| := Complex.norm_le_abs_re_add_abs_im X
    _ ≤ _ := by linarith

end Wb

section Bound

variable {k r : ℕ}

theorem hb_sub_expand {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (u v w : Fin m → ℂ) (s s' : ℂ) :
    herm H (u - s • w) (v - s' • w) =
      herm H u v - star s' * herm H u w - s * herm H w v + s * star s' * herm H w w := by
  rw [hb_sub_left, hb_sub_right, hb_sub_right, hb_smul_left, hb_smul_left, hb_smul_right,
    hb_smul_right]
  ring

theorem norm_herm_le {a b c : Fin (2 * r + k + 1) → ℂ} (ha : inWb k r a) (hb : inWb k r b) (hc : inWb k r c)
    (hbn : (herm (Hpk k r) b b).re < 0) :
    ‖herm (Hpk k r) a c‖ ≤ (herm (Hpk k r) a a).re + (herm (Hpk k r) c c).re +
      (-(herm (Hpk k r) b b).re)⁻¹ * (‖herm (Hpk k r) a b‖ ^ 2 + ‖herm (Hpk k r) c b‖ ^ 2 +
        ‖herm (Hpk k r) a b‖ * ‖herm (Hpk k r) c b‖) := by
  set H := Hpk k r with hHdef
  have hH : Hᴴ = H := hpk_herm k r
  set T : ℝ := -(herm H b b).re with hTdef
  have hTpos : 0 < T := by rw [hTdef]; linarith
  set t : ℝ := T⁻¹ with htdef
  have htT : (t : ℂ) * (T : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, htdef, inv_mul_cancel₀ hTpos.ne', Complex.ofReal_one]
  have hbb : herm H b b = -(T : ℂ) := by
    rw [hb_self_real H hH b, hTdef]; push_cast; ring
  set X := herm H a b with hX
  set Z := herm H c b with hZ
  have hXn : X * star X = ((‖X‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hZn : Z * star Z = ((‖Z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hst : star (t : ℂ) = (t : ℂ) := by rw [Complex.star_def, Complex.conj_ofReal]
  set α : ℂ := -((t : ℂ) * X) with hα
  set γ : ℂ := -((t : ℂ) * Z) with hγ
  have hsα : star α = -((t : ℂ) * star X) := by rw [hα, star_neg, star_mul', hst]
  have hsγ : star γ = -((t : ℂ) * star Z) := by rw [hγ, star_neg, star_mul', hst]
  have hba : herm H b a = star X := hb_symm H hH a b
  have hbc : herm H b c = star Z := hb_symm H hH c b
  have ha' : inWb k r (a - α • b) := inWb_sub ha (inWb_smul α hb)
  have hc' : inWb k r (c - γ • b) := inWb_sub hc (inWb_smul γ hb)
  have ha'b : herm H (a - α • b) b = 0 := by
    rw [hb_sub_left, hb_smul_left, hbb, ← hX, hα]
    linear_combination (-X) * htT
  have hc'b : herm H (c - γ • b) b = 0 := by
    rw [hb_sub_left, hb_smul_left, hbb, ← hZ, hγ]
    linear_combination (-Z) * htT
  have eac := hb_sub_expand H a c b α γ
  rw [← hX, hbc, hsγ, hbb] at eac
  have eaa := hb_sub_expand H a a b α α
  rw [← hX, hba, hsα, hbb] at eaa
  have ecc := hb_sub_expand H c c b γ γ
  rw [← hZ, hbc, hsγ, hbb] at ecc
  have hac : herm H a c = herm H (a - α • b) (c - γ • b) - (t : ℂ) * X * star Z := by
    rw [eac, hα]
    linear_combination ((t : ℂ) * X * star Z) * htT
  have haa' : herm H (a - α • b) (a - α • b) = herm H a a + ((t * ‖X‖ ^ 2 : ℝ) : ℂ) := by
    rw [eaa, hα]; push_cast at hXn ⊢
    linear_combination ((2 : ℂ) * t - t * t * T) * hXn + (-(t * ‖X‖ ^ 2 : ℂ)) * htT
  have hcc' : herm H (c - γ • b) (c - γ • b) = herm H c c + ((t * ‖Z‖ ^ 2 : ℝ) : ℂ) := by
    rw [ecc, hγ]; push_cast at hZn ⊢
    linear_combination ((2 : ℂ) * t - t * t * T) * hZn + (-(t * ‖Z‖ ^ 2 : ℂ)) * htT
  have hperp := norm_perp_le hb hbn ha' hc' ha'b hc'b
  rw [haa', hcc', Complex.add_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_re] at hperp
  have ht0 : 0 ≤ t := inv_nonneg.mpr hTpos.le
  have hn : ‖(t : ℂ) * X * star Z‖ = t * (‖X‖ * ‖Z‖) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0, norm_star]; ring
  rw [hac]
  calc ‖herm H (a - α • b) (c - γ • b) - (t : ℂ) * X * star Z‖
      ≤ ‖herm H (a - α • b) (c - γ • b)‖ + ‖(t : ℂ) * X * star Z‖ := norm_sub_le _ _
    _ ≤ _ := by rw [hn]; nlinarith

end Bound

section Group

variable {k r : ℕ}

theorem hpk_outer (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) :
    (Hpk k r *ᵥ y) ⟨2 * r + k - i.val, by omega⟩ = y i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · simp only [Hpk, Fin.val_mk]
    split_ifs <;> first | (exfalso; omega) | simp
  · intro j _ hj
    have hj' : j.val ≠ i.val := fun h => hj (Fin.ext h)
    simp only [Hpk, Fin.val_mk, Fin.ext_iff]
    split_ifs <;> first | (exfalso; omega) | simp
  · simp

theorem norm_hpk_mid (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) (hi : r ≤ i.val ∧ i.val ≤ r + k) :
    ‖(Hpk k r *ᵥ y) i‖ = ‖y i‖ := by
  have h : (Hpk k r *ᵥ y) i = (if i.val = r + k then -1 else 1) * y i := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single i]
    · simp only [Hpk, and_true]
      split_ifs <;> first | (exfalso; omega) | simp
    · intro j _ hj
      have hj' : j.val ≠ i.val := fun h => hj (Fin.ext h)
      simp only [Hpk, Fin.ext_iff]
      split_ifs <;> first | (exfalso; omega) | simp
    · simp
  rw [h]
  split_ifs <;> simp

theorem glev_fix {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (q : Fin (2 * r + k + 1))
    (hq : q.val < r ∨ r + k < q.val) : g *ᵥ bvec q = bvec q := by
  rcases hq with hq | hq
  · have e : q = eI k r ⟨q.val, hq⟩ := Fin.ext rfl
    rw [e]
    exact (hg.2 ⟨q.val, hq⟩ (by simp only [Fin.val_last]; exact hq)).1
  · have hlt : 2 * r + k - q.val < r := by omega
    have e : q = esI k r ⟨2 * r + k - q.val, hlt⟩ := Fin.ext (by simp only [esI]; omega)
    rw [e]
    exact (hg.2 ⟨2 * r + k - q.val, hlt⟩ (by simp only [Fin.val_last]; exact hlt)).2

theorem glev_wb {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    inWb k r (g *ᵥ v) := by
  intro i hi
  have hp := hpk_outer (g *ᵥ v) i hi
  have hp' := hpk_outer v i hi
  have hout : (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1)).val < r ∨
      r + k < (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1)).val := by simp only [Fin.val_mk]; omega
  rw [← hp, ← gn_herm_bvec_right, ← glev_fix hg _ hout, hb_UH _ hg.1, gn_herm_bvec_right, hp', hv i hi]

theorem bvec_wb (q : Fin (2 * r + k + 1)) (hq : r ≤ q.val ∧ q.val ≤ r + k) : inWb k r (bvec q) := by
  intro i hi
  have hne : i ≠ q := by
    rintro rfl
    omega
  simp [bvec, Pi.single_apply, hne]

theorem entry_eq (g : Mx k r) (p q : Fin (2 * r + k + 1)) : g p q = (g *ᵥ bvec q) p := by
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem fvec_last (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by
  simp [fvec]

variable (z z' : Fin (2 * r + k + 1) → ℂ)

def bz (p : Fin (2 * r + k + 1)) (R : ℝ) : ℝ :=
  (herm (Hpk k r) (bvec p) (bvec p)).re + (herm (Hpk k r) z' z').re +
    (-(herm (Hpk k r) z z).re)⁻¹ * (‖herm (Hpk k r) (bvec p) z‖ ^ 2 + R ^ 2 + ‖herm (Hpk k r) (bvec p) z‖ * R)

def bnd (p q : Fin (2 * r + k + 1)) (R : ℝ) : ℝ :=
  1 + |(herm (Hpk k r) (bvec q) (bvec q)).re| + |(herm (Hpk k r) (bvec p) (bvec p)).re| +
    (-(herm (Hpk k r) z' z').re)⁻¹ * (‖herm (Hpk k r) (bvec q) z'‖ ^ 2 + bz z z' p R ^ 2 +
      ‖herm (Hpk k r) (bvec q) z'‖ * |bz z z' p R|)

theorem one_le_bnd (hT' : 0 < Tz k r z') (p q : Fin (2 * r + k + 1)) (R : ℝ) : 1 ≤ bnd z z' p q R := by
  unfold bnd
  have h0 : 0 ≤ (-(herm (Hpk k r) z' z').re)⁻¹ := inv_nonneg.mpr (le_of_lt hT')
  have h1 : 0 ≤ (-(herm (Hpk k r) z' z').re)⁻¹ * (‖herm (Hpk k r) (bvec q) z'‖ ^ 2 + bz z z' p R ^ 2 +
      ‖herm (Hpk k r) (bvec q) z'‖ * |bz z z' p R|) := mul_nonneg h0 (by positivity)
  have h2 := abs_nonneg (herm (Hpk k r) (bvec q) (bvec q)).re
  have h3 := abs_nonneg (herm (Hpk k r) (bvec p) (bvec p)).re
  linarith

theorem norm_herm_gz_le (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (R : ℝ) (hR : ‖zetaL k r z z' (Fin.last r) g‖ ≤ R)
    (p : Fin (2 * r + k + 1)) (hp : r ≤ p.val ∧ p.val ≤ r + k) :
    ‖herm (Hpk k r) (bvec p) (g *ᵥ z')‖ ≤ bz z z' p R := by
  have hzn : (herm (Hpk k r) z z).re < 0 := by unfold Tz at hT; linarith
  have h := norm_herm_le (bvec_wb p hp) hz (glev_wb hg hz') hzn
  rw [hb_UH _ hg.1] at h
  have hζ : herm (Hpk k r) (g *ᵥ z') z = zetaL k r z z' (Fin.last r) g := by
    simp only [zetaL, fvec_last]
  rw [hζ] at h
  unfold bz
  have h0 : 0 ≤ (-(herm (Hpk k r) z z).re)⁻¹ := inv_nonneg.mpr (by linarith)
  have hn0 := norm_nonneg (zetaL k r z z' (Fin.last r) g)
  have hsq : ‖zetaL k r z z' (Fin.last r) g‖ ^ 2 ≤ R ^ 2 := by nlinarith
  have hm : ‖herm (Hpk k r) (bvec p) z‖ * ‖zetaL k r z z' (Fin.last r) g‖ ≤
      ‖herm (Hpk k r) (bvec p) z‖ * R := mul_le_mul_of_nonneg_left hR (norm_nonneg _)
  have := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (le_refl (‖herm (Hpk k r) (bvec p) z‖ ^ 2)) hsq) hm) h0
  linarith

theorem norm_entry_le (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (R : ℝ) (hR : ‖zetaL k r z z' (Fin.last r) g‖ ≤ R)
    (p q : Fin (2 * r + k + 1)) : ‖g p q‖ ≤ bnd z z' p q R := by
  have h1 := one_le_bnd z z' hT' p q R
  rw [entry_eq g p q]
  by_cases hq : q.val < r ∨ r + k < q.val
  · rw [glev_fix hg q hq]
    by_cases hpq : p = q
    · subst hpq; simp [bvec]; linarith
    · simp [bvec, Pi.single_apply, hpq]; linarith
  have hq' : r ≤ q.val ∧ q.val ≤ r + k := by omega
  by_cases hp : p.val < r ∨ r + k < p.val
  · rw [glev_wb hg (bvec_wb q hq') p hp, norm_zero]; linarith
  have hp' : r ≤ p.val ∧ p.val ≤ r + k := by omega
  have hz'n : (herm (Hpk k r) (g *ᵥ z') (g *ᵥ z')).re < 0 := by
    rw [hb_UH _ hg.1]; unfold Tz at hT'; linarith
  rw [← norm_hpk_mid _ p hp', ← gn_herm_bvec_right]
  have h := norm_herm_le (glev_wb hg (bvec_wb q hq')) (glev_wb hg hz') (bvec_wb p hp') hz'n
  rw [hb_UH _ hg.1, hb_UH _ hg.1, hb_UH _ hg.1] at h
  have hb := norm_herm_gz_le z z' hz hz' hT hg R hR p hp'
  have hbabs : ‖herm (Hpk k r) (bvec p) (g *ᵥ z')‖ ≤ |bz z z' p R| := hb.trans (le_abs_self _)
  have h0 : 0 ≤ (-(herm (Hpk k r) z' z').re)⁻¹ := inv_nonneg.mpr (by unfold Tz at hT'; linarith)
  have hn0 := norm_nonneg (herm (Hpk k r) (bvec p) (g *ᵥ z'))
  have hsq : ‖herm (Hpk k r) (bvec p) (g *ᵥ z')‖ ^ 2 ≤ bz z z' p R ^ 2 := by
    have := abs_nonneg (bz z z' p R)
    nlinarith [sq_abs (bz z z' p R)]
  have hm := mul_le_mul_of_nonneg_left hbabs (norm_nonneg (herm (Hpk k r) (bvec q) z'))
  have := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (le_refl (‖herm (Hpk k r) (bvec q) z'‖ ^ 2)) hsq) hm) h0
  unfold bnd
  have := le_abs_self (herm (Hpk k r) (bvec q) (bvec q)).re
  have := le_abs_self (herm (Hpk k r) (bvec p) (bvec p)).re
  linarith

theorem isCompact_zeta_le (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (ε R : ℝ) :
    IsCompact {g : Mx k r | g ∈ Glev k r (Fin.last r) ∧ ε ≤ GGl k r z z' g ∧
      ‖zetaL k r z z' (Fin.last r) g‖ ≤ R} := by
  have hbox : IsCompact (Set.pi Set.univ fun p : Fin (2 * r + k + 1) =>
      Set.pi Set.univ fun q : Fin (2 * r + k + 1) => Metric.closedBall (0 : ℂ) (bnd z z' p q R)) :=
    isCompact_univ_pi fun p => isCompact_univ_pi fun q => isCompact_closedBall _ _
  have hcl : IsClosed {g : Mx k r | g ∈ Glev k r (Fin.last r) ∧ ε ≤ GGl k r z z' g ∧
      ‖zetaL k r z z' (Fin.last r) g‖ ≤ R} :=
    (Formalism.FourierDecayAlt.P.Qx5.Glev_closed (Fin.last r)).inter
      ((isClosed_le continuous_const (Formalism.FourierDecayAlt.P.Qx5.GGl_continuous k r z z')).inter
        (isClosed_le (continuous_norm.comp (Formalism.FourierDecayAlt.P.Qx5.zetaL_contDiff k r z z' (Fin.last r)).continuous)
          continuous_const))
  refine hbox.of_isClosed_subset hcl ?_
  rintro g ⟨hg, -, hR⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  exact fun p q => norm_entry_le z z' hz hz' hT hT' hg R hR p q

end Group

end Formalism.FourierDecayAlt.P5.HerB
