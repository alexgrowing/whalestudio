import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPfC

noncomputable section

open Matrix Formalism.MainNotions.S
open scoped ComplexOrder

namespace Formalism.L2.SG.RealObj.InfCut.PtRepPf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ}

theorem norm_sq_star (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl

theorem dframe (A B : Fr ε r k) (he : B.e = A.e) (i0 : Fin k) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hZ : IsUnit Z.det)
    (hlt : A.T * B.T * ‖(Z⁻¹ *ᵥ Pi.single (Fin.last r) 1) (Fin.last r)‖ ^ 2 < 1)
    (g : Formalism.REAL.UJ ε) (y : Fin (r + 1) → Fin n → ℂ) (t : Fin (r + 1) → ℂ) (σ : ℝ) (hσ : 0 < σ)
    (htc : t ⬝ᵥ (Z⁻¹ *ᵥ Pi.single (Fin.last r) 1) = σ)
    (hgf : ∀ b, uMat g *ᵥ fam B.e B.z b = y b) (hgw : ∀ i, i ≠ i0 → uMat g *ᵥ B.wb i = A.wb i)
    (hp1 : ∀ a b, hJ ε (fam A.e A.z a) (y b) = Z a b)
    (hp4 : ∀ i b, hJ ε (A.wb i) (y b) = if i = i0 then t b else 0)
    (sc : ℝ) (hsc : 0 < sc) :
    ∃ φ : ℂ, star φ * φ = 1 ∧
      IsDFrame ε (famSc sc A.e A.z) (famSc sc A.e B.z) (uMat g) (uMat g⁻¹) A.wb B.wb i0 i0 1
        (Matrix.diagonal fun i => if i = i0 then φ else 1) := by
  classical
  unfold IsDFrame
  set L := Fin.last r with hL
  set c := Z⁻¹ *ᵥ Pi.single L 1 with hcdef
  have hZc : Z *ᵥ c = Pi.single L 1 := by rw [hcdef, mulVec_mulVec, mul_nonsing_inv _ hZ, one_mulVec]
  obtain ⟨lam, hlam⟩ : ∃ lam : Fin (r + 1) → ℂ, lam = fun a => ((sc : ℂ) ^ (r - a.1))⁻¹ := ⟨_, rfl⟩
  have hscC : (sc : ℂ) ≠ 0 := by exact_mod_cast hsc.ne'
  have hl0 : ∀ a, lam a ≠ 0 := fun a => by rw [hlam]; exact inv_ne_zero (pow_ne_zero _ hscC)
  have hls : ∀ a, star (lam a) = lam a := fun a => by
    rw [hlam]; simp only [star_inv₀, star_pow, Complex.star_def, Complex.conj_ofReal]
  have hlL : lam L = 1 := by rw [hlam]; simp [hL]
  have hF : famSc sc A.e A.z = fun a => lam a • fam A.e A.z a := by rw [hlam]; rfl
  have hF' : famSc sc A.e B.z = fun a => lam a • fam B.e B.z a := by rw [hlam, he]; rfl
  have hgF' : ∀ b, uMat g *ᵥ famSc sc A.e B.z b = lam b • y b := fun b => by
    rw [hF', mulVec_smul, hgf]
  set Zs := Zhat ε (famSc sc A.e A.z) (famSc sc A.e B.z) (uMat g) with hZsdef
  have hZs : ∀ a b, Zs a b = lam a * lam b * Z a b := fun a b => by
    rw [hZsdef]
    show hJ ε (famSc sc A.e A.z a) (uMat g *ᵥ famSc sc A.e B.z b) = _
    rw [hgF', hF]
    simp only [hJ_smul_left, hJ_smul_right, hp1, hls]
    ring
  have hZsd : Zs = diagonal lam * Z * diagonal lam := by
    ext a b; rw [hZs, mul_diagonal, diagonal_mul]; ring
  have hDs : Zs.det ≠ 0 := by
    rw [hZsd, det_mul, det_mul, det_diagonal]
    exact mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun a _ => hl0 a) (isUnit_iff_ne_zero.1 hZ))
      (Finset.prod_ne_zero_iff.2 fun a _ => hl0 a)
  have hDl : Dl Zs (r + 1) = Zs.det := dl_top Zs
  rw [hDl]
  have hmi : uMat g * uMat g⁻¹ = 1 := uMat_mul_inv g
  have hgi : ∀ q, uMat g *ᵥ (uMat g⁻¹ *ᵥ q) = q := fun q => by rw [mulVec_mulVec, hmi, one_mulVec]
  have hpv : ∀ p q, hJ ε p (uMat g⁻¹ *ᵥ q) = hJ ε (uMat g *ᵥ p) q := fun p q => by
    rw [← hJ_UJ ε g p (uMat g⁻¹ *ᵥ q), hgi]

  obtain ⟨ν, hνdef⟩ : ∃ ν : Fin (r + 1) → ℂ, ν = fun b => adjugate Zs b L * lam b := ⟨_, rfl⟩
  have hZν : Z *ᵥ ν = Pi.single L Zs.det := by
    funext a
    have h2 : lam a * (Z *ᵥ ν) a = Zs.det * (if a = L then 1 else 0) := by
      have h := congrFun (congrFun (mul_adjugate Zs) a) L
      rw [Matrix.mul_apply, Matrix.smul_apply, one_apply, smul_eq_mul] at h
      rw [← h]
      simp only [mulVec, dotProduct, hνdef, Finset.mul_sum, hZs]
      exact Finset.sum_congr rfl fun b _ => by ring
    by_cases ha : a = L
    · rw [ha, hlL, one_mul, if_pos rfl, mul_one] at h2
      rw [ha, h2, Pi.single_eq_same]
    · rw [if_neg ha, mul_zero] at h2
      rw [Pi.single_eq_of_ne ha]
      exact (mul_eq_zero.1 h2).resolve_left (hl0 a)
  have hν : ν = Zs.det • c := by
    have : ν = Z⁻¹ *ᵥ (Z *ᵥ ν) := by rw [mulVec_mulVec, nonsing_inv_mul _ hZ, one_mulVec]
    rw [this, hZν, single_last_smul, mulVec_smul]
  obtain ⟨x', hx'v⟩ : ∃ x', xPr Zs (uMat g) (famSc sc A.e B.z) = x' := ⟨_, rfl⟩
  rw [hx'v]
  have hx'def : x' = ∑ b, ν b • y b := by
    rw [← hx'v]
    unfold xPr
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hgF', smul_smul, hνdef]
  have hPx' : ∀ i, hJ ε (A.wb i) x' = if i = i0 then Zs.det * σ else 0 := by
    intro i
    rw [hx'def, hJ_sum_right]
    simp only [hJ_smul_right, hp4]
    by_cases hi : i = i0
    · simp only [hi, if_true]
      have : ∑ b, ν b * t b = ν ⬝ᵥ t := rfl
      rw [this, hν, smul_dotProduct, dotProduct_comm, htc, smul_eq_mul]
    · simp [hi]
  have hnn : (Zs.det)⁻¹ • wCoord ε A.wb x' = Pi.single i0 (σ : ℂ) := by
    funext i
    simp only [Pi.smul_apply, wCoord, hPx', smul_eq_mul]
    by_cases hi : i = i0
    · rw [if_pos hi, hi, Pi.single_eq_same, ← mul_assoc, inv_mul_cancel₀ hDs, one_mul]
    · rw [if_neg hi, Pi.single_eq_of_ne hi, mul_zero]

  obtain ⟨ρ, hρdef⟩ : ∃ ρ : Fin (r + 1) → ℂ, ρ = fun a => adjugate Zs L a * lam a := ⟨_, rfl⟩
  obtain ⟨x, hxv⟩ : ∃ x, xUn Zs (famSc sc A.e A.z) = x := ⟨_, rfl⟩
  rw [hxv]
  have hxdef : x = ∑ a, star (ρ a) • fam A.e A.z a := by
    rw [← hxv]
    unfold xUn
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hF, hρdef]
    simp only [smul_smul, star_mul', hls, ← hL]
  have hρZ : ρ ᵥ* Z = Pi.single L Zs.det := by
    funext b
    have h2 : lam b * (ρ ᵥ* Z) b = Zs.det * (if L = b then 1 else 0) := by
      have h := congrFun (congrFun (adjugate_mul Zs) L) b
      rw [Matrix.mul_apply, Matrix.smul_apply, one_apply, smul_eq_mul] at h
      rw [← h]
      simp only [vecMul, dotProduct, hρdef, Finset.mul_sum, hZs]
      exact Finset.sum_congr rfl fun a _ => by ring
    by_cases hb : b = L
    · rw [hb, hlL, one_mul, if_pos rfl, mul_one] at h2
      rw [hb, h2, Pi.single_eq_same]
    · rw [if_neg (Ne.symm hb), mul_zero] at h2
      rw [Pi.single_eq_of_ne hb]
      exact (mul_eq_zero.1 h2).resolve_left (hl0 b)
  have hρL : ρ L = Zs.det * c L := by
    have : ρ = Pi.single L Zs.det ᵥ* Z⁻¹ := by rw [← hρZ, vecMul_vecMul, mul_nonsing_inv _ hZ, vecMul_one]
    rw [this, single_vecMul, hcdef, mulVec_single_one]
    simp [Matrix.row, Matrix.col]
  have hxy : ∀ b, hJ ε x (y b) = if b = L then Zs.det else 0 := by
    intro b
    rw [hxdef, hJ_sum_left]
    simp only [hJ_smul_left, star_star, hp1]
    have := congrFun hρZ b
    simp only [vecMul, dotProduct] at this
    rw [this, Pi.single_apply]
  have hfx : ∀ a, hJ ε (fam A.e A.z a) x = if a = L then -(A.T : ℂ) * star (ρ L) else 0 := by
    intro a
    rw [hxdef, hJ_sum_right]
    simp only [hJ_smul_right, A.gf, ← hL]
    by_cases ha : a = L
    · simp [ha, Finset.sum_ite_eq']
      ring
    · simp [ha]
  have hxx : hJ ε x x = -(A.T : ℂ) * (ρ L * star (ρ L)) := by
    calc hJ ε x x = hJ ε (∑ a, star (ρ a) • fam A.e A.z a) x := by rw [← hxdef]
      _ = -(A.T : ℂ) * (ρ L * star (ρ L)) := by
        rw [hJ_sum_left]
        simp only [hJ_smul_left, star_star, hfx, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
          if_true]
        ring

  have hwx : ∀ i, hJ ε (A.wb i) x = 0 := fun i => by
    rw [hxdef, hJ_sum_right]; simp [hJ_smul_right, A.w_fam]
  have hev : ∀ a, hJ ε (B.e a) (uMat g⁻¹ *ᵥ x) = 0 := fun a => by
    rw [hpv, ← fam_cs B.e B.z a, hgf, swapJ (hxy _), if_neg (Fin.castSucc_ne_last a), star_zero]
  have hzv : hJ ε B.z (uMat g⁻¹ *ᵥ x) = star Zs.det := by
    rw [hpv, ← fam_last B.e B.z, hgf, swapJ (hxy _), if_pos rfl]
  have hwv : ∀ i, i ≠ i0 → hJ ε (B.wb i) (uMat g⁻¹ *ᵥ x) = 0 := fun i hi => by
    rw [hpv, hgw i hi, hwx]
  obtain ⟨κ, hκdef⟩ : ∃ κ, hJ ε (B.wb i0) (uMat g⁻¹ *ᵥ x) = κ := ⟨_, rfl⟩
  have hsumv : ∑ i, hJ ε (B.wb i) (uMat g⁻¹ *ᵥ x) * star (hJ ε (B.wb i) (uMat g⁻¹ *ᵥ x)) = κ * star κ := by
    rw [Finset.sum_eq_single i0 (fun j _ hj => by rw [hwv j hj, star_zero, mul_zero]) (by simp), hκdef]
  have key := B.pair (uMat g⁻¹ *ᵥ x) (uMat g⁻¹ *ᵥ x) hev hev
  rw [hJ_UJ, hxx, hsumv, hzv, star_star, hρL] at key
  have hκ : κ ≠ 0 := by
    intro h0
    rw [h0, star_zero, mul_zero, add_zero, star_mul'] at key
    have hT'inv : (B.T : ℂ) * (B.T : ℂ)⁻¹ = 1 := mul_inv_cancel₀ B.T_ne
    have hC : star Zs.det * Zs.det * (1 - (A.T : ℂ) * B.T * (star (c L) * c L)) = 0 := by
      linear_combination (B.T : ℂ) * key - (star Zs.det * Zs.det) * hT'inv
    rw [norm_sq_star, norm_sq_star] at hC
    have hreal : ‖Zs.det‖ ^ 2 * (1 - A.T * B.T * ‖c L‖ ^ 2) = 0 := by exact_mod_cast hC
    have hpos : 0 < ‖Zs.det‖ ^ 2 * (1 - A.T * B.T * ‖c L‖ ^ 2) :=
      mul_pos (by positivity) (by linarith)
    linarith
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : ℂ, ζ = (star Zs.det)⁻¹ * κ := ⟨_, rfl⟩
  have hζ : ζ ≠ 0 := by rw [hζdef]; exact mul_ne_zero (inv_ne_zero (star_ne_zero.2 hDs)) hκ
  have hnn' : (star Zs.det)⁻¹ • wCoord ε B.wb (uMat g⁻¹ *ᵥ x) = Pi.single i0 ζ := by
    funext i
    simp only [Pi.smul_apply, wCoord, smul_eq_mul]
    by_cases hi : i = i0
    · rw [hi, hκdef, Pi.single_eq_same, hζdef]
    · rw [hwv i hi, Pi.single_eq_of_ne hi, mul_zero]
  have hnz : (‖ζ‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hζ
  obtain ⟨φ, hφdef⟩ : ∃ φ : ℂ, φ = ζ * (‖ζ‖ : ℂ)⁻¹ := ⟨_, rfl⟩
  have hφ : star φ * φ = 1 := by
    have h1 : star ζ * ζ = (‖ζ‖ : ℂ) ^ 2 := by rw [Complex.star_def, Complex.conj_mul']
    have h2 : star (‖ζ‖ : ℂ) = ‖ζ‖ := by rw [Complex.star_def, Complex.conj_ofReal]
    rw [hφdef, star_mul', star_inv₀, h2]
    field_simp
    linear_combination h1
  refine ⟨φ, hφ, one_mem _, ?_, ?_, ?_, ?_⟩
  · rw [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext i
    by_cases hi : i = i0
    · simp only [hi, if_true, Pi.star_apply]; rw [mul_comm]; exact hφ
    · simp [hi]
  · rw [hnn, eN_single, Complex.norm_of_nonneg hσ.le, one_mulVec]
    funext j
    by_cases hj : j = i0
    · subst hj; simp [hσ.ne']
    · simp [hj]
  · rw [hnn', eN_single, diagonal_mulVec_single]
    funext j
    by_cases hj : j = i0
    · subst hj; simp only [if_true, mul_one, Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, hφdef]
      push_cast; ring
    · simp [hj]
  · intro y' hf hgF
    have hf1 : ∀ a, hJ ε (fam A.e A.z a) y' = 0 := fun a => by
      have := hf a
      simp only [hF, hJ_smul_left, hls] at this
      exact (mul_eq_zero.1 this).resolve_left (hl0 a)
    have hy1 : ∀ b, hJ ε (y b) y' = 0 := fun b => by
      have := hgF b
      rw [hgF', hJ_smul_left, hls] at this
      exact (mul_eq_zero.1 this).resolve_left (hl0 b)

    have hex' : ∀ a, hJ ε (A.e a) x' = 0 := fun a => by
      rw [← fam_cs A.e A.z a, hx'def, hJ_sum_right]
      simp only [hJ_smul_right, hp1]
      have := congrFun hZν (Fin.castSucc a)
      simp only [mulVec, dotProduct] at this
      rw [show ∑ b, ν b * Z (Fin.castSucc a) b = ∑ b, Z (Fin.castSucc a) b * ν b from
        Finset.sum_congr rfl fun b _ => mul_comm _ _, this, Pi.single_eq_of_ne (Fin.castSucc_ne_last a)]
    have hey' : ∀ a, hJ ε (A.e a) y' = 0 := fun a => by rw [← fam_cs A.e A.z a]; exact hf1 _
    have hzy : hJ ε A.z y' = 0 := by rw [← fam_last A.e A.z]; exact hf1 _
    have hx'y : hJ ε x' y' = 0 := by
      rw [hx'def, hJ_sum_left]; simp [hJ_smul_left, hy1]
    have hpr := A.pair x' y' hex' hey'
    have hsum : ∑ i, hJ ε (A.wb i) y' * star (hJ ε (A.wb i) x') =
        hJ ε (A.wb i0) y' * star (Zs.det * σ) := by
      rw [Finset.sum_eq_single i0 (fun j _ hj => by rw [hPx', if_neg hj, star_zero, mul_zero]) (by simp),
        hPx', if_pos rfl]
    rw [hsum, hx'y, hzy] at hpr
    simp only [mul_zero, zero_mul, zero_add] at hpr
    have hne : star (Zs.det * (σ : ℂ)) ≠ 0 :=
      star_ne_zero.2 (mul_ne_zero hDs (by exact_mod_cast hσ.ne'))
    have hPy0 := (mul_eq_zero.1 hpr.symm).resolve_right hne

    have hev' : ∀ a, hJ ε (B.e a) (uMat g⁻¹ *ᵥ y') = 0 := fun a => by
      rw [hpv, ← fam_cs B.e B.z a, hgf]; exact hy1 _
    have hzv' : hJ ε B.z (uMat g⁻¹ *ᵥ y') = 0 := by
      rw [hpv, ← fam_last B.e B.z, hgf]; exact hy1 _
    have hvv' : hJ ε (uMat g⁻¹ *ᵥ x) (uMat g⁻¹ *ᵥ y') = 0 := by
      rw [hJ_UJ, hxdef, hJ_sum_left]; simp [hJ_smul_left, hf1]
    have hpr2 := B.pair (uMat g⁻¹ *ᵥ x) (uMat g⁻¹ *ᵥ y') hev hev'
    have hsum2 : ∑ i, hJ ε (B.wb i) (uMat g⁻¹ *ᵥ y') * star (hJ ε (B.wb i) (uMat g⁻¹ *ᵥ x)) =
        hJ ε (B.wb i0) (uMat g⁻¹ *ᵥ y') * star κ := by
      rw [Finset.sum_eq_single i0 (fun j _ hj => by rw [hwv j hj, star_zero, mul_zero]) (by simp), hκdef]
    rw [hsum2, hvv', hzv'] at hpr2
    simp only [mul_zero, zero_mul, zero_add] at hpr2
    have hPv0 := (mul_eq_zero.1 hpr2.symm).resolve_right (star_ne_zero.2 hκ)
    rw [one_mulVec, star_eq_conjTranspose, diagonal_conjTranspose]
    funext i
    rw [mulVec_diagonal]
    simp only [wCoord]
    by_cases hi : i = i0
    · rw [hi, hPv0, hPy0, mul_zero]
    · rw [hpv, hgw i hi]; simp [hi]

theorem locMain (A B : Fr ε r k) (he : B.e = A.e) (i0 : Fin k) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hG : 0 < Gv A.T B.T Z) (sc : ℝ) (hsc : 0 < sc) :
    ∃ g : Formalism.REAL.UJ ε, Zhat ε (fam A.e A.z) (fam A.e B.z) (uMat g) = Z ∧
      ∃ φ : ℂ, star φ * φ = 1 ∧
        IsDFrame ε (famSc sc A.e A.z) (famSc sc A.e B.z) (uMat g) (uMat g⁻¹) A.wb B.wb i0 i0 1
          (Matrix.diagonal fun i => if i = i0 then φ else 1) := by
  obtain ⟨hZ, hlt⟩ := gv_facts A.T_pos B.T_pos Z hG
  have hcL : (Z⁻¹ *ᵥ Pi.single (Fin.last r) 1) (Fin.last r) = Z⁻¹ (Fin.last r) (Fin.last r) := by
    simp [mulVec_single_one]
  rw [← hcL] at hlt
  set q : ℝ := (A.T)⁻¹ - B.T * ‖(Z⁻¹ *ᵥ Pi.single (Fin.last r) 1) (Fin.last r)‖ ^ 2 with hqdef
  have hq : 0 < q := by
    have h1 : A.T * q = 1 - A.T * B.T * ‖(Z⁻¹ *ᵥ Pi.single (Fin.last r) 1) (Fin.last r)‖ ^ 2 := by
      rw [hqdef, mul_sub, mul_inv_cancel₀ A.T_pos.ne', ← mul_assoc]
    have h2 : 0 < A.T * q := by rw [h1]; linarith
    exact pos_of_mul_pos_right h2 A.T_pos.le
  obtain ⟨g, y, t, htc, hgf, hgw, hp1, hp4⟩ := realize A B i0 Z hZ (Real.sqrt q) (Real.sq_sqrt hq.le)
  refine ⟨g, ?_, dframe A B he i0 Z hZ hlt g y t (Real.sqrt q) (Real.sqrt_pos.2 hq) htc hgf hgw hp1 hp4 sc hsc⟩
  ext a b
  show hJ ε (fam A.e A.z a) (uMat g *ᵥ fam A.e B.z b) = Z a b
  rw [show fam A.e B.z = fam B.e B.z by rw [he], hgf, hp1]

end Formalism.L2.SG.RealObj.InfCut.PtRepPf
