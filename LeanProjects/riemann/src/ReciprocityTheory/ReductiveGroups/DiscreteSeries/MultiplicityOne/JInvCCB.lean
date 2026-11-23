import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvCCA

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.InvCC

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section Alg

variable {k r : ℕ}

lemma lie_rsmul (t : ℝ) {X : Mat k r} (hX : inLie k r X) : inLie k r ((t : ℂ) • X) := by
  have h : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  show ((t : ℂ) • X)ᴴ * Hpk k r + Hpk k r * ((t : ℂ) • X) = 0
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
  have hs : star (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
  rw [hs, ← smul_add, h, smul_zero]

lemma lie_neg {X : Mat k r} (hX : inLie k r X) : inLie k r (-X) := by
  have h : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  show (-X)ᴴ * Hpk k r + Hpk k r * (-X) = 0
  rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, h, neg_zero]

private lemma Hpk_conjTranspose_Hpk_mul_eq_one_of_mem_GV {g : Mat k r} (hg : g ∈ GV k r) : Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, hpk_sq]

private lemma inv_eq_Hpk_conjTranspose_Hpk_of_mem_GV {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ = Hpk k r * gᴴ * Hpk k r :=
  Matrix.inv_eq_left_inv (Hpk_conjTranspose_Hpk_mul_eq_one_of_mem_GV hg)

private lemma Hpk_mul_conjTranspose_eq_neg_mul_Hpk_of_inLie {Y : Mat k r} (hY : inLie k r Y) : Hpk k r * Yᴴ = -(Y * Hpk k r) := by
  have h : Yᴴ * Hpk k r + Hpk k r * Y = 0 := hY
  have h1 : Yᴴ * Hpk k r = -(Hpk k r * Y) := eq_neg_of_add_eq_zero_left h
  calc Hpk k r * Yᴴ = Hpk k r * Yᴴ * (Hpk k r * Hpk k r) := by rw [hpk_sq, Matrix.mul_one]
    _ = Hpk k r * (Yᴴ * Hpk k r) * Hpk k r := by simp only [Matrix.mul_assoc]
    _ = -(Hpk k r * Hpk k r * Y * Hpk k r) := by
      rw [h1]; simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = -(Y * Hpk k r) := by rw [hpk_sq, Matrix.one_mul]

lemma lie_conj {P Y : Mat k r} (hP : P ∈ GV k r) (hY : inLie k r Y) : inLie k r (P * Y * P⁻¹) := by
  have key : ∀ Z : Mat k r, Hpk k r * (Yᴴ * Z) = -(Y * (Hpk k r * Z)) := by
    intro Z
    rw [← Matrix.mul_assoc, Hpk_mul_conjTranspose_eq_neg_mul_Hpk_of_inLie hY, Matrix.neg_mul, Matrix.mul_assoc]
  show (P * Y * P⁻¹)ᴴ * Hpk k r + Hpk k r * (P * Y * P⁻¹) = 0
  rw [inv_eq_Hpk_conjTranspose_Hpk_of_mem_GV hP]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hpk_conjT, Matrix.mul_assoc]
  rw [key]
  simp only [Matrix.mul_neg, neg_add_cancel]

private lemma Hpk_map_conj_eq : (Hpk k r).map (starRingEnd ℂ) = Hpk k r := by
  ext i j
  simp only [Matrix.map_apply, Hpk]
  split_ifs <;> simp

lemma lie_map_conj {Y : Mat k r} (hY : inLie k r Y) : inLie k r (Y.map (starRingEnd ℂ)) := by
  have h : Yᴴ * Hpk k r + Hpk k r * Y = 0 := hY
  show (Y.map (starRingEnd ℂ))ᴴ * Hpk k r + Hpk k r * Y.map (starRingEnd ℂ) = 0
  have e1 : (Y.map (starRingEnd ℂ))ᴴ = (Yᴴ).map (starRingEnd ℂ) := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [e1]
  conv_lhs => rw [← Hpk_map_conj_eq (k := k) (r := r)]
  rw [← Matrix.map_mul, ← Matrix.map_mul]
  ext i j
  have hij : (Yᴴ * Hpk k r) i j + (Hpk k r * Y) i j = 0 := by
    rw [← Matrix.add_apply, h, Matrix.zero_apply]
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.zero_apply, ← map_add, hij, map_zero]

private lemma mul_Hpk_conjTranspose_Hpk_eq_one_of_mem_GV {g : Mat k r} (hg : g ∈ GV k r) : g * (Hpk k r * gᴴ * Hpk k r) = 1 :=
  by
  rw [← inv_eq_Hpk_conjTranspose_Hpk_of_mem_GV hg]
  exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse (Hpk_conjTranspose_Hpk_mul_eq_one_of_mem_GV hg))

private lemma inv_mem_GV' {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ ∈ GV k r := by
  rw [inv_eq_Hpk_conjTranspose_Hpk_of_mem_GV hg]
  show (Hpk k r * gᴴ * Hpk k r)ᴴ * Hpk k r * (Hpk k r * gᴴ * Hpk k r) = Hpk k r
  have h1 := mul_Hpk_conjTranspose_Hpk_eq_one_of_mem_GV hg
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hpk_conjT, Matrix.mul_assoc] at h1 ⊢
  rw [← Matrix.mul_assoc (Hpk k r) (Hpk k r), hpk_sq, Matrix.one_mul, h1, Matrix.mul_one]

private lemma mul_mem_GV_multiplicity_one {g h : Mat k r} (hg : g ∈ GV k r) (hh : h ∈ GV k r) : g * h ∈ GV k r := by
  have e1 : gᴴ * Hpk k r * g = Hpk k r := hg
  have e2 : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [e1, e2]

private lemma map_conj_mem_GV {g : Mat k r} (hg : g ∈ GV k r) : g.map (starRingEnd ℂ) ∈ GV k r := by
  have e1 : gᴴ * Hpk k r * g = Hpk k r := hg
  show (g.map (starRingEnd ℂ))ᴴ * Hpk k r * g.map (starRingEnd ℂ) = Hpk k r
  have e2 : (g.map (starRingEnd ℂ))ᴴ = (gᴴ).map (starRingEnd ℂ) := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [e2]
  conv_lhs => rw [← Hpk_map_conj_eq (k := k) (r := r)]
  rw [← Matrix.map_mul, ← Matrix.map_mul, e1, Hpk_map_conj_eq]

lemma exp_mem {X : Mat k r} (hX : inLie k r X) : NormedSpace.exp X ∈ GV k r := by
  have h : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have hXH : Xᴴ = Hpk k r * (-X) * (Hpk k r)⁻¹ := by
    rw [Matrix.inv_eq_left_inv hpk_sq]
    have h1 : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left h
    calc Xᴴ = Xᴴ * Hpk k r * Hpk k r := by rw [Matrix.mul_assoc, hpk_sq, Matrix.mul_one]
      _ = Hpk k r * (-X) * Hpk k r := by rw [h1, Matrix.mul_neg, Matrix.neg_mul]
  have hU : IsUnit (Hpk k r) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hpk_sq)
  have hc : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl X)), neg_add_cancel,
      NormedSpace.exp_zero]
  show (NormedSpace.exp X)ᴴ * Hpk k r * NormedSpace.exp X = Hpk k r
  rw [← Matrix.exp_conjTranspose, hXH, Matrix.exp_conj _ _ hU, Matrix.inv_eq_left_inv hpk_sq,
    Matrix.mul_assoc (Hpk k r * NormedSpace.exp (-X)) (Hpk k r) (Hpk k r), hpk_sq, Matrix.mul_one,
    Matrix.mul_assoc, hc, Matrix.mul_one]

section gbar

variable {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hE : IsUnit (embWb k r γ).det)

private lemma conj_map_add (A B : Mat k r) :
    (A + B).map (starRingEnd ℂ) = A.map (starRingEnd ℂ) + B.map (starRingEnd ℂ) := by
  ext i j
  simp

private lemma conj_map_real_smul (t : ℝ) (A : Mat k r) :
    ((t : ℂ) • A).map (starRingEnd ℂ) = (t : ℂ) • A.map (starRingEnd ℂ) := by
  ext i j
  simp

private lemma conj_map_neg (A : Mat k r) : (-A).map (starRingEnd ℂ) = -A.map (starRingEnd ℂ) := by
  ext i j
  simp

private lemma conj_map_conj_map (A : Mat k r) : (A.map (starRingEnd ℂ)).map (starRingEnd ℂ) = A := by
  ext i j
  simp

lemma gbar_add (A B : Mat k r) : gbar k r γ (A + B) = gbar k r γ A + gbar k r γ B := by
  simp only [gbar, Matrix.mul_add, Matrix.add_mul, conj_map_add]

lemma gbar_rsmul (t : ℝ) (A : Mat k r) : gbar k r γ ((t : ℂ) • A) = (t : ℂ) • gbar k r γ A := by
  simp only [gbar, Matrix.mul_smul, Matrix.smul_mul, conj_map_real_smul]

lemma gbar_neg (A : Mat k r) : gbar k r γ (-A) = -gbar k r γ A := by
  simp only [gbar, Matrix.mul_neg, Matrix.neg_mul, conj_map_neg]

lemma exp_map_conj (A : Mat k r) :
    NormedSpace.exp (A.map (starRingEnd ℂ)) = (NormedSpace.exp A).map (starRingEnd ℂ) := by
  have h : ∀ B : Mat k r, B.map (starRingEnd ℂ) = (Bᴴ)ᵀ := fun B => by ext i j; simp
  rw [h, h, Matrix.exp_transpose, Matrix.exp_conjTranspose]

include hE

lemma gbar_mul (g h : Mat k r) : gbar k r γ (g * h) = gbar k r γ g * gbar k r γ h := by
  simp only [gbar]
  rw [show (embWb k r γ)⁻¹ * (g * h) * embWb k r γ =
      ((embWb k r γ)⁻¹ * g * embWb k r γ) * ((embWb k r γ)⁻¹ * h * embWb k r γ) by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left, hE], Matrix.map_mul]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left, hE]

lemma gbar_one : gbar k r γ 1 = 1 := by
  simp only [gbar, Matrix.mul_one, Matrix.nonsing_inv_mul _ hE]
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.mul_nonsing_inv _ hE]

lemma gbar_gbar (g : Mat k r) : gbar k r γ (gbar k r γ g) = g := by
  simp only [gbar, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left, Matrix.mul_nonsing_inv_cancel_left,
    Matrix.nonsing_inv_mul, Matrix.mul_nonsing_inv, Matrix.mul_one, hE, conj_map_conj_map]

lemma gbar_mul_inv {x : Mat k r} (hx : IsUnit x.det) : gbar k r γ x * gbar k r γ x⁻¹ = 1 := by
  rw [← gbar_mul hE, Matrix.mul_nonsing_inv _ hx, gbar_one hE]

lemma gbar_inv {x : Mat k r} (hx : IsUnit x.det) : gbar k r γ x⁻¹ = (gbar k r γ x)⁻¹ := (Matrix.inv_eq_right_inv (gbar_mul_inv hE hx)).symm

lemma gbar_unit {x : Mat k r} (hx : IsUnit x.det) : IsUnit (gbar k r γ x).det := Matrix.isUnit_det_of_right_inverse (gbar_mul_inv hE hx)

lemma th_mul (g h : Mat k r) : th k r γ (g * h) = th k r γ h * th k r γ g := by
  simp only [th, gbar_mul hE, Matrix.mul_inv_rev]

lemma th_th {g : Mat k r} (hg : IsUnit g.det) : th k r γ (th k r γ g) = g := by
  simp only [th]
  rw [gbar_inv hE (gbar_unit hE hg), gbar_gbar hE, Matrix.nonsing_inv_nonsing_inv _ hg]

lemma gbar_exp (A : Mat k r) : gbar k r γ (NormedSpace.exp A) = NormedSpace.exp (gbar k r γ A) := by
  have hU : IsUnit (embWb k r γ) := (Matrix.isUnit_iff_isUnit_det _).mpr hE
  simp only [gbar]
  rw [← Matrix.exp_conj' _ A hU, ← exp_map_conj, Matrix.exp_conj _ _ hU]

lemma th_exp (A : Mat k r) : th k r γ (NormedSpace.exp A) = NormedSpace.exp (-(gbar k r γ A)) := by
  simp only [th]
  rw [gbar_exp hE, Matrix.exp_neg]

variable (hEG : embWb k r γ ∈ GV k r)
include hEG

lemma lie_gbar {X : Mat k r} (hX : inLie k r X) : inLie k r (gbar k r γ X) := by
  have hEi : (embWb k r γ)⁻¹ ∈ GV k r := inv_mem_GV' hEG
  have h1 : inLie k r ((embWb k r γ)⁻¹ * X * embWb k r γ) := by
    have h2 := lie_conj hEi hX
    rwa [Matrix.nonsing_inv_nonsing_inv _ hE] at h2
  exact lie_conj hEG (lie_map_conj h1)

lemma gbar_mem {g : Mat k r} (hg : g ∈ GV k r) : gbar k r γ g ∈ GV k r := mul_mem_GV_multiplicity_one (mul_mem_GV_multiplicity_one hEG (map_conj_mem_GV (mul_mem_GV_multiplicity_one (mul_mem_GV_multiplicity_one (inv_mem_GV' hEG) hg) hEG)))
    (inv_mem_GV' hEG)

lemma th_mem {g : Mat k r} (hg : g ∈ GV k r) : th k r γ g ∈ GV k r := inv_mem_GV' (gbar_mem hE hEG hg)

lemma th_eq {g : Mat k r} (hg : g ∈ GV k r) : th k r γ g = Hpk k r * (gbar k r γ g)ᴴ * Hpk k r := inv_eq_Hpk_conjTranspose_Hpk_of_mem_GV (gbar_mem hE hEG hg)

end gbar

end Alg

open Formalism.REAL
open Filter Topology
open scoped ContDiff

section Linfty

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra Matrix.linftyOpNormedSpace

lemma hasDerivAt_exp_linfty {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 := by
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℂ) X ((0 : ℝ) : ℂ))
  have h2 := h.scomp (x := (0:ℝ)) Complex.ofRealCLM.hasDerivAt
  exact h2.congr_deriv (by simp)

end Linfty

lemma slope_exp {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (slope (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) 0) (𝓝[≠] 0) (𝓝 X) := by
  let _ := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℂ) (n := Fin n) (α := ℂ)
  let _ := Matrix.linftyOpNormedSpace (R := ℝ) (m := Fin n) (n := Fin n) (α := ℂ)
  exact (hasDerivAt_exp_linfty X).tendsto_slope

lemma slope_curveR {n : ℕ} (g X : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (slope (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0) (𝓝[≠] 0) (𝓝 (g * X)) := by
  have hm : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => g * M) := continuous_const.mul continuous_id
  refine ((hm.tendsto X).comp (slope_exp X)).congr' ?_
  filter_upwards with t
  simp only [Function.comp_apply, slope_def_module, Matrix.mul_sub, Matrix.mul_smul]

lemma slope_curveL {n : ℕ} (g X : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (slope (fun t : ℝ => NormedSpace.exp (-((t : ℂ) • X)) * g) 0) (𝓝[≠] 0) (𝓝 (-(X * g))) := by
  have h := (slope_exp (-X)).mul_const g
  rw [Matrix.neg_mul] at h
  refine h.congr (fun t => ?_)
  simp only [slope_def_module, Matrix.sub_mul, Matrix.smul_mul, smul_neg]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma hasDerivAt_curveR (g X : Mat k r) :
    HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 := hasDerivAt_iff_tendsto_slope.mpr (slope_curveR g X)

lemma hasDerivAt_curveL (g X : Mat k r) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (-((t : ℂ) • X)) * g) (-(X * g)) 0 := hasDerivAt_iff_tendsto_slope.mpr (slope_curveL g X)

def mulR (X : Mat k r) : Mat k r →L[ℝ] Mat k r := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)

def mulL (X : Mat k r) : Mat k r →L[ℝ] Mat k r := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ X)

lemma expL_mem {X : Mat k r} (hX : inLie k r X) (t : ℝ) {g : Mat k r} (hg : g ∈ GV k r) :
    NormedSpace.exp (-((t : ℂ) • X)) * g ∈ GV k r := by
  have h1 : inLie k r (-((t : ℂ) • X)) := lie_neg (lie_rsmul t hX)
  exact mul_mem_GV_multiplicity_one (exp_mem h1) hg

lemma expR_mem {X : Mat k r} (hX : inLie k r X) (t : ℝ) {g : Mat k r} (hg : g ∈ GV k r) :
    g * NormedSpace.exp ((t : ℂ) • X) ∈ GV k r := mul_mem_GV_multiplicity_one hg (exp_mem (lie_rsmul t hX))

lemma LdV_congr {f₁ f₂ : Mat k r → ℂ} (h : ∀ g ∈ GV k r, f₁ g = f₂ g) {X : Mat k r} (hX : inLie k r X)
    {g : Mat k r} (hg : g ∈ GV k r) : LdV X f₁ g = LdV X f₂ g := by
  show deriv (fun t : ℝ => f₁ (NormedSpace.exp (-((t : ℂ) • X)) * g)) 0 =
    deriv (fun t : ℝ => f₂ (NormedSpace.exp (-((t : ℂ) • X)) * g)) 0
  congr 1
  funext t
  exact h _ (expL_mem hX t hg)

lemma RdV_congr {f₁ f₂ : Mat k r → ℂ} (h : ∀ g ∈ GV k r, f₁ g = f₂ g) {X : Mat k r} (hX : inLie k r X)
    {g : Mat k r} (hg : g ∈ GV k r) : RdV X f₁ g = RdV X f₂ g := by
  show deriv (fun t : ℝ => f₁ (g * NormedSpace.exp ((t : ℂ) • X))) 0 =
    deriv (fun t : ℝ => f₂ (g * NormedSpace.exp ((t : ℂ) • X))) 0
  congr 1
  funext t
  exact h _ (expR_mem hX t hg)

lemma LdV_eq {f f' : Mat k r → ℂ} {U : Set (Mat k r)} (hU : IsOpen U) {g : Mat k r} (hgU : g ∈ U)
    (hg : g ∈ GV k r) (hd : DifferentiableAt ℝ f' g) (hff : ∀ h ∈ U, h ∈ GV k r → f h = f' h)
    {X : Mat k r} (hX : inLie k r X) : LdV X f g = fderiv ℝ f' g (-(X * g)) := by
  have hc := hasDerivAt_curveL g X
  have hc0 : NormedSpace.exp (-(((0 : ℝ) : ℂ) • X)) * g = g := by simp
  have hd' : DifferentiableAt ℝ f' (NormedSpace.exp (-(((0 : ℝ) : ℂ) • X)) * g) := by rw [hc0]; exact hd
  have hcomp := hd'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
  have hev : (fun t : ℝ => f (NormedSpace.exp (-((t : ℂ) • X)) * g)) =ᶠ[𝓝 0]
      (f' ∘ fun t : ℝ => NormedSpace.exp (-((t : ℂ) • X)) * g) := by
    have hU' : ∀ᶠ (t : ℝ) in 𝓝 (0 : ℝ), NormedSpace.exp (-((t : ℂ) • X)) * g ∈ U :=
      hc.continuousAt.preimage_mem_nhds (by
        simp only [Complex.ofReal_zero, zero_smul, neg_zero, NormedSpace.exp_zero, Matrix.one_mul]
        exact hU.mem_nhds hgU)
    filter_upwards [hU'] with t ht
    exact hff _ ht (expL_mem hX t hg)
  show deriv (fun t : ℝ => f (NormedSpace.exp (-((t : ℂ) • X)) * g)) 0 = _
  rw [hev.deriv_eq, hcomp.deriv, hc0]
  rfl

lemma RdV_eq {f f' : Mat k r → ℂ} {U : Set (Mat k r)} (hU : IsOpen U) {g : Mat k r} (hgU : g ∈ U)
    (hg : g ∈ GV k r) (hd : DifferentiableAt ℝ f' g) (hff : ∀ h ∈ U, h ∈ GV k r → f h = f' h)
    {X : Mat k r} (hX : inLie k r X) : RdV X f g = fderiv ℝ f' g (g * X) := by
  have hc := hasDerivAt_curveR g X
  have hc0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp
  have hd' : DifferentiableAt ℝ f' (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by rw [hc0]; exact hd
  have hcomp := hd'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc
  have hev : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (f' ∘ fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) := by
    have hU' : ∀ᶠ (t : ℝ) in 𝓝 (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
      hc.continuousAt.preimage_mem_nhds (by
        simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
        exact hU.mem_nhds hgU)
    filter_upwards [hU'] with t ht
    exact hff _ ht (expR_mem hX t hg)
  show deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0 = _
  rw [hev.deriv_eq, hcomp.deriv, hc0]
  rfl

lemma cast_succ_le (m : ℕ) : ((m : ℕ∞) : WithTop ℕ∞) + 1 ≤ (((m + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) := by
  norm_cast

lemma one_le_cast_succ (m : ℕ) : (((m + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  exact_mod_cast Nat.succ_ne_zero m

lemma CkOn_mono {m m' : ℕ} (h : m' ≤ m) {f : Mat k r → ℂ} (hf : CkOn (m : ℕ∞) (GV k r) f) :
    CkOn (m' : ℕ∞) (GV k r) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g₀ hg₀
  exact ⟨U, f', hU, hgU, hc.of_le (by exact_mod_cast h), hff⟩

lemma CkOn_LdV {m : ℕ} {f : Mat k r → ℂ} (hf : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f) {X : Mat k r}
    (hX : inLie k r X) : CkOn (m : ℕ∞) (GV k r) (LdV X f) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, h0, hc, he⟩ := hf g₀ hg₀
  refine ⟨U, fun h => fderiv ℝ f' h (-(mulL X h)), hU, h0, ?_, ?_⟩
  · have h1 := hc.fderiv_of_isOpen hU (cast_succ_le m)
    have h2 : ContDiffOn ℝ ((m : ℕ∞) : WithTop ℕ∞) (fun h : Mat k r => -(mulL X h)) U :=
      (mulL X).contDiff.neg.contDiffOn
    exact h1.clm_apply h2
  · intro h hh hG
    exact LdV_eq hU hh hG ((hc.differentiableOn (one_le_cast_succ m)).differentiableAt (hU.mem_nhds hh)) he hX

lemma CkOn_RdV {m : ℕ} {f : Mat k r → ℂ} (hf : CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f) {X : Mat k r}
    (hX : inLie k r X) : CkOn (m : ℕ∞) (GV k r) (RdV X f) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, h0, hc, he⟩ := hf g₀ hg₀
  refine ⟨U, fun h => fderiv ℝ f' h (mulR X h), hU, h0, ?_, ?_⟩
  · have h1 := hc.fderiv_of_isOpen hU (cast_succ_le m)
    have h2 : ContDiffOn ℝ ((m : ℕ∞) : WithTop ℕ∞) (fun h : Mat k r => mulR X h) U :=
      (mulR X).contDiff.contDiffOn
    exact h1.clm_apply h2
  · intro h hh hG
    exact RdV_eq hU hh hG ((hc.differentiableOn (one_le_cast_succ m)).differentiableAt (hU.mem_nhds hh)) he hX

lemma LR_comm {f : Mat k r → ℂ} (hf : CkOn ((2 : ℕ) : ℕ∞) (GV k r) f) {X Y : Mat k r} (hX : inLie k r X)
    (hY : inLie k r Y) {g : Mat k r} (hg : g ∈ GV k r) : LdV X (RdV Y f) g = RdV Y (LdV X f) g := by
  obtain ⟨U, f', hU, h0, hc, he⟩ := hf g hg
  have hd1 : ∀ h ∈ U, DifferentiableAt ℝ f' h := fun h hh =>
    (hc.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hh)
  have hc1 := hc.fderiv_of_isOpen (m := 1) hU (by norm_num)
  have hd2 : DifferentiableAt ℝ (fderiv ℝ f') g :=
    (hc1.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds h0)
  have eφ : ∀ h ∈ U, h ∈ GV k r → RdV Y f h = (fun h => fderiv ℝ f' h (h * Y)) h :=
    fun h hh hG => RdV_eq hU hh hG (hd1 h hh) he hY
  have eψ : ∀ h ∈ U, h ∈ GV k r → LdV X f h = (fun h => fderiv ℝ f' h (-(X * h))) h :=
    fun h hh hG => LdV_eq hU hh hG (hd1 h hh) he hX
  have Dφ : DifferentiableAt ℝ (fun h => fderiv ℝ f' h (h * Y)) g :=
    (hd2.hasFDerivAt.clm_apply (mulR Y).hasFDerivAt).differentiableAt
  have Dψ : DifferentiableAt ℝ (fun h => fderiv ℝ f' h (-(X * h))) g :=
    (hd2.hasFDerivAt.clm_apply (mulL X).hasFDerivAt.neg).differentiableAt
  have hdφ : ∀ W, fderiv ℝ (fun h => fderiv ℝ f' h (h * Y)) g W =
      fderiv ℝ (fderiv ℝ f') g W (g * Y) + fderiv ℝ f' g (W * Y) := by
    intro W
    have H := (hd2.hasFDerivAt.clm_apply (mulR Y).hasFDerivAt).fderiv
    erw [H]
    exact add_comm _ _
  have hdψ : ∀ W, fderiv ℝ (fun h => fderiv ℝ f' h (-(X * h))) g W =
      fderiv ℝ (fderiv ℝ f') g W (-(X * g)) + fderiv ℝ f' g (-(X * W)) := by
    intro W
    have H := (hd2.hasFDerivAt.clm_apply (mulL X).hasFDerivAt.neg).fderiv
    erw [H]
    exact add_comm _ _
  have hs : IsSymmSndFDerivAt ℝ f' g := (hc.contDiffAt (hU.mem_nhds h0)).isSymmSndFDerivAt
    (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num)
  rw [LdV_eq hU h0 hg Dφ eφ hX, RdV_eq hU h0 hg Dψ eψ hY, hdφ, hdψ,
    show -(X * g) * Y = -(X * (g * Y)) by rw [Matrix.neg_mul, Matrix.mul_assoc]]
  erw [hs (-(X * g)) (g * Y)]
  exact rfl

end ReciprocityTheory.ChartRestriction.DS.Mult1.InvCC
