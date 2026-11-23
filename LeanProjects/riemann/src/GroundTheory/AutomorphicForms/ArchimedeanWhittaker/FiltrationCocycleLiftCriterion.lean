import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.Frechet
import GroundTheory.AutomorphicForms.HarishChandraRegularity
import GroundTheory.AutomorphicForms.RealGroupsKAK

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

abbrev FiltrationCocycleLiftCriterion : Subgroup (GL (Fin 2) ℝ) := ⊤

abbrev gl2 : Submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ) := ⊤

theorem hGL2 : IsExpLieAlgebra FiltrationCocycleLiftCriterion gl2 := isExpLieAlgebra_top

noncomputable def toGL (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.det ≠ 0) : FiltrationCocycleLiftCriterion :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hA, Subgroup.mem_top _⟩

@[simp] theorem coe_toGL (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.det ≠ 0) :
    (((toGL A hA : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = A := rfl

theorem GL2_ext {g g' : FiltrationCocycleLiftCriterion}
    (h : ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = ((g' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) :
    g = g' := Subtype.ext (Units.ext h)

noncomputable def nMat (x : ℝ) : FiltrationCocycleLiftCriterion := toGL !![1, x; 0, 1] (by simp)

noncomputable def kMat (θ : ℝ) : FiltrationCocycleLiftCriterion :=
  toGL !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] (by
    simp [Matrix.det_fin_two_of]; nlinarith [Real.sin_sq_add_cos_sq θ])

noncomputable def aT (t : ℝ) : FiltrationCocycleLiftCriterion :=
  toGL !![Real.exp t, 0; 0, Real.exp (-t)] (by
    simp [Matrix.det_fin_two_of, ← Real.exp_add])

noncomputable def zPos (s : ℝ) : FiltrationCocycleLiftCriterion :=
  toGL !![Real.exp s, 0; 0, Real.exp s] (by
    simp [Matrix.det_fin_two_of])

noncomputable def eps : FiltrationCocycleLiftCriterion := toGL !![1, 0; 0, -1] (by simp [Matrix.det_fin_two_of])

@[simp] theorem coe_nMat (x : ℝ) :
    (((nMat x : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, x; 0, 1] := rfl
@[simp] theorem coe_kMat (θ : ℝ) : (((kMat θ : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := rfl
@[simp] theorem coe_aT (t : ℝ) : (((aT t : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![Real.exp t, 0; 0, Real.exp (-t)] := rfl
@[simp] theorem coe_zPos (s : ℝ) : (((zPos s : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![Real.exp s, 0; 0, Real.exp s] := rfl
@[simp] theorem coe_eps : (((eps : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![1, 0; 0, -1] := rfl

theorem nMat_add (x y : ℝ) : nMat (x + y) = nMat x * nMat y := by
  apply GL2_ext; simp only [Subgroup.coe_mul, Units.val_mul, coe_nMat]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem kMat_add (a b : ℝ) : kMat (a + b) = kMat a * kMat b := by
  apply GL2_ext; simp only [Subgroup.coe_mul, Units.val_mul, coe_kMat]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

theorem aT_add (s t : ℝ) : aT (s + t) = aT s * aT t := by
  apply GL2_ext; simp only [Subgroup.coe_mul, Units.val_mul, coe_aT]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Real.exp_add]
  ring_nf

theorem kMat_zero : kMat 0 = 1 := by
  apply GL2_ext; simp only [coe_kMat, Subgroup.coe_one, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem kMat_two_pi : kMat (2 * Real.pi) = 1 := by
  apply GL2_ext; simp only [coe_kMat, Subgroup.coe_one, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem eps_mul_eps : eps * eps = 1 := by
  apply GL2_ext; simp only [Subgroup.coe_mul, Units.val_mul, coe_eps, Subgroup.coe_one, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem eps_inv : eps⁻¹ = eps := inv_eq_of_mul_eq_one_right eps_mul_eps

theorem eps_kMat_eps (θ : ℝ) : eps * kMat θ * eps = kMat (-θ) := by
  apply GL2_ext; simp only [Subgroup.coe_mul, Units.val_mul, coe_eps, coe_kMat]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem eps_nMat_eps (x : ℝ) : eps * nMat x * eps = nMat (-x) := by
  apply GL2_ext; simp only [Subgroup.coe_mul, Units.val_mul, coe_eps, coe_nMat]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem eps_aT_eps (t : ℝ) : eps * aT t * eps = aT t := by
  apply GL2_ext; simp only [Subgroup.coe_mul, Units.val_mul, coe_eps, coe_aT]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem zPos_mul_comm (s : ℝ) (g : FiltrationCocycleLiftCriterion) : zPos s * g = g * zPos s := by
  apply GL2_ext; simp only [Subgroup.coe_mul, Units.val_mul, coe_zPos]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

def lE : gl2 := ⟨!![0, 1; 0, 0], Submodule.mem_top⟩

def lF : gl2 := ⟨!![0, 0; 1, 0], Submodule.mem_top⟩

def lH : gl2 := ⟨!![1, 0; 0, -1], Submodule.mem_top⟩

def lW : gl2 := ⟨!![0, 1; -1, 0], Submodule.mem_top⟩

@[simp] theorem coe_lE : ((lE : gl2) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; 0, 0] := rfl
@[simp] theorem coe_lF : ((lF : gl2) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 0; 1, 0] := rfl
@[simp] theorem coe_lH : ((lH : gl2) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; 0, -1] := rfl
@[simp] theorem coe_lW : ((lW : gl2) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; -1, 0] := rfl

theorem lW_eq : lW = lE - lF := by
  apply Subtype.ext
  simp only [coe_lW, Submodule.coe_sub, coe_lE, coe_lF]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem exp_eq_of_hasDerivAt {X : Matrix (Fin 2) (Fin 2) ℝ} {c : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hc : ∀ t, HasDerivAt c (X * c t) t) (h0 : c 0 = 1) (t : ℝ) : exp (t • X) = c t := by
  have hcomm : ∀ s : ℝ, exp (s • X) * X = X * exp (s • X) := fun s =>
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) X s).unique (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X s)
  set D : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun s => exp ((-s) • X) * c s with hD
  have hDd : ∀ s, HasDerivAt D 0 s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => exp ((-s) • X)) ((-1 : ℝ) • (X * exp ((-s) • X))) s :=
      (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X (-s)).scomp s (hasDerivAt_neg s)
    have h2 := h1.mul (hc s)
    refine h2.congr_deriv ?_
    rw [neg_one_smul, neg_mul, ← mul_assoc, hcomm, mul_assoc, neg_add_cancel]
  have hconst : D t = D 0 := is_const_of_deriv_eq_zero
    (fun s => (hDd s).differentiableAt) (fun s => (hDd s).deriv) t 0
  have hD0 : D 0 = 1 := by simp [hD, h0]
  have hinv : exp (t • X) * exp ((-t) • X) = 1 := by
    rw [← exp_add_of_commute' ℝ ((Commute.refl X).smul_left t |>.smul_right (-t)), ← add_smul,
      add_neg_cancel, zero_smul, exp_zero]
  calc exp (t • X) = exp (t • X) * D t := by rw [hconst, hD0, mul_one]
    _ = exp (t • X) * exp ((-t) • X) * c t := by simp [hD, mul_assoc]
    _ = c t := by rw [hinv, one_mul]

theorem expG_lE (t : ℝ) : hGL2.expG (t • lE) = nMat t := by
  apply GL2_ext
  rw [IsExpLieAlgebra.coe_expG, coe_nMat, Submodule.coe_smul, coe_lE]
  have hc : ∀ s : ℝ, HasDerivAt (fun s : ℝ => (1 : Matrix (Fin 2) (Fin 2) ℝ) + s • !![0, 1; 0, 0])
      (!![0, 1; 0, 0] * (1 + s • !![0, 1; 0, 0])) s := by
    intro s
    refine (((hasDerivAt_id s).smul_const (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)).const_add 1).congr_deriv ?_
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [exp_eq_of_hasDerivAt hc (by simp) t]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem expG_lW (θ : ℝ) : hGL2.expG (θ • lW) = kMat θ := by
  apply GL2_ext
  rw [IsExpLieAlgebra.coe_expG, coe_kMat, Submodule.coe_smul, coe_lW]
  have hc : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Real.cos s • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      Real.sin s • !![0, 1; -1, 0])
      (!![0, 1; -1, 0] * (Real.cos s • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Real.sin s • !![0, 1; -1, 0])) s := by
    intro s
    refine (((Real.hasDerivAt_cos s).smul_const (1 : Matrix (Fin 2) (Fin 2) ℝ)).add
      ((Real.hasDerivAt_sin s).smul_const (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ))).congr_deriv ?_
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [exp_eq_of_hasDerivAt hc (by simp) θ]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem expG_lH (s : ℝ) : hGL2.expG (s • lH) = aT s := by
  apply GL2_ext
  rw [IsExpLieAlgebra.coe_expG, coe_aT, Submodule.coe_smul, coe_lH]
  have hc : ∀ u : ℝ, HasDerivAt (fun u : ℝ => Real.exp u • (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) +
      Real.exp (-u) • !![0, 0; 0, 1])
      (!![1, 0; 0, -1] * (Real.exp u • (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) +
        Real.exp (-u) • !![0, 0; 0, 1])) u := by
    intro u
    refine (((Real.hasDerivAt_exp u).smul_const (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)).add
      (((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).smul_const
        (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ))).congr_deriv ?_
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [exp_eq_of_hasDerivAt hc (by ext i j; fin_cases i <;> fin_cases j <;> simp) s]
  ext i j; fin_cases i <;> fin_cases j <;> simp

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

def lS : gl2 := ⟨!![0, 1; 1, 0], Submodule.mem_top⟩

@[simp] theorem coe_lS : ((lS : gl2) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; 1, 0] := rfl

theorem lS_eq : lS = lE + lF := by
  apply Subtype.ext
  simp only [coe_lS, Submodule.coe_add, coe_lE, coe_lF]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem aT_inv (t : ℝ) : (aT t)⁻¹ = aT (-t) := by
  rw [inv_eq_iff_mul_eq_one, ← aT_add, add_neg_cancel]
  apply GL2_ext; simp only [coe_aT, Subgroup.coe_one, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem kMat_inv (θ : ℝ) : (kMat θ)⁻¹ = kMat (-θ) := by
  rw [inv_eq_iff_mul_eq_one, ← kMat_add, add_neg_cancel, kMat_zero]

theorem zPos_inv (s : ℝ) : (zPos s)⁻¹ = zPos (-s) := by
  rw [inv_eq_iff_mul_eq_one]
  apply GL2_ext; simp only [Subgroup.coe_mul, Units.val_mul, coe_zPos, Subgroup.coe_one, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]

theorem coe_Ad_GL2 (g : FiltrationCocycleLiftCriterion) (X : gl2) : ((hGL2.Ad g X : gl2) : Matrix (Fin 2) (Fin 2) ℝ) =
    ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * X *
      (((g⁻¹ : FiltrationCocycleLiftCriterion) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := rfl

theorem Ad_aT_lE (t : ℝ) : hGL2.Ad (aT t) lE = Real.exp (2 * t) • lE := by
  apply Subtype.ext
  rw [coe_Ad_GL2, aT_inv, Submodule.coe_smul, coe_aT, coe_aT, coe_lE]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add]
  ring_nf

theorem Ad_kMat_lH (θ : ℝ) :
    hGL2.Ad (kMat θ) lH = Real.cos (2 * θ) • lH - Real.sin (2 * θ) • lS := by
  apply Subtype.ext
  rw [coe_Ad_GL2, kMat_inv, Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_smul, coe_kMat,
    coe_kMat, coe_lH, coe_lS]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_two_mul, Real.sin_two_mul] <;>
    nlinarith [Real.sin_sq_add_cos_sq θ]

theorem Ad_kMat_lS (θ : ℝ) :
    hGL2.Ad (kMat θ) lS = Real.sin (2 * θ) • lH + Real.cos (2 * θ) • lS := by
  apply Subtype.ext
  rw [coe_Ad_GL2, kMat_inv, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, coe_kMat,
    coe_kMat, coe_lH, coe_lS]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_two_mul, Real.sin_two_mul] <;>
    nlinarith [Real.sin_sq_add_cos_sq θ]

theorem Ad_eps_lH : hGL2.Ad eps lH = lH := by
  apply Subtype.ext
  rw [coe_Ad_GL2, eps_inv, coe_eps, coe_lH]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem Ad_eps_lS : hGL2.Ad eps lS = -lS := by
  apply Subtype.ext
  rw [coe_Ad_GL2, eps_inv, coe_eps, Submodule.coe_neg, coe_lS]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem Ad_eps_lE : hGL2.Ad eps lE = -lE := by
  apply Subtype.ext
  rw [coe_Ad_GL2, eps_inv, coe_eps, Submodule.coe_neg, coe_lE]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem Ad_zPos (s : ℝ) (X : gl2) : hGL2.Ad (zPos s) X = X := by
  apply Subtype.ext
  rw [coe_Ad_GL2, zPos_inv, coe_zPos, coe_zPos]
  have e : ∀ u : ℝ, (!![Real.exp u, 0; 0, Real.exp u] : Matrix (Fin 2) (Fin 2) ℝ) =
      Real.exp u • (1 : Matrix (Fin 2) (Fin 2) ℝ) := fun u => by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [e, e, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_smul, ← Real.exp_add,
    neg_add_cancel, Real.exp_zero, one_smul]

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

theorem exists_cos_sin {p r : ℝ} (h : p ^ 2 + r ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = p ∧ Real.sin θ = r := by
  set z : ℂ := ⟨p, r⟩ with hz
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply]; simp [hz]; nlinarith
  have hz0 : z ≠ 0 := by intro h0; rw [h0, norm_zero] at hn; norm_num at hn
  refine ⟨Complex.arg z, ?_, ?_⟩
  · rw [Complex.cos_arg hz0, hn, div_one]
  · rw [Complex.sin_arg, hn, div_one]

theorem exists_iwasawa (g : FiltrationCocycleLiftCriterion)
    (hg : 0 < (((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)).det) :
    ∃ s x t θ : ℝ, g = zPos s * nMat x * aT t * kMat θ := by
  set A := ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) with hA
  set a := A 0 0
  set b := A 0 1
  set c := A 1 0
  set d := A 1 1
  have hdet : A.det = a * d - b * c := Matrix.det_fin_two A
  have hcd : 0 < c ^ 2 + d ^ 2 := by
    by_contra hle
    have hc : c = 0 := by nlinarith [sq_nonneg c, sq_nonneg d]
    have hd : d = 0 := by nlinarith [sq_nonneg c, sq_nonneg d]
    rw [hdet, hc, hd] at hg; simp at hg
  set r := Real.sqrt (c ^ 2 + d ^ 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hcd
  have hr2 : r ^ 2 = c ^ 2 + d ^ 2 := Real.sq_sqrt hcd.le
  obtain ⟨θ, hcos, hsin⟩ := exists_cos_sin (p := d / r) (r := -c / r) (by
    field_simp; rw [hr2]; ring)
  set α := A.det / r with hα
  have hα0 : 0 < α := div_pos hg hr0
  set β := (a * c + b * d) / r with hβ
  refine ⟨(Real.log α + Real.log r) / 2, β / r, (Real.log α - Real.log r) / 2, θ, ?_⟩
  have hB : g * kMat (-θ) = zPos ((Real.log α + Real.log r) / 2) * nMat (β / r) *
      aT ((Real.log α - Real.log r) / 2) := by
    apply GL2_ext
    simp only [Subgroup.coe_mul, Units.val_mul, coe_kMat, coe_zPos, coe_nMat, coe_aT, ← hA,
      Real.cos_neg, Real.sin_neg, hcos, hsin]
    have e1 : Real.exp ((Real.log α + Real.log r) / 2) * Real.exp ((Real.log α - Real.log r) / 2) = α := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_log hα0
    have e2 : Real.exp ((Real.log α + Real.log r) / 2) * Real.exp (-((Real.log α - Real.log r) / 2)) = r := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_log hr0
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    · rw [e1, hα, hdet]; field_simp; ring
    · rw [mul_assoc, mul_comm (β / r), ← mul_assoc, e2, hβ]; field_simp; ring
    · field_simp; ring
    · rw [e2]; field_simp; rw [hr2]; ring
  calc g = g * kMat (-θ) * kMat θ := by rw [mul_assoc, ← kMat_add, neg_add_cancel, kMat_zero, mul_one]
    _ = _ := by rw [hB]

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

theorem orthogonal_cases {O : Matrix (Fin 2) (Fin 2) ℝ} (hO : O ∈ Matrix.unitaryGroup (Fin 2) ℝ) :
    ∃ θ : ℝ, O = !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] ∨
      O = !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] * !![1, 0; 0, -1] := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hO
  set p := O 0 0
  set q := O 0 1
  set r := O 1 0
  set s := O 1 1
  have h00 := congrFun (congrFun hO 0) 0
  have h01 := congrFun (congrFun hO 0) 1
  have h11 := congrFun (congrFun hO 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h11

  have e1 : p ^ 2 + r ^ 2 = 1 := by nlinarith
  have e2 : p * q + r * s = 0 := by nlinarith
  have e3 : q ^ 2 + s ^ 2 = 1 := by nlinarith
  obtain ⟨θ, hc, hs⟩ := exists_cos_sin (p := p) (r := -r) (by nlinarith)
  set μ := p * s - q * r with hμ
  have hq : q = -μ * r := by linear_combination p * e2 - q * e1 + r * hμ
  have hs' : s = μ * p := by linear_combination r * e2 - s * e1 - p * hμ
  have hμ2 : μ ^ 2 = 1 := by
    have : μ ^ 2 * (p ^ 2 + r ^ 2) = q ^ 2 + s ^ 2 := by rw [hq, hs']; ring
    rwa [e1, e3, mul_one] at this
  have hμ' : μ = 1 ∨ μ = -1 := by
    have : (μ - 1) * (μ + 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  refine ⟨θ, ?_⟩
  rcases hμ' with h1 | h1
  · left
    ext i j; fin_cases i <;> fin_cases j <;> simp
    · exact hc.symm
    · show q = Real.sin θ; rw [hq, h1, hs]; ring
    · show r = -Real.sin θ; rw [hs]; ring
    · show s = Real.cos θ; rw [hs', h1, hc]; ring
  · right
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · exact hc.symm
    · show q = -Real.sin θ; rw [hq, h1, hs]; ring
    · show r = -Real.sin θ; rw [hs]; ring
    · show s = -Real.cos θ; rw [hs', h1, hc]; ring

def iotaMat (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; 0, -1] * Aᵀ * !![1, 0; 0, -1]

theorem det_iotaMat (A : Matrix (Fin 2) (Fin 2) ℝ) : (iotaMat A).det = A.det := by
  rw [iotaMat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  simp [Matrix.det_fin_two_of]

noncomputable def iotaG (g : FiltrationCocycleLiftCriterion) : FiltrationCocycleLiftCriterion :=
  toGL (iotaMat ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
    (by rw [det_iotaMat]; exact (Matrix.GeneralLinearGroup.det_ne_zero (g : GL (Fin 2) ℝ)))

theorem iotaG_mul (g g' : FiltrationCocycleLiftCriterion) : iotaG (g * g') = iotaG g' * iotaG g := by
  apply GL2_ext
  simp only [iotaG, coe_toGL, Subgroup.coe_mul, Units.val_mul, iotaMat, Matrix.transpose_mul]
  have e : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 0; 0, -1] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) !![1, 0; 0, -1], e,
    Matrix.one_mul]

theorem iotaG_kMat (θ : ℝ) : iotaG (kMat θ) = kMat θ := by
  apply GL2_ext
  simp only [iotaG, coe_toGL, coe_kMat]
  ext i j
  simp only [iotaMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem iotaG_diag (d₁ d₂ : ℝ) (hd : (!![d₁, 0; 0, d₂] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0) :
    iotaG (toGL !![d₁, 0; 0, d₂] hd) = toGL !![d₁, 0; 0, d₂] hd := by
  apply GL2_ext
  simp only [iotaG, coe_toGL]
  ext i j
  simp only [iotaMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem exists_kak (g : FiltrationCocycleLiftCriterion) : ∃ (α β : ℝ) (D : FiltrationCocycleLiftCriterion), iotaG D = D ∧ g = kMat α * D * kMat β := by
  obtain ⟨k₁, k₂, a, -, hg⟩ := exists_KAK (g : GL (Fin 2) ℝ)
  obtain ⟨θ₁, h₁⟩ := orthogonal_cases k₁.2
  obtain ⟨θ₂, h₂⟩ := orthogonal_cases k₂.2
  simp only [RCLike.ofReal_real_eq_id, id] at hg

  have key : ∀ (e₁ e₂ : Matrix (Fin 2) (Fin 2) ℝ) (θ : ℝ),
      (e₁ = 1 ∨ e₁ = !![1, 0; 0, -1]) → (e₂ = 1 ∨ e₂ = !![1, 0; 0, -1]) →
      (k₁ : Matrix (Fin 2) (Fin 2) ℝ) = !![Real.cos θ₁, Real.sin θ₁; -Real.sin θ₁, Real.cos θ₁] * e₁ →
      (k₂ : Matrix (Fin 2) (Fin 2) ℝ) = e₂ * !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] →
      ∃ (α β : ℝ) (D : FiltrationCocycleLiftCriterion), iotaG D = D ∧ g = kMat α * D * kMat β := by
    intro e₁ e₂ θ he₁ he₂ hk₁ hk₂
    set M := e₁ * Matrix.diagonal (fun i => a i) * e₂ with hM
    have hMd : ∃ d₁ d₂ : ℝ, M = !![d₁, 0; 0, d₂] := by
      have h01 : M 0 1 = 0 := by
        rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl <;>
          simp only [hM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.one_apply] <;>
          simp
      have h10 : M 1 0 = 0 := by
        rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl <;>
          simp only [hM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.one_apply] <;>
          simp
      refine ⟨M 0 0, M 1 1, ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;> simp [h01, h10]
    obtain ⟨d₁, d₂, hd⟩ := hMd
    have hgM : ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![Real.cos θ₁, Real.sin θ₁; -Real.sin θ₁, Real.cos θ₁] * !![d₁, 0; 0, d₂] *
          !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := by
      rw [hg, hk₁, hk₂, ← hd, hM]; simp only [Matrix.mul_assoc]
    have hdet : (!![d₁, 0; 0, d₂] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
      intro h0
      have := Matrix.GeneralLinearGroup.det_ne_zero (g : GL (Fin 2) ℝ)
      rw [hgM, Matrix.det_mul, Matrix.det_mul, h0] at this
      simp at this
    refine ⟨θ₁, θ, toGL _ hdet, iotaG_diag d₁ d₂ hdet, ?_⟩
    apply GL2_ext
    simp only [Subgroup.coe_mul, Units.val_mul, coe_kMat, coe_toGL]
    exact hgM
  have hε : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 0; 0, -1] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hrot : ∀ θ : ℝ, !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] * (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1, 0; 0, -1] * !![Real.cos (-θ), Real.sin (-θ); -Real.sin (-θ), Real.cos (-θ)] := by
    intro θ; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact key 1 1 θ₂ (Or.inl rfl) (Or.inl rfl) (by rw [h₁, Matrix.mul_one]) (by rw [h₂, Matrix.one_mul])
  · exact key 1 _ (-θ₂) (Or.inl rfl) (Or.inr rfl) (by rw [h₁, Matrix.mul_one]) (by rw [h₂, hrot])
  · exact key _ 1 θ₂ (Or.inr rfl) (Or.inl rfl) h₁ (by rw [h₂, Matrix.one_mul])
  · exact key _ _ (-θ₂) (Or.inr rfl) (Or.inr rfl) h₁ (by rw [h₂, hrot])

end GroundTheory.Automorphic.ArchWhittaker
