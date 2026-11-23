import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2

variable {F : Type} [Field F] [NumberField F]

def nL (c : A F) : G1 F := ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩

theorem specialLinear_ext_entries {g h : G1 F} (h00 : g 0 0 = h 0 0) (h01 : g 0 1 = h 0 1) (h10 : g 1 0 = h 1 0) (h11 : g 1 1 = h 1 1) : g = h := by
  ext i j; fin_cases i <;> fin_cases j <;> assumption
theorem specialLinear_det_entries (g : G1 F) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h
theorem specialLinear_mul_entry (g h : G1 F) (i j : Fin 2) : (g * h) i j = g i 0 * h 0 j + g i 1 * h 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]
theorem specialLinear_inv_val (g : G1 F) : (g⁻¹).1 = !![g 1 1, -g 0 1; -g 1 0, g 0 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
@[simp] theorem nU_val (b : A F) : (nU b).1 = !![1, b; 0, 1] := rfl
@[simp] theorem nL_val (c : A F) : (nL c).1 = !![1, 0; c, 1] := rfl
@[simp] theorem mD_val (a : (A F)ˣ) : (mD a).1 = !![(a : A F), 0; 0, ((a⁻¹ : (A F)ˣ) : A F)] := rfl
@[simp] theorem wW_val : (wW F).1 = !![0, 1; -1, 0] := rfl
@[simp] theorem dM_val (t : (A F)ˣ) : (dM t).val = !![1, 0; 0, (t : A F)] := rfl
@[simp] theorem aE_val (t : (A F)ˣ) : (aE t).val = !![(t : A F), 0; 0, 1] := rfl
@[simp] theorem cD_val (t : (A F)ˣ) (g : G1 F) :
    (cD t g).1 = !![g 0 0, g 0 1 * ((t⁻¹ : (A F)ˣ) : A F); (t : A F) * g 1 0, g 1 1] := rfl
@[simp] theorem gl_val (g : G1 F) : (gl g).val = g.1 := rfl

local macro "sl2" : tactic => `(tactic|
  (refine Subtype.ext ?_; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]))
local macro "gl2" : tactic => `(tactic|
  (refine Units.ext ?_; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]))

@[simp] theorem nU_zero : nU (0 : A F) = 1 := by sl2
theorem nU_add (b c : A F) : nU (b + c) = nU b * nU c := by sl2; ring
theorem nU_neg (b : A F) : nU (-b) = (nU b)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← nU_add]; simp)
@[simp] theorem nL_zero : nL (0 : A F) = 1 := by sl2
theorem nL_add (b c : A F) : nL (b + c) = nL b * nL c := by sl2
theorem nL_neg (b : A F) : nL (-b) = (nL b)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← nL_add]; simp)
@[simp] theorem mD_one : mD (1 : (A F)ˣ) = 1 := by sl2
theorem mD_mul (a b : (A F)ˣ) : mD (a * b) = mD a * mD b := by sl2; ring
theorem mD_inv (a : (A F)ˣ) : mD a⁻¹ = (mD a)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← mD_mul]; simp)
theorem mD_mul_nU (a : (A F)ˣ) (b : A F) : mD a * nU b = nU ((a : A F) ^ 2 * b) * mD a := by
  sl2; linear_combination (-(a : A F) * b) * a.mul_inv
theorem mD_mul_nL (a : (A F)ˣ) (c : A F) : mD a * nL c = nL (((a⁻¹ : (A F)ˣ) : A F) ^ 2 * c) * mD a := by
  sl2; linear_combination (-((a⁻¹ : (A F)ˣ) : A F) * c) * a.mul_inv
theorem wW_mul_mD (a : (A F)ˣ) : wW F * mD a = mD a⁻¹ * wW F := by sl2
theorem wW_mul_wW : wW F * wW F = mD (-1) := by sl2
theorem wW_inv : (wW F)⁻¹ = mD (-1) * wW F := by
  refine inv_eq_of_mul_eq_one_right ?_; sl2
theorem wW_mul_nU (b : A F) : wW F * nU b = nL (-b) * wW F := by sl2
theorem wW_nU_wW_inv (b : A F) : wW F * nU b * (wW F)⁻¹ = nL (-b) := by rw [wW_mul_nU, mul_inv_cancel_right]
theorem nL_eq (c : A F) : nL c = wW F * nU (-c) * (wW F)⁻¹ := by rw [wW_nU_wW_inv, neg_neg]
theorem wW_eq : wW F = nU 1 * nL (-1) * nU 1 := by sl2
theorem mD_neg_one_comm (g : G1 F) : mD (-1) * g = g * mD (-1) := by sl2

theorem wW_nU_wW (t : (A F)ˣ) : wW F * nU (t : A F) * wW F =
    nU (-((t⁻¹ : (A F)ˣ) : A F)) * mD (-t⁻¹) * wW F * nU (-((t⁻¹ : (A F)ˣ) : A F)) := by sl2
theorem mD_mul_wW (a : (A F)ˣ) : mD a * wW F = nU (a : A F) * nL (-((a⁻¹ : (A F)ˣ) : A F)) * nU (a : A F) := by sl2

@[simp] theorem dM_one : dM (1 : (A F)ˣ) = 1 := by gl2
theorem dM_mul (s t : (A F)ˣ) : dM (s * t) = dM s * dM t := by gl2
theorem dM_inv (t : (A F)ˣ) : dM t⁻¹ = (dM t)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← dM_mul]; simp)
@[simp] theorem det_dM (t : (A F)ˣ) : Matrix.GeneralLinearGroup.det (dM t) = t := by
  refine Units.ext ?_; simp [Matrix.det_fin_two]
@[simp] theorem aE_one : aE (1 : (A F)ˣ) = 1 := by gl2
theorem aE_mul (s t : (A F)ˣ) : aE (s * t) = aE s * aE t := by gl2
theorem aE_inv (t : (A F)ˣ) : aE t⁻¹ = (aE t)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← aE_mul]; simp)
@[simp] theorem det_aE (t : (A F)ˣ) : Matrix.GeneralLinearGroup.det (aE t) = t := by
  refine Units.ext ?_; simp [Matrix.det_fin_two]
@[simp] theorem det_gl (g : G1 F) : Matrix.GeneralLinearGroup.det (gl g) = 1 := Units.ext g.det_coe
theorem det_scalar (s : (A F)ˣ) : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) s) = s ^ 2 := by
  refine Units.ext ?_; simp [Matrix.det_fin_two, pow_two]
theorem gl_mul (g h : G1 F) : gl (g * h) = gl g * gl h := map_mul _ _ _
theorem gl_one : gl (1 : G1 F) = 1 := map_one _
theorem gl_inv (g : G1 F) : gl g⁻¹ = (gl g)⁻¹ := map_inv _ _
theorem gl_injective : Function.Injective (gl (F := F)) := fun _ _ h => Subtype.ext (congrArg Units.val h)
theorem scalar_comm (s : (A F)ˣ) (g : GL (Fin 2) (A F)) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) s * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) s := by
  gl2 <;> ring
theorem aE_mul_dM (s : (A F)ˣ) : aE s * dM s = Matrix.GeneralLinearGroup.scalar (Fin 2) s := by gl2
theorem dM_mul_aE (s t : (A F)ˣ) : dM s * aE t = aE t * dM s := by gl2
theorem gl_mD (a : (A F)ˣ) : gl (mD a) = aE a * dM a⁻¹ := by gl2
theorem gl_mD_mul_dM_sq (s : (A F)ˣ) : gl (mD s) * dM (s ^ 2) = Matrix.GeneralLinearGroup.scalar (Fin 2) s := by
  gl2; rw [pow_two, ← mul_assoc, Units.inv_mul, one_mul]
theorem gl_wW_mul_aE (t : (A F)ˣ) : gl (wW F) * aE t = dM t * gl (wW F) := by gl2
theorem aE_mul_nU (t : (A F)ˣ) (b : A F) : aE t * gl (nU b) = gl (nU ((t : A F) * b)) * aE t := by gl2
theorem dM_mul_gl (t : (A F)ˣ) (g : G1 F) : dM t * gl g = gl (cD t g) * dM t := by
  gl2 <;> first | rw [mul_assoc, Units.inv_mul, mul_one] | ring
theorem gl_cD (t : (A F)ˣ) (g : G1 F) : gl (cD t g) = dM t * gl g * (dM t)⁻¹ := by rw [dM_mul_gl, mul_inv_cancel_right]
theorem exists_gl_of_det_eq_one (h : GL (Fin 2) (A F)) (hd : Matrix.GeneralLinearGroup.det h = 1) : ∃ g, gl g = h :=
  ⟨⟨h.val, congrArg Units.val hd⟩, Units.ext rfl⟩
theorem exists_gl_mul_dM (h : GL (Fin 2) (A F)) : ∃ g, h = gl g * dM (Matrix.GeneralLinearGroup.det h) := by
  obtain ⟨g, hg⟩ := exists_gl_of_det_eq_one (h * (dM (Matrix.GeneralLinearGroup.det h))⁻¹) (by simp)
  exact ⟨g, by rw [hg, inv_mul_cancel_right]⟩
theorem exists_gl_mul_aE (h : GL (Fin 2) (A F)) : ∃ g, h = gl g * aE (Matrix.GeneralLinearGroup.det h) := by
  obtain ⟨g, hg⟩ := exists_gl_of_det_eq_one (h * (aE (Matrix.GeneralLinearGroup.det h))⁻¹) (by simp)
  exact ⟨g, by rw [hg, inv_mul_cancel_right]⟩

@[simp] theorem cD_one_left (g : G1 F) : cD 1 g = g := gl_injective (by rw [gl_cD]; simp)
theorem cD_mul_left (s t : (A F)ˣ) (g : G1 F) : cD (s * t) g = cD s (cD t g) :=
  gl_injective (by simp only [gl_cD, dM_mul]; group)
theorem cD_mul (t : (A F)ˣ) (g h : G1 F) : cD t (g * h) = cD t g * cD t h :=
  gl_injective (by simp only [gl_cD, gl_mul]; group)
@[simp] theorem cD_one (t : (A F)ˣ) : cD t (1 : G1 F) = 1 := gl_injective (by rw [gl_cD, gl_one]; simp)

def cDE (t : (A F)ˣ) : G1 F ≃* G1 F where
  toFun := cD t
  invFun := cD t⁻¹
  left_inv g := by rw [← cD_mul_left]; simp
  right_inv g := by rw [← cD_mul_left]; simp
  map_mul' := cD_mul t
@[simp] theorem cDE_apply (t : (A F)ˣ) (g : G1 F) : cDE t g = cD t g := rfl
theorem cD_inv (t : (A F)ˣ) (g : G1 F) : cD t g⁻¹ = (cD t g)⁻¹ := map_inv (cDE t) g
theorem cD_nU (t : (A F)ˣ) (b : A F) : cD t (nU b) = nU (b * ((t⁻¹ : (A F)ˣ) : A F)) := by sl2
theorem cD_nL (t : (A F)ˣ) (c : A F) : cD t (nL c) = nL ((t : A F) * c) := by sl2
theorem cD_mD (t a : (A F)ˣ) : cD t (mD a) = mD a := by sl2
theorem cD_wW (t : (A F)ˣ) : cD t (wW F) = mD t⁻¹ * wW F := by sl2
theorem cD_sq (t : (A F)ˣ) (g : G1 F) : cD (t ^ 2) g = (mD t)⁻¹ * g * mD t := by
  apply gl_injective
  have h : dM (t ^ 2) = (gl (mD t))⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) t := by
    rw [← gl_mD_mul_dM_sq, inv_mul_cancel_left]
  rw [gl_cD, h, gl_mul, gl_mul, gl_inv, mul_assoc (gl (mD t))⁻¹, scalar_comm]; group

theorem continuous_entry (i j : Fin 2) : Continuous fun g : G1 F => g i j :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
theorem continuous_adelicSL2_of_continuous_entries {X : Type*} [TopologicalSpace X] {f : X → G1 F} (h : ∀ i j, Continuous fun x => f x i j) : Continuous f :=
  continuous_induced_rng.2 (continuous_matrix h)
theorem continuous_adelicGL2_of_continuous_entries {X : Type*} [TopologicalSpace X] {f : X → GL (Fin 2) (A F)} (h : ∀ i j, Continuous fun x => (f x).val i j)
    (h' : ∀ i j, Continuous fun x => ((f x)⁻¹).val i j) : Continuous f :=
  Units.continuous_iff.2 ⟨continuous_matrix h, continuous_matrix h'⟩
theorem continuous_nU : Continuous (nU (F := F)) :=
  continuous_adelicSL2_of_continuous_entries fun i j => by fin_cases i <;> fin_cases j <;> simp <;> fun_prop
theorem continuous_nL : Continuous (nL (F := F)) :=
  continuous_adelicSL2_of_continuous_entries fun i j => by fin_cases i <;> fin_cases j <;> simp <;> fun_prop
theorem continuous_mD : Continuous (mD (F := F)) :=
  continuous_adelicSL2_of_continuous_entries fun i j => by
    fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact Units.continuous_val | exact Units.continuous_coe_inv
private theorem cdM (i j : Fin 2) : Continuous fun t : (A F)ˣ => (dM t).val i j := by
  fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact Units.continuous_val
private theorem caE (i j : Fin 2) : Continuous fun t : (A F)ˣ => (aE t).val i j := by
  fin_cases i <;> fin_cases j <;> simp <;> first | exact continuous_const | exact Units.continuous_val
theorem continuous_dM : Continuous (dM (F := F)) :=
  continuous_adelicGL2_of_continuous_entries cdM fun i j => by simp only [← dM_inv]; exact (cdM i j).comp continuous_inv
theorem continuous_aE : Continuous (aE (E := F)) :=
  continuous_adelicGL2_of_continuous_entries caE fun i j => by simp only [← aE_inv]; exact (caE i j).comp continuous_inv
theorem continuous_gl : Continuous (gl (F := F)) :=
  continuous_adelicGL2_of_continuous_entries continuous_entry fun i j => by simp only [← gl_inv]; exact (continuous_entry i j).comp continuous_inv
theorem continuous_cD : Continuous fun p : (A F)ˣ × G1 F => cD p.1 p.2 :=
  continuous_adelicSL2_of_continuous_entries fun i j => by
    have e := fun i j => (continuous_entry (F := F) i j).comp (continuous_snd (X := (A F)ˣ))
    fin_cases i <;> fin_cases j
    exacts [e 0 0, (e 0 1).mul (Units.continuous_coe_inv.comp continuous_fst),
      (Units.continuous_val.comp continuous_fst).mul (e 1 0), e 1 1]
theorem continuous_adelicGL2_det : Continuous fun h : GL (Fin 2) (A F) => Matrix.GeneralLinearGroup.det h :=
  Matrix.GeneralLinearGroup.continuous_det

theorem ab_pos (a : (A F)ˣ) : 0 < ab a := (IdeleGroup.ideleModule F a).2
theorem ab_ne_zero (a : (A F)ˣ) : ab a ≠ 0 := (ab_pos a).ne'
@[simp] theorem ab_one : ab (1 : (A F)ˣ) = 1 := congrArg Subtype.val (map_one (IdeleGroup.ideleModule F))
theorem ab_mul (a b : (A F)ˣ) : ab (a * b) = ab a * ab b := congrArg Subtype.val (map_mul (IdeleGroup.ideleModule F) a b)
theorem ab_inv (a : (A F)ˣ) : ab a⁻¹ = (ab a)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← ab_mul]; simp)
theorem ab_pow (a : (A F)ˣ) (n : ℕ) : ab (a ^ n) = ab a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, ab_mul, ih]
theorem ab_diagonal (c : Fˣ) : ab (IdeleGroup.diagonal F c) = 1 := congrArg Subtype.val (IdeleGroup.ideleModule_diagonal c)
theorem coe_diagonal (c : Fˣ) : ((IdeleGroup.diagonal F c : (A F)ˣ) : A F) = rt (c : F) := rfl
theorem ab_neg_one : ab (-1 : (A F)ˣ) = 1 := by
  have h : ab (-1 : (A F)ˣ) ^ 2 = 1 := by rw [← ab_pow]; simp
  exact (pow_eq_one_iff_of_nonneg (ab_pos _).le two_ne_zero).1 h
theorem ab_neg (a : (A F)ˣ) : ab (-a) = ab a := by rw [← neg_one_mul, ab_mul, ab_neg_one, one_mul]
theorem continuous_ab : Continuous (ab (F := F)) := continuous_subtype_val.comp IdeleGroup.continuous_ideleModule

@[simp] theorem ψ_zero : ψ (0 : A F) = 1 := by simp [ψ]
theorem ψ_add (x y : A F) : ψ (x + y) = ψ x * ψ y := by simp [ψ, AddChar.map_add_eq_mul]
@[simp] theorem norm_ψ (x : A F) : ‖ψ x‖ = 1 := Circle.norm_coe _
theorem ψ_ne_zero (x : A F) : ψ x ≠ 0 := Circle.coe_ne_zero _
theorem ψ_neg (x : A F) : ψ (-x) = (ψ x)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← ψ_add]; simp)
@[simp] theorem ψ_rt (c : F) : ψ (rt c) = 1 := by simp [ψ, adelicChar_algebraMap]
theorem continuous_ψ : Continuous (ψ (F := F)) := continuous_subtype_val.comp continuous_adelicChar

theorem ratS_apply (γ : Matrix.SpecialLinearGroup (Fin 2) F) (i j : Fin 2) : ratS F γ i j = rt (γ i j) := rfl
theorem ratGL_apply (n : ℕ) (γ : GL (Fin n) F) (i j : Fin n) : (ratGL F n γ).val i j = rt (γ.val i j) := rfl
theorem gl_ratS (γ : Matrix.SpecialLinearGroup (Fin 2) F) : gl (ratS F γ) = ratGL F 2 (Matrix.SpecialLinearGroup.toGL γ) :=
  Units.ext rfl
theorem det_ratGL (γ : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.det (ratGL F 2 γ) = IdeleGroup.diagonal F (Matrix.GeneralLinearGroup.det γ) := by
  refine Units.ext ?_
  simp [Matrix.det_fin_two, ratGL_apply, coe_diagonal]
theorem nU_rt_mem (b : F) : nU (rt b) ∈ Gam F := ⟨⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩, by
  apply specialLinear_ext_entries <;> refine (ratS_apply _ _ _).trans ?_ <;> simp⟩
theorem nL_rt_mem (b : F) : nL (rt b) ∈ Gam F := ⟨⟨!![1, 0; b, 1], by simp [Matrix.det_fin_two]⟩, by
  apply specialLinear_ext_entries <;> refine (ratS_apply _ _ _).trans ?_ <;> simp⟩
theorem wW_mem : wW F ∈ Gam F := ⟨⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩, by
  apply specialLinear_ext_entries <;> refine (ratS_apply _ _ _).trans ?_ <;> simp⟩
theorem mem_Gam_iff (g : G1 F) : g ∈ Gam F ↔ ∀ i j, ∃ c : F, g i j = rt c := by
  refine ⟨by rintro ⟨γ, rfl⟩ i j; exact ⟨γ i j, rfl⟩, fun h => ?_⟩
  choose c hc using h
  refine ⟨⟨Matrix.of c, ?_⟩, by ext i j; exact (hc i j).symm⟩
  haveI := AdeleBaseChange.nontrivial_adeleRing F
  apply (algebraMap F (A F)).injective
  have := specialLinear_det_entries g
  simp only [hc] at this
  simpa [Matrix.det_fin_two] using this
theorem mD_diagonal_mem (c : Fˣ) : mD (IdeleGroup.diagonal F c) ∈ Gam F := by
  rw [mem_Gam_iff]; intro i j
  fin_cases i <;> fin_cases j
  exacts [⟨c, rfl⟩, ⟨0, by simp⟩, ⟨0, by simp⟩, ⟨(c⁻¹ : Fˣ), rfl⟩]
theorem cD_diagonal_mem (c : Fˣ) {g : G1 F} (hg : g ∈ Gam F) : cD (IdeleGroup.diagonal F c) g ∈ Gam F := by
  obtain ⟨γ, rfl⟩ := hg
  rw [mem_Gam_iff]; intro i j
  fin_cases i <;> fin_cases j
  exacts [⟨γ 0 0, rfl⟩, ⟨γ 0 1 * (c⁻¹ : Fˣ), (map_mul (algebraMap F (A F)) (γ 0 1) ((c⁻¹ : Fˣ) : F)).symm⟩,
    ⟨c * γ 1 0, (map_mul (algebraMap F (A F)) (c : F) (γ 1 0)).symm⟩, ⟨γ 1 1, rfl⟩]
theorem exists_ratGL_dM (c : Fˣ) : ∃ γ, ratGL F 2 γ = dM (IdeleGroup.diagonal F c) :=
  ⟨⟨!![1, 0; 0, (c : F)], !![1, 0; 0, ((c⁻¹ : Fˣ) : F)], by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩, by
      refine Units.ext ?_; ext i j; fin_cases i <;> fin_cases j <;> simp [ratGL_apply, coe_diagonal]⟩
theorem exists_ratGL_aE (c : Fˣ) : ∃ γ, ratGL F 2 γ = aE (IdeleGroup.diagonal F c) :=
  ⟨⟨!![(c : F), 0; 0, 1], !![((c⁻¹ : Fˣ) : F), 0; 0, 1], by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩, by
      refine Units.ext ?_; ext i j; fin_cases i <;> fin_cases j <;> simp [ratGL_apply, coe_diagonal]⟩

end UpperTheory.ConvolutionTheory.R2

end
