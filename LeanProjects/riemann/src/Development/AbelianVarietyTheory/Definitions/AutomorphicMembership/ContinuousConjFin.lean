import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.Imports
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfValuedEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart

noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open scoped ContDiff

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [NumberField E] [IsTotallyComplex E] in
open Classical in

def coord (τ : E →+* ℂ) : Cinf E →+* ℂ :=
  if (InfinitePlace.mk τ).embedding = τ then Pi.evalRingHom (fun _ => ℂ) (InfinitePlace.mk τ)
  else (starRingEnd ℂ).comp (Pi.evalRingHom (fun _ => ℂ) (InfinitePlace.mk τ))

theorem coord_algebraMap (τ : E →+* ℂ) (x : E) : coord τ (pInf E (algebraMap E (Ad E) x)) = τ x := by
  unfold coord
  split_ifs with h
  · exact (pInf_algebraMap x _).trans (by rw [h])
  · have h' := (InfinitePlace.embedding_mk_eq τ).resolve_left h
    change starRingEnd ℂ (pInf E _ _) = _
    rw [pInf_algebraMap, h']
    simp

omit [NumberField E] [IsTotallyComplex E] in
open Classical in

def atEmb (τ : E →+* ℂ) (z : ℂ) : Cinf E :=
  Pi.single (InfinitePlace.mk τ) (if (InfinitePlace.mk τ).embedding = τ then z else starRingEnd ℂ z)

omit [NumberField E] [IsTotallyComplex E] in

theorem coord_atEmb (τ : E →+* ℂ) (z : ℂ) : coord τ (atEmb τ z) = z := by
  unfold coord atEmb
  split_ifs <;> simp

omit [NumberField E] [IsTotallyComplex E] in

theorem atEmb_mul (τ : E →+* ℂ) (z z' : ℂ) : atEmb τ z * atEmb τ z' = atEmb τ (z * z') := by
  classical
  unfold atEmb
  rw [← Pi.single_mul]
  split_ifs <;> simp

omit [NumberField E] [IsTotallyComplex E] in

theorem atEmb_eq (τ : E →+* ℂ) (z : ℂ) : atEmb τ z = z.re • atEmb τ 1 + z.im • atEmb τ Complex.I := by
  classical
  unfold atEmb
  rw [← Pi.single_smul, ← Pi.single_smul, ← Pi.single_add]
  congr 1
  split_ifs <;> apply Complex.ext <;> simp

omit [NumberField E] in

theorem atEmb_conj (τ : E →+* ℂ) (z : ℂ) :
    atEmb (ComplexEmbedding.conjugate τ) z = atEmb τ (starRingEnd ℂ z) := by
  have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h))
  unfold atEmb
  simp only [InfinitePlace.mk_conjugate_eq]
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · rw [if_pos h, if_neg (by rw [InfinitePlace.mk_conjugate_eq, h]; exact hne.symm)]
  · rw [if_pos (by rw [InfinitePlace.mk_conjugate_eq, h]), if_neg (by rw [h]; exact hne)]; simp

omit [NumberField E] [IsTotallyComplex E] in

theorem atEmb_mul_of_ne {τ τ' : E →+* ℂ} (h : InfinitePlace.mk τ ≠ InfinitePlace.mk τ') (z z' : ℂ) :
    atEmb τ z * atEmb τ' z' = 0 := by
  classical
  funext w
  unfold atEmb
  by_cases hw : w = InfinitePlace.mk τ
  · subst hw; simp [Pi.single_eq_of_ne h]
  · simp [Pi.single_eq_of_ne hw]

variable (E a) in

def lieS (i j : Fin a) : Cinf E →ₗ[ℝ] Module.End ℂ (Sm E a) :=
  (lie E a).comp (Matrix.singleLinearMap ℝ i j : Cinf E →ₗ[ℝ] Matrix (Fin a) (Fin a) (Cinf E))

theorem lieS_apply (i j : Fin a) (x : Cinf E) : lieS E a i j x = lie E a (toL (Matrix.single i j x)) := rfl

theorem lieS_comm (i j k l : Fin a) (x y : Cinf E) :
    lieS E a i j x * lieS E a k l y - lieS E a k l y * lieS E a i j x =
      (if j = k then lieS E a i l (x * y) else 0) - (if l = i then lieS E a k j (x * y) else 0) := by
  simp only [lieS_apply]
  rw [lie_comm]
  congr 1
  · split_ifs with h
    · subst h; exact congrArg (fun X => lie E a (toL X)) (Matrix.single_mul_single_same _ _ _ _ _)
    · exact (congrArg (fun X => lie E a (toL X)) (Matrix.single_mul_single_of_ne _ _ _ _ h _)).trans (map_zero _)
  · split_ifs with h
    · subst h; rw [mul_comm x]; exact congrArg (fun X => lie E a (toL X)) (Matrix.single_mul_single_same _ _ _ _ _)
    · exact (congrArg (fun X => lie E a (toL X)) (Matrix.single_mul_single_of_ne _ _ _ _ h _)).trans (map_zero _)

def Eop (τ : E →+* ℂ) (i j : Fin a) : Module.End ℂ (Sm E a) :=
  (1 / 2 : ℂ) • (lieS E a i j (atEmb τ 1) - Complex.I • lieS E a i j (atEmb τ Complex.I))

theorem Eop_comm_aux (τ τ' : E →+* ℂ) (i j k l : Fin a) :
    Eop τ i j * Eop τ' k l - Eop τ' k l * Eop τ i j =
      (if j = k then (1 / 4 : ℂ) • (lieS E a i l (atEmb τ 1 * atEmb τ' 1) - lieS E a i l (atEmb τ .I * atEmb τ' .I) -
        Complex.I • (lieS E a i l (atEmb τ 1 * atEmb τ' .I) + lieS E a i l (atEmb τ .I * atEmb τ' 1))) else 0) -
      (if l = i then (1 / 4 : ℂ) • (lieS E a k j (atEmb τ 1 * atEmb τ' 1) - lieS E a k j (atEmb τ .I * atEmb τ' .I) -
        Complex.I • (lieS E a k j (atEmb τ 1 * atEmb τ' .I) + lieS E a k j (atEmb τ .I * atEmb τ' 1))) else 0) := by
  have h1 := lieS_comm i j k l (atEmb τ 1) (atEmb τ' 1)
  have h2 := lieS_comm i j k l (atEmb τ 1) (atEmb τ' .I)
  have h3 := lieS_comm i j k l (atEmb τ .I) (atEmb τ' 1)
  have h4 := lieS_comm i j k l (atEmb τ .I) (atEmb τ' .I)
  simp only [Eop, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, smul_sub, smul_smul]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  split_ifs at h1 h2 h3 h4 ⊢ <;>
    linear_combination (norm := skip) (exp := 1) (1 / 4 : ℂ) • h1 - (Complex.I / 4 : ℂ) • h2 - (Complex.I / 4 : ℂ) • h3 - (1 / 4 : ℂ) • h4 <;>
    match_scalars <;> ring_nf <;> simp

theorem glRel_Eop (τ : E →+* ℂ) : Formalism.REAL.GlRel (Eop (a := a) τ) := by
  intro i j k l
  have e : atEmb τ (Complex.I * Complex.I) = -atEmb τ 1 := by
    rw [atEmb_eq]; simp
  rw [Eop_comm_aux]
  simp only [atEmb_mul, one_mul, mul_one, e, map_neg, Eop]
  congr 1 <;> split_ifs <;> first | rfl | (match_scalars <;> ring)

theorem Eop_comm {τ τ' : E →+* ℂ} (h : τ ≠ τ') (i j k l : Fin a) : Eop τ i j * Eop τ' k l = Eop τ' k l * Eop τ i j := by
  rw [← sub_eq_zero, Eop_comm_aux]
  by_cases hw : InfinitePlace.mk τ = InfinitePlace.mk τ'
  · obtain rfl : ComplexEmbedding.conjugate τ = τ' := (InfinitePlace.mk_eq_iff.1 hw).resolve_left h
    have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
      rw [atEmb_eq]; simp
    have e' : atEmb τ (-1) = -atEmb τ 1 := by
      rw [atEmb_eq]; simp
    simp [atEmb_conj, atEmb_mul, e, e']
  · simp [atEmb_mul_of_ne hw]

def cap (τ : E →+* ℂ) (u : ℂ) : Module.End ℂ (Sm E a) := Formalism.REAL.qdet (Eop τ) (u + ((a : ℂ) - 1) / 2)

theorem cap_comm (τ : E →+* ℂ) (u : ℂ) (i j : Fin a) : cap τ u * Eop τ i j = Eop τ i j * cap τ u :=
  Formalism.REAL.qDetCentral _ a _ (glRel_Eop τ) _ i j

theorem cap_highest (τ : E →+* ℂ) (ν : Fin a → ℂ) (φ : Sm E a) (h : Formalism.REAL.IsHW (Eop τ) ν φ) (u : ℂ) :
    cap τ u φ = (∏ k : Fin a, (u + (ν k + (((a : ℂ) - 1) / 2 - (k : ℕ))))) • φ := by
  rw [cap, Formalism.REAL.qDetHW _ a _ ν φ (glRel_Eop τ) h]
  congr 1
  exact Finset.prod_congr rfl fun k _ => by ring

variable (E a) in

def Zalg : Subalgebra ℂ (Module.End ℂ (Sm E a)) := Algebra.adjoin ℂ {z | ∃ τ u, z = cap τ u}

theorem map_qdet {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) (X : Fin a → Fin a → A)
    (u : ℂ) : f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) u := by
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 3
  funext k
  simp [Formalism.REAL.Tm, apply_ite f]

theorem qdet_shift {A : Type} [Ring A] [Algebra ℂ A] (X : Fin a → Fin a → A) (s u : ℂ) :
    Formalism.REAL.qdet (fun i j => X i j + if i = j then algebraMap ℂ A s else 0) u = Formalism.REAL.qdet X (u + s) := by
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 3
  funext k
  simp only [Formalism.REAL.Tm]
  split_ifs
  · simp only [map_sub, map_add]; abel
  · simp

theorem Zalg_stable {V : Submodule ℂ (Sm E a)} (hV : ∀ X, ∀ φ ∈ V, lie E a X φ ∈ V) {z : Module.End ℂ (Sm E a)}
    (hz : z ∈ Zalg E a) : ∀ φ ∈ V, z φ ∈ V := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {z | ∀ φ ∈ V, z φ ∈ V}
      mul_mem' := fun hx hy φ h => hx _ (hy φ h)
      add_mem' := fun hx hy φ h => V.add_mem (hx φ h) (hy φ h)
      algebraMap_mem' := fun c φ h => V.smul_mem c h }
  have hE : ∀ τ i j, Eop τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hV _) (S.smul_mem (hV _) _)) _
  refine (Algebra.adjoin_le (S := S) ?_) hz
  rintro _ ⟨τ, u, rfl⟩
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

omit [IsTotallyComplex E] in

def chiDet (a : ℕ) (χ : HChar E) : GA E a →* ℂˣ := χ.1.comp GeneralLinearGroup.det

def chiInf (χ : HChar E) : (Cinf E)ˣ →* ℂˣ := χ.1.comp (infId E)

theorem continuous_chiInf (χ : HChar E) : Continuous (chiInf χ) := χ.2.1.comp (continuous_infId E)

def dchi (χ : HChar E) : Cinf E →L[ℝ] ℂ := fderiv ℝ (extZero (chiInf χ)) 1

theorem chiInf_expU (χ : HChar E) (z : Cinf E) : ((chiInf χ (expU z) : ℂˣ) : ℂ) = Complex.exp (dchi χ z) := by
  obtain ⟨L, hL⟩ := exists_lin _ (continuous_chiInf χ)
  rw [dchi, fderiv_extZero (continuous_chiInf χ) hL, hL]

def expo (χ : HChar E) (τ : E →+* ℂ) : ℂ := (1 / 2 : ℂ) * (dchi χ (atEmb τ 1) - Complex.I * dchi χ (atEmb τ Complex.I))

theorem chiInf_expU_atEmb (χ : HChar E) (τ : E →+* ℂ) (z : ℂ) :
    ((chiInf χ (expU (atEmb τ z)) : ℂˣ) : ℂ) =
      Complex.exp (expo χ τ * z + expo χ (ComplexEmbedding.conjugate τ) * starRingEnd ℂ z) := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  rw [chiInf_expU, atEmb_eq, map_add, map_smul, map_smul]
  simp only [expo, atEmb_conj, map_one, Complex.conj_I, e, map_neg, Complex.real_smul]
  congr 1
  conv_rhs => rw [← Complex.re_add_im z]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  linear_combination (z.im * dchi χ (atEmb τ Complex.I)) * Complex.I_mul_I

theorem expo_eq_of_exp (χ : HChar E) (τ : E →+* ℂ) (p q : ℂ)
    (h : ∀ z, ((chiInf χ (expU (atEmb τ z)) : ℂˣ) : ℂ) = Complex.exp (p * z + q * starRingEnd ℂ z)) : expo χ τ = p := by
  have key : ∀ z : ℂ, dchi χ (atEmb τ z) = p * z + q * starRingEnd ℂ z := by
    intro z
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (t * dchi χ (atEmb τ z))) (dchi χ (atEmb τ z)) 0 := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (dchi χ (atEmb τ z))).cexp
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp (t * (p * z + q * starRingEnd ℂ z))) (p * z + q * starRingEnd ℂ z) 0 := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (p * z + q * starRingEnd ℂ z)).cexp
    refine h1.unique (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_))
    have e : atEmb τ (t * z) = t • atEmb τ z := by
      rw [atEmb_eq, atEmb_eq τ z]; simp [smul_smul]
    have := h (t * z)
    rw [chiInf_expU, e, map_smul, Complex.real_smul] at this
    beta_reduce
    rw [this]
    congr 1
    simp only [map_mul, Complex.conj_ofReal]; ring
  simp only [expo, key, map_one, Complex.conj_I]
  linear_combination (-(p - q) / 2) * Complex.I_mul_I

theorem chart_mul_chi (χ : HChar E) (φ : GA E a → ℂ) (g : GA E a) :
    chart (fun x => φ x * (chiDet a χ x : ℂˣ)) g =
      fun x => chart φ g x * ((chiDet a χ g : ℂˣ) * extZero (chiInf χ) (Matrix.of x).det) := by
  funext x
  by_cases h : IsUnit (Matrix.of x)
  · obtain ⟨u, hu⟩ := h
    have hx : x = toL u.val := hu.symm
    rw [hx, chart_val, chart_val, map_mul, Units.val_mul]
    congr 2
    rw [show chiDet a χ (infGL E a u) = chiInf χ (GeneralLinearGroup.det u) from congrArg χ.1 (det_infGL u)]
    exact (extZero_unit _ _).symm
  · simp [chart, h]

theorem contDiffAt_chi_det (χ : HChar E) {x : Lie E a} (hx : x ∈ invSet E a) :
    ContDiffAt ℝ ∞ (fun x : Lie E a => extZero (chiInf χ) (Matrix.of x).det) x := by
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).1 hx
  exact ContDiffAt.comp (g := extZero (chiInf χ)) x (hu ▸ contDiffAt_extZero _ (continuous_chiInf χ) u)
    contDiff_det.contDiffAt

theorem mul_chi_mem_Sm (χ : HChar E) {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) :
    (fun x => φ x * (chiDet a χ x : ℂˣ)) ∈ Sm E a := fun g => by
  rw [chart_mul_chi]
  exact (hφ g).mul (contDiffOn_const.mul fun x hx => (contDiffAt_chi_det χ hx).contDiffWithinAt)

variable (a) in

def mulChi (χ : HChar E) : Sm E a ≃ₗ[ℂ] Sm E a where
  toFun φ := ⟨fun x => φ.1 x * (chiDet a χ x : ℂˣ), mul_chi_mem_Sm χ φ.2⟩
  invFun φ := ⟨fun x => φ.1 x * (chiDet a χ⁻¹ x : ℂˣ), mul_chi_mem_Sm χ⁻¹ φ.2⟩
  map_add' φ ψ := Subtype.ext <| funext fun x => add_mul _ _ _
  map_smul' c φ := Subtype.ext <| funext fun x => mul_assoc _ _ _
  left_inv φ := Subtype.ext <| funext fun x => Units.mul_inv_cancel_right _ _
  right_inv φ := Subtype.ext <| funext fun x => Units.inv_mul_cancel_right _ _

@[simp] theorem mulChi_apply (χ : HChar E) (φ : Sm E a) (g : GA E a) :
    (mulChi a χ φ).1 g = φ.1 g * (chiDet a χ g : ℂˣ) := rfl

theorem mulChi_mul (χ χ' : HChar E) (φ : Sm E a) : mulChi a (χ * χ') φ = mulChi a χ' (mulChi a χ φ) :=
  Subtype.ext <| funext fun _ => (mul_assoc _ _ _).symm

theorem mulChi_one (φ : Sm E a) : mulChi a 1 φ = φ := Subtype.ext <| funext fun _ => mul_one _

theorem rt_mulChi (χ : HChar E) (h : GA E a) (φ : Sm E a) :
    rt E a h (mulChi a χ φ) = mulChi a χ (((chiDet a χ h : ℂˣ) : ℂ) • rt E a h φ) :=
  Subtype.ext <| funext fun g => by
    simp only [rt_apply, mulChi_apply, map_mul, Units.val_mul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]; ring

omit [IsTotallyComplex E] in

theorem fderiv_det_one (X : Lie E a) :
    fderiv ℝ (fun x : Lie E a => (Matrix.of x).det) (oneL E a) X = (Matrix.of X).trace := by
  have hd : HasFDerivAt (fun x : Lie E a => (Matrix.of x).det)
      (fderiv ℝ (fun x : Lie E a => (Matrix.of x).det) (oneL E a)) (oneL E a + (0 : ℝ) • X) := by
    rw [zero_smul, add_zero]
    exact (contDiff_det.differentiable (by simp) _).hasFDerivAt
  have h1 := hd.comp_hasDerivAt (0 : ℝ) (((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (oneL E a))
  rw [one_smul] at h1
  refine h1.unique ?_
  set P := (1 + (Polynomial.X : Polynomial (Cinf E)) • (Matrix.of X).map Polynomial.C).det.divX.divX
  have hr : HasDerivAt (fun t : ℝ => t • (1 : Cinf E)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (1 : Cinf E)
  have hP : DifferentiableAt ℝ (fun t : ℝ => P.eval (t • (1 : Cinf E))) 0 := by
    simp only [Polynomial.eval_eq_sum_range]
    fun_prop
  have h2 := ((hr.const_mul (Matrix.of X).trace).const_add 1).add (hP.hasDerivAt.mul (hr.mul hr))
  simp only [mul_one, zero_smul, Pi.mul_apply, mul_zero, zero_mul, add_zero] at h2
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have e : Matrix.of (oneL E a + t • X) = 1 + (t • (1 : Cinf E)) • Matrix.of X := by
    rw [smul_assoc, one_smul]; rfl
  change (Matrix.of (oneL E a + t • X)).det = _
  rw [e, Matrix.det_one_add_smul, sq]
  rfl

theorem lie_mulChi (χ : HChar E) (X : Lie E a) (φ : Sm E a) :
    lie E a X (mulChi a χ φ) = mulChi a χ (lie E a X φ + dchi χ (Matrix.of X).trace • φ) := by
  refine Subtype.ext <| funext fun g => ?_
  have h1 : (Matrix.of (oneL E a)).det = 1 := Matrix.det_one
  have hd : HasFDerivAt (fun x : Lie E a => extZero (chiInf χ) (Matrix.of x).det)
      ((dchi χ).comp (fderiv ℝ (fun x : Lie E a => (Matrix.of x).det) (oneL E a))) (oneL E a) := by
    refine HasFDerivAt.comp (g := extZero (chiInf χ)) _ ?_ (contDiff_det.differentiable (by simp) _).hasFDerivAt
    rw [h1]
    exact ((contDiffAt_extZero _ (continuous_chiInf χ) 1).differentiableAt (by simp)).hasFDerivAt
  have h2 := ((differentiableAt_chart φ.2 g).hasFDerivAt.mul (hd.const_mul ((chiDet a χ g : ℂˣ) : ℂ))).fderiv
  have h3 : extZero (chiInf χ) 1 = 1 := (extZero_unit _ 1).trans (by simp)
  have h4 : chart φ.1 g (oneL E a) = φ.1 g := (chart_val φ.1 g 1).trans (by simp)
  change fderiv ℝ (chart (fun x => φ.1 x * (chiDet a χ x : ℂˣ)) g) _ X = (lieD X φ.1 g + _ * φ.1 g) * _
  rw [chart_mul_chi]
  refine (congrArg (fun L : Lie E a →L[ℝ] ℂ => L X) h2).trans ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    fderiv_det_one, h1, h3, h4, smul_eq_mul, lieD]
  ring

theorem Eop_mulChi (χ : HChar E) (τ : E →+* ℂ) (i j : Fin a) (φ : Sm E a) :
    Eop τ i j (mulChi a χ φ) = mulChi a χ (Eop τ i j φ + (if i = j then expo χ τ else 0) • φ) := by
  have ht : ∀ x : Cinf E, (Matrix.of (toL (Matrix.single i j x))).trace = if i = j then x else 0 := fun x => by
    change (Matrix.single i j x).trace = _
    split_ifs with h
    · subst h; simp
    · exact Matrix.trace_single_eq_of_ne _ _ _ h
  simp only [Eop, lieS_apply, LinearMap.smul_apply, LinearMap.sub_apply, lie_mulChi, ht]
  rw [← map_smul (mulChi a χ), ← map_sub (mulChi a χ), ← map_smul (mulChi a χ)]
  congr 1
  split_ifs
  · simp only [expo]; match_scalars <;> ring
  · simp

theorem cap_mulChi (χ : HChar E) (τ : E →+* ℂ) (u : ℂ) (φ : Sm E a) :
    cap τ u (mulChi a χ φ) = mulChi a χ (cap τ (u + expo χ τ) φ) := by
  have h := map_qdet ((mulChi a χ).conjAlgEquiv ℂ).toAlgHom
    (fun i j => Eop τ i j + if i = j then algebraMap ℂ _ (expo χ τ) else 0) (u + ((a : ℂ) - 1) / 2)
  have e : (fun i j => ((mulChi a χ).conjAlgEquiv ℂ).toAlgHom
      (Eop τ i j + if i = j then algebraMap ℂ _ (expo χ τ) else 0)) = Eop τ := by
    funext i j
    refine LinearMap.ext fun ψ => ?_
    obtain ⟨ψ, rfl⟩ := (mulChi a χ).surjective ψ
    rw [Eop_mulChi]
    change mulChi a χ ((Eop τ i j + if i = j then algebraMap ℂ _ (expo χ τ) else 0)
      ((mulChi a χ).symm (mulChi a χ ψ))) = _
    rw [LinearEquiv.symm_apply_apply]
    split_ifs <;> simp
  rw [e, qdet_shift] at h
  rw [cap, ← h, cap, add_right_comm u (expo χ τ)]
  generalize Formalism.REAL.qdet (Eop (a := a) τ) (u + ((a : ℂ) - 1) / 2 + expo χ τ) = z
  change mulChi a χ (z ((mulChi a χ).symm (mulChi a χ φ))) = _
  rw [LinearEquiv.symm_apply_apply]

section Theta

variable {R : Type} [CommRing R]

theorem Phi_mul_transpose (a : ℕ) (R : Type) [CommRing R] : GlobalTheory.Tw.Phi a R * (GlobalTheory.Tw.Phi a R)ᵀ = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  rw [Finset.sum_eq_single i.rev]
  · have h1 : (i : ℕ) + (i.rev : ℕ) + 1 = a := by rw [Fin.val_rev]; omega
    rw [if_pos h1]
    by_cases h : i = j
    · subst h; rw [if_pos h1, Matrix.one_apply_eq, ← mul_pow]; simp
    · rw [if_neg (fun h2 => h (Fin.ext (by omega))), Matrix.one_apply_ne h, mul_zero]
  · intro k _ hk
    rw [if_neg (fun h => hk (Fin.ext (by rw [Fin.val_rev]; omega))), zero_mul]
  · simp

def PhiU (a : ℕ) (R : Type) [CommRing R] : GL (Fin a) R :=
  ⟨GlobalTheory.Tw.Phi a R, (GlobalTheory.Tw.Phi a R)ᵀ, Phi_mul_transpose a R, mul_eq_one_comm.1 (Phi_mul_transpose a R)⟩

def thetaGL (a : ℕ) (c : R →+* R) : GL (Fin a) R →* GL (Fin a) R :=
  (MulAut.conj (PhiU a R)).toMonoidHom.comp ((invT a R).comp (GeneralLinearGroup.map c))

theorem thetaGL_val [StarRing R] (g : GL (Fin a) R) :
    (thetaGL a (starRingEnd R) g).val = GlobalTheory.Tw.theta g.val := by
  rw [GlobalTheory.Tw.theta, ← Matrix.coe_units_inv]
  rfl

theorem det_thetaGL (c : R →+* R) (g : GL (Fin a) R) :
    GeneralLinearGroup.det (thetaGL a c g) = (Units.map c.toMonoidHom (GeneralLinearGroup.det g))⁻¹ := by
  change GeneralLinearGroup.det (PhiU a R * invT a R (GeneralLinearGroup.map c g) * (PhiU a R)⁻¹) = _
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm, eq_inv_iff_mul_eq_one]
  apply Units.ext
  change ((GeneralLinearGroup.map c g)⁻¹).valᵀ.det * c g.val.det = 1
  rw [Matrix.det_transpose, RingHom.map_det]
  exact (Matrix.det_mul _ _).symm.trans (by
    rw [show c.mapMatrix g.val = (GeneralLinearGroup.map c g).val from rfl, Units.inv_mul, Matrix.det_one])

end Theta

section Conj

open GlobalTheory.Mem.Chr

omit [IsTotallyComplex E]

def conjSrc (c : E ≃+* E) (v : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  (existsUnique_conjPl c.symm v).exists.choose

theorem conjPl_conjSrc (c : E ≃+* E) (v : HeightOneSpectrum (𝓞 E)) : ConjPl c (conjSrc c v) v :=
  (conjPl_symm_iff c _ _).1 (existsUnique_conjPl c.symm v).exists.choose_spec

theorem eq_conjSrc {c : E ≃+* E} {v v' : HeightOneSpectrum (𝓞 E)} (h : ConjPl c v v') : v = conjSrc c v' :=
  (existsUnique_conjPl c.symm v').unique ((conjPl_symm_iff c _ _).2 h) ((conjPl_symm_iff c _ _).2 (conjPl_conjSrc c v'))

theorem conjSrc_injective (c : E ≃+* E) : Function.Injective (conjSrc c) := fun x y h =>
  (existsUnique_conjPl c (conjSrc c x)).unique (conjPl_conjSrc c x) (h ▸ conjPl_conjSrc c y)

def conjLoc (c : E ≃+* E) (v : HeightOneSpectrum (𝓞 E)) : (conjSrc c v).adicCompletion E →+* v.adicCompletion E :=
  (exists_finCompl_map c (conjPl_conjSrc c v)).choose

theorem conjLoc_spec (c : E ≃+* E) (v : HeightOneSpectrum (𝓞 E)) : Continuous (conjLoc c v) ∧
    (∀ k : E, conjLoc c v (algebraMap E _ k) = algebraMap E _ (c k)) ∧ ∀ x, Valued.v (conjLoc c v x) = Valued.v x :=
  (exists_finCompl_map c (conjPl_conjSrc c v)).choose_spec

def conjFin (c : E ≃+* E) : Af E →+* Af E :=
  RestrictedProduct.mapAlongRingHom (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) (conjSrc c) (conjSrc_injective c).tendsto_cofinite (conjLoc c)
    (Filter.Eventually.of_forall fun v x hx => ((conjLoc_spec c v).2.2 x).trans_le hx)

theorem pLoc_conjFin (c : E ≃+* E) (x : Af E) (v : HeightOneSpectrum (𝓞 E)) :
    pLoc E v (conjFin c x) = conjLoc c v (pLoc E (conjSrc c v) x) := rfl

theorem conjFin_algebraMap (c : E ≃+* E) (k : E) : conjFin c (algebraMap E (Af E) k) = algebraMap E (Af E) (c k) :=
  FiniteAdeleRing.ext _ fun v => (conjLoc_spec c v).2.1 k

theorem continuous_conjFin (c : E ≃+* E) : Continuous (conjFin c) :=
  RestrictedProduct.mapAlong_continuous (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) (conjSrc c) (conjSrc_injective c).tendsto_cofinite
    (fun j r => conjLoc c j r) (Filter.Eventually.of_forall fun v x hx => ((conjLoc_spec c v).2.2 x).trans_le hx)
    fun v => (conjLoc_spec c v).1

end Conj

theorem pInf_complexConj {E : Type} [Field E] [NumberField E] [IsCMField E] (x : E) :
    pInf E (algebraMap E (Ad E) (IsCMField.complexConj E x)) = star (pInf E (algebraMap E (Ad E) x)) := by
  funext w
  rw [Pi.star_apply, pInf_algebraMap, pInf_algebraMap]
  exact IsCMField.complexEmbedding_complexConj E _ x

end GlobalTheory.CuspRep
