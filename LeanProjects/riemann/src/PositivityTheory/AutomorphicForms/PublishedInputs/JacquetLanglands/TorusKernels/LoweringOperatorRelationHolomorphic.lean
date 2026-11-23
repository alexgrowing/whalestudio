import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc Topology
open scoped Matrix

namespace UpperTheory.Esk.HolomorphicVectorLemmas

section Cent
open UpperTheory.V.TR

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem infGL_scalar (u : (Rinf F)ˣ) :
    infGL F 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = Matrix.GeneralLinearGroup.scalar (Fin 2) (infId F u) := by
  have h : ∀ x, pInf F (sInf F x) = x := fun x => (infEq F).symm_apply_apply x
  have h1 : pInf F (infId F u : Ideles F) = u := by
    change pInf F (1 - sInf F 1 + sInf F _) = _
    simp [h]
  have h2 : pFin F (infId F u : Ideles F) = 1 := by
    change (1 : Af F) - 0 + 0 = 1
    simp
  refine ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [TR.pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

theorem fin_expU {ω : HChar F} (h : IsOfFinOrder ω) (z : Rinf F) : ω.1 (infId F (expU z)) = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : expU z = expU ((n : ℝ)⁻¹ • z) ^ n := by
    refine Units.ext (funext fun i => ?_)
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply, expU_val, ← Real.exp_nat_mul, Pi.smul_apply, smul_eq_mul]
    congr 1
    field_simp
  rw [e1, map_pow, map_pow]
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact DFunLike.congr_fun e2 _

theorem lie_scalar {k c} {ω : HChar F} (h : IsOfFinOrder ω)
    {φ : Sm F 2} (hφ : UpperTheory.Esk.IsHolV k c ω φ) (z : Rinf F) : lie F 2 (toL (Matrix.scalar (Fin 2) z)) φ = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  have h1 := hasDerivAt_curve φ g (fun t => Matrix.GeneralLinearGroup.scalar (Fin 2) (expU (t • z)))
    (toL (Matrix.scalar (Fin 2) z)) (by simp [TR.expU_zero]) (by
      refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
      by_cases e : i = j
      · subst e
        have := ((hasDerivAt_id (0 : ℝ)).mul_const (z v)).exp
        simpa using this
      · simpa [Matrix.diagonal_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have h2 : (fun t : ℝ => φ.1 (g * infGL F 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) (expU (t • z))))) = fun _ => φ.1 g := by
    funext t
    rw [infGL_scalar, ← Matrix.GeneralLinearGroup.scalar_commute, hφ.cent, fin_expU h]
    simp
  rw [h2] at h1
  exact h1.unique (hasDerivAt_const _ _)

theorem cent0 {k c} {ω : HChar F} (h : IsOfFinOrder ω) {φ : Sm F 2} (hφ : UpperTheory.Esk.IsHolV k c ω φ) (v : InfinitePlace F) :
    Eop v 0 0 φ + Eop v 1 1 φ = 0 := by
  classical
  rw [← lie_scalar h hφ (Pi.single v 1), TR.Eop, TR.Eop, ← LinearMap.add_apply, ← map_add]
  congr 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end Cent

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem lowering_operator_relation_holomorphic {k c} {ω : HChar F} (h : IsOfFinOrder ω) {φ : TR.Sm F 2} (hφ : IsHolV k c ω φ) (v : InfinitePlace F)
    (g : GA F 2) : (TR.Eop v 0 0 φ).1 g = Complex.I * (TR.Eop v 0 1 φ).1 g + (k v : ℂ) / 2 * φ.1 g := by
  have h0 := congrArg (fun ψ : TR.Sm F 2 => ψ.1 g) (cent0 h hφ v)
  have h1 := congrArg (fun ψ : TR.Sm F 2 => ψ.1 g) (hφ.wt v)
  have h2 := congrArg (fun ψ : TR.Sm F 2 => ψ.1 g) (hφ.low v)
  simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Submodule.coe_zero, Pi.zero_apply] at h0 h1 h2
  linear_combination (1 / 2 : ℂ) * h0 + (1 / 2 : ℂ) * h2 - (Complex.I / 2) * h1 - ((k v : ℂ) / 2 * φ.1 g) * Complex.I_mul_I

open Classical in

def E (v : InfinitePlace F) (i j : Fin 2) : TR.Lie F 2 := TR.toL (Matrix.single i j (Pi.single v (1 : ℝ) : TR.Rinf F))

theorem Eop_val (v : InfinitePlace F) (i j : Fin 2) (φ : TR.Sm F 2) (g : GA F 2) :
    (TR.Eop v i j φ).1 g = TR.lieD (E v i j) φ.1 g := by
  rw [← TR.lie_apply]
  rfl

def pP (t : ℂ) (ht : t.im ≠ 0) : P := ⟨t, ht⟩

omit [NumberField F] [IsTotallyReal F] in
@[simp] theorem pP_val (t : ℂ) (ht : t.im ≠ 0) : (pP t ht).1 = t := rfl

def yU (z : X (InfinitePlace F)) : (TR.Rinf F)ˣ where
  val v := (z v).1.im
  inv v := ((z v).1.im)⁻¹
  val_inv := funext fun v => mul_inv_cancel₀ (z v).2
  inv_val := funext fun v => inv_mul_cancel₀ (z v).2

def xR (z : X (InfinitePlace F)) : TR.Rinf F := fun v => (z v).1.re

def A (z : X (InfinitePlace F)) : GL (Fin 2) (TR.Rinf F) := aff (yU z) (xR z)

theorem A_val (z : X (InfinitePlace F)) : (A z).val = !![fun v => (z v).1.im, fun v => (z v).1.re; 0, 1] := rfl

theorem gv_A (z : X (InfinitePlace F)) (v : InfinitePlace F) : gv v (A z) • iP = z v := by
  apply Subtype.ext
  rw [coe_smul]
  have e1 : num (gv v (A z)) iP.1 = (z v).1 := by
    apply Complex.ext <;> simp [num, gv, A_val, iP]
  have e2 : den (gv v (A z)) iP.1 = 1 := by simp [den, gv, A_val, iP]
  rw [e1, e2, div_one]

theorem automorphy_factor_diagonal_point (z : X (InfinitePlace F)) (v : InfinitePlace F) (n : ℕ) :
    j1 n (gv v (A z)) iP = ((|(z v).1.im| ^ (-(n : ℝ) / 2) : ℝ) : ℂ) := by
  have e2 : den (gv v (A z)) iP.1 = 1 := by simp [den, gv, A_val, iP]
  have e3 : (gv v (A z)).val.det = (z v).1.im := by
    rw [det_eq]; simp [gv, A_val]
  rw [j1, e2, e3, one_pow, one_mul]

theorem f_eq {k : InfinitePlace F → ℕ} {f : X (InfinitePlace F) × GF F → ℂ} {φ : GA F 2 → ℂ} (h : Rel k f φ)
    (z : X (InfinitePlace F)) (x : GF F) :
    f (z, x) = φ (TR.infGL F 2 (A z) * finGL F 2 x) * ∏ v, ((|(z v).1.im| ^ (-(k v : ℝ) / 2) : ℝ) : ℂ) := by
  have h1 := h (A z) x
  have e : (fun v => gv v (A z) • iP) = z := funext (gv_A z)
  rw [e] at h1
  rw [← h1]
  congr 1
  exact Finset.prod_congr rfl fun v _ => automorphy_factor_diagonal_point z v (k v)

theorem continuous_A : Continuous fun z : X (InfinitePlace F) => TR.toL (A z).val := by
  have hc : ∀ u, Continuous fun z : X (InfinitePlace F) => (z u).1 := fun u =>
    continuous_subtype_val.comp (continuous_apply u)
  refine continuous_pi fun i => continuous_pi fun j => continuous_pi fun u => ?_
  fin_cases i <;> fin_cases j
  · exact Complex.continuous_im.comp (hc u)
  · exact Complex.continuous_re.comp (hc u)
  · exact continuous_const
  · exact continuous_const

theorem hasDerivAt_rpow_abs (q : ℝ) {b : ℝ} (hb : b ≠ 0) : HasDerivAt (fun s : ℝ => |s| ^ q) (q * |b| ^ q / b) b := by
  rcases lt_or_gt_of_ne hb with h | h
  · have h1 : HasDerivAt (fun s : ℝ => (-s) ^ q) (q * (-b) ^ (q - 1) * (-1)) b :=
      (Real.hasDerivAt_rpow_const (Or.inl (neg_ne_zero.2 hb))).comp b (hasDerivAt_neg b)
    have e : (fun s : ℝ => |s| ^ q) =ᶠ[𝓝 b] fun s => (-s) ^ q :=
      (eventually_lt_nhds h).mono fun s hs => by simp only [abs_of_neg hs]
    refine (h1.congr_of_eventuallyEq e).congr_deriv ?_
    rw [abs_of_neg h, Real.rpow_sub_one (neg_ne_zero.2 hb), div_neg]
    ring
  · have h1 : HasDerivAt (fun s : ℝ => s ^ q) (q * b ^ (q - 1)) b := Real.hasDerivAt_rpow_const (Or.inl hb)
    have e : (fun s : ℝ => |s| ^ q) =ᶠ[𝓝 b] fun s => s ^ q :=
      (eventually_gt_nhds h).mono fun s hs => by simp only [abs_of_pos hs]
    refine (h1.congr_of_eventuallyEq e).congr_deriv ?_
    rw [abs_of_pos h, Real.rpow_sub_one hb]
    ring

theorem cr {G : ℂ → ℂ} {L : ℂ →L[ℝ] ℂ} {t0 : ℂ} (h : HasFDerivAt G L t0) (hI : L Complex.I = Complex.I * L 1) :
    DifferentiableAt ℂ G t0 := by
  have e : (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (L 1)).restrictScalars ℝ = L := by
    refine ContinuousLinearMap.ext fun w => ?_
    have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
      apply Complex.ext <;> simp
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, smul_eq_mul]
    conv_rhs => rw [hw]
    rw [map_add, map_smul, map_smul, hI, Complex.real_smul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im w]
    ring
  exact (hasFDerivAt_of_restrictScalars ℝ h e).differentiableAt

theorem rmul_E (v : InfinitePlace F) (j : Fin 2) (M : GL (Fin 2) (TR.Rinf F)) (hM : M 1 0 = 0) :
    TR.rmul (E v 0 j) (TR.toL M.val) = (M 0 0 v) • E v 0 j := by
  classical
  funext a b u
  change (Matrix.of (TR.toL M.val) * Matrix.of (E v 0 j)) a b u = _
  by_cases hu : u = v
  · subst hu
    fin_cases a <;> fin_cases b <;> fin_cases j <;>
      simp [E, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, hM]
  · fin_cases a <;> fin_cases b <;> fin_cases j <;>
      simp [E, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, hM, Pi.single_apply, hu]

theorem sepHol {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {ω : HChar F} {φ : TR.Sm F 2} (hω : IsOfFinOrder ω)
    (hφ : IsHolV k c ω φ) {f : X (InfinitePlace F) × GF F → ℂ} (hf : Rel k f φ.1) (x : GF F) :
    SepHol fun z => f (z, x) := by
  classical
  set g := finGL F 2 x with hg
  have hfe : ∀ z, f (z, x) = TR.chart φ.1 g (TR.toL (A z).val) * ∏ u, ((|(z u).1.im| ^ (-(k u : ℝ) / 2) : ℝ) : ℂ) := by
    intro z
    rw [f_eq hf, TR.infGL_comm, TR.chart_val]
  refine ⟨?_, fun z v => ?_⟩
  · have e : (fun z => f (z, x)) = fun z => TR.chart φ.1 g (TR.toL (A z).val) *
        ∏ u, ((|(z u).1.im| ^ (-(k u : ℝ) / 2) : ℝ) : ℂ) := funext hfe
    rw [e]
    refine Continuous.mul ?_ ?_
    · exact continuous_iff_continuousAt.2 fun z =>
        ContinuousAt.comp (f := fun z => TR.toL (A z).val) (TR.contDiffAt_chart φ.2 g (TR.val_mem_invSet (A z))).continuousAt
          continuous_A.continuousAt
    · exact continuous_finset_prod _ fun u _ => Complex.continuous_ofReal.comp
        ((continuous_abs.comp (Complex.continuous_im.comp (continuous_subtype_val.comp (continuous_apply u)))).rpow_const
          fun z => Or.inl (abs_ne_zero.2 (z u).2))
  · intro t0 ht0
    have ht0' : t0.im ≠ 0 := ht0
    set q : ℝ := -(k v : ℝ) / 2 with hq
    set C : ℂ := ∏ u ∈ Finset.univ.erase v, ((|(z u).1.im| ^ (-(k u : ℝ) / 2) : ℝ) : ℂ) with hC
    set L0 : ℂ →L[ℝ] TR.Lie F 2 := Complex.reCLM.smulRight (E v 0 1) + Complex.imCLM.smulRight (E v 0 0) with hL0
    set B : TR.Lie F 2 := TR.toL (A z).val - L0 (z v).1 with hB0
    have hB : ∀ t (ht : t.im ≠ 0), TR.toL (A (Function.update z v (pP t ht))).val = B + L0 t := by
      intro t ht
      funext i j u
      by_cases hu : u = v
      · subst hu
        fin_cases i <;> fin_cases j <;>
          simp [B, L0, E, A_val, Matrix.vecHead, Matrix.vecTail, Pi.single_apply, Matrix.single_apply]
      · fin_cases i <;> fin_cases j <;>
          simp [B, L0, E, A_val, hu, Function.update_of_ne hu, Pi.single_apply, Matrix.vecHead, Matrix.vecTail, Matrix.single_apply]
    have hN : ∀ t (ht : t.im ≠ 0), ∏ u, ((|(Function.update z v (pP t ht) u).1.im| ^ (-(k u : ℝ) / 2) : ℝ) : ℂ) =
        ((|t.im| ^ q : ℝ) : ℂ) * C := by
      intro t ht
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v), Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun u hu => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hu)]
    set G : ℂ → ℂ := fun t => TR.chart φ.1 g (B + L0 t) * (((|t.im| ^ q : ℝ) : ℂ) * C) with hG0
    have hEq : ext1 (fun t : P => f (Function.update z v t, x)) =ᶠ[𝓝 t0] G := by
      filter_upwards [(isOpen_ne_fun Complex.continuous_im continuous_const).mem_nhds ht0'] with t ht
      have ht' : t.im ≠ 0 := ht
      rw [ext1, dif_pos ht']
      change f (Function.update z v (pP t ht'), x) = G t
      rw [hfe, hB t ht', hN t ht']
    refine (DifferentiableAt.congr_of_eventuallyEq ?_ hEq).differentiableWithinAt
    set A0 := A (Function.update z v (pP t0 ht0')) with hA0
    have hx0e : B + L0 t0 = TR.toL A0.val := (hB t0 ht0').symm
    have hx0 : B + L0 t0 ∈ TR.invSet F 2 := by rw [hx0e]; exact TR.val_mem_invSet _
    set D := fderiv ℝ (TR.chart φ.1 g) (B + L0 t0) with hD
    have hCd : HasFDerivAt (TR.chart φ.1 g) D (B + L0 t0) :=
      ((TR.contDiffAt_chart φ.2 g hx0).differentiableAt (by simp)).hasFDerivAt
    have hM : HasFDerivAt (fun t => B + L0 t) L0 t0 := L0.hasFDerivAt.const_add B
    have him : HasFDerivAt (fun t : ℂ => t.im) Complex.imCLM t0 := Complex.imCLM.hasFDerivAt
    have hn1 := (hasDerivAt_rpow_abs q ht0').comp_hasFDerivAt t0 him
    have hn2 : HasFDerivAt (fun t : ℂ => ((|t.im| ^ q : ℝ) : ℂ)) _ t0 := Complex.ofRealCLM.hasFDerivAt.comp t0 hn1
    have hn3 := hn2.mul (hasFDerivAt_const C t0)
    have hGd : HasFDerivAt G _ t0 := (hCd.comp t0 hM).mul hn3
    have hA00 : A0 0 0 v = t0.im := by simp [hA0, A_val]
    have hA10 : A0 1 0 = 0 := by simp [hA0, A_val]
    have hp : TR.chart φ.1 g (B + L0 t0) = φ.1 (g * TR.infGL F 2 A0) := by rw [hx0e, TR.chart_val]
    have hDj : ∀ j : Fin 2, (t0.im : ℂ) * D (E v 0 j) = (TR.Eop v 0 j φ).1 (g * TR.infGL F 2 A0) := by
      intro j
      have h1 := TR.chart_lieD φ.2 (E v 0 j) g hx0
      rw [hx0e, TR.chart_val, rmul_E v j A0 hA10, hA00, ← hx0e, map_smul] at h1
      rw [Eop_val, h1, Complex.real_smul]
    have hL1 : L0 1 = E v 0 1 := by simp [hL0]
    have hLI : L0 Complex.I = E v 0 0 := by simp [hL0]
    have hrel := lowering_operator_relation_holomorphic hω hφ v (g * TR.infGL F 2 A0)
    refine cr hGd ?_
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, hL1, hLI,
      smul_zero, zero_add, smul_eq_mul]
    have hI1 : Complex.imCLM Complex.I = 1 := by simp
    have hI0 : Complex.imCLM (1 : ℂ) = 0 := by simp
    have hof : ∀ r : ℝ, Complex.ofRealCLM r = (r : ℂ) := fun r => rfl
    rw [hI1, hI0, hof, hof, hp]
    have hb : (t0.im : ℂ) ≠ 0 := by exact_mod_cast ht0'
    have h00 := hDj 0
    have h01 := hDj 1
    rw [hrel] at h00
    have hD00 : D (E v 0 0) = (Complex.I * (TR.Eop v 0 1 φ).1 (g * TR.infGL F 2 A0) + (k v : ℂ) / 2 * φ.1 (g * TR.infGL F 2 A0)) /
        (t0.im : ℂ) := by rw [eq_div_iff hb, mul_comm]; exact h00
    have hD01 : D (E v 0 1) = (TR.Eop v 0 1 φ).1 (g * TR.infGL F 2 A0) / (t0.im : ℂ) := by
      rw [eq_div_iff hb, mul_comm]; exact h01
    have hqc : (q : ℂ) = -(k v : ℂ) / 2 := by rw [hq]; push_cast; ring
    set R : ℝ := |t0.im| ^ q with hR
    rw [hD00, hD01]
    push_cast
    linear_combination (φ.1 (g * TR.infGL F 2 A0) * C * (R : ℂ) / (t0.im : ℂ)) * hqc

end UpperTheory.Esk.HolomorphicVectorLemmas

theorem UpperTheory.Esk.hyperbolic_kernel_measurable_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.H1b := by
  intro _ _ _ F _ _ _ k c ω φ hω hφ f hf x
  exact UpperTheory.Esk.HolomorphicVectorLemmas.sepHol hω hφ hf x
