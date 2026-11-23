import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Wc Topology
open scoped Matrix

namespace UpperTheory.Esk.ArchimedeanEmbeddingLemmas

open UpperTheory.Esk

private noncomputable def cR (i j : Fin 2) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.proj i)

private noncomputable def cC (i j : Fin 2) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (cR i j)

private theorem cR_apply (i j : Fin 2) (x : Fin 2 → Fin 2 → ℝ) : cR i j x = x i j := rfl
private theorem cC_apply (i j : Fin 2) (x : Fin 2 → Fin 2 → ℝ) : cC i j x = (x i j : ℂ) := rfl

theorem key (k : ℕ) (F : ℂ → ℂ) (F' : ℂ) (hF : HasDerivAt F F' Complex.I) (x0 : Fin 2 → Fin 2 → ℝ)
    (h00 : x0 0 0 = 1) (h01 : x0 0 1 = 0) (h10 : x0 1 0 = 0) (h11 : x0 1 1 = 1) :
    ∃ L : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℂ,
      HasFDerivAt (fun x : Fin 2 → Fin 2 → ℝ =>
        (((x 0 0 * x 1 1 - x 0 1 * x 1 0) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * ((x 1 0 : ℂ) * Complex.I + x 1 1) ^ (-(k : ℤ)) *
          F (((x 0 0 : ℂ) * Complex.I + x 0 1) * ((x 1 0 : ℂ) * Complex.I + x 1 1)⁻¹)) L x0 ∧
      ∀ v : Fin 2 → Fin 2 → ℝ, L v = (k : ℂ) / 2 * (v 0 0 + v 1 1) * F Complex.I - k * (v 1 0 * Complex.I + v 1 1) * F Complex.I +
        (v 0 0 * Complex.I + v 0 1 + v 1 0 - v 1 1 * Complex.I) * F' := by
  have r : ∀ i j, HasFDerivAt (fun x : Fin 2 → Fin 2 → ℝ => x i j) (cR i j) x0 := fun i j => (cR i j).hasFDerivAt
  have c : ∀ i j, HasFDerivAt (fun x : Fin 2 → Fin 2 → ℝ => (x i j : ℂ)) (cC i j) x0 := fun i j => (cC i j).hasFDerivAt
  have hd := ((r 0 0).fun_mul (r 1 1)).fun_sub ((r 0 1).fun_mul (r 1 0))
  have hd2 := hd.rpow_const (p := (k : ℝ) / 2) (Or.inl (by simp [h00, h01, h10, h11]))
  have hd3 := Complex.ofRealCLM.hasFDerivAt.comp x0 hd2
  have hden := ((c 1 0).mul_const Complex.I).fun_add (c 1 1)
  have hnum := ((c 0 0).mul_const Complex.I).fun_add (c 0 1)
  have hne : (x0 1 0 : ℂ) * Complex.I + x0 1 1 ≠ 0 := by simp [h10, h11]
  have hz := (hasDerivAt_zpow (-(k : ℤ)) _ (Or.inl hne)).comp_hasFDerivAt x0 hden
  have hi := (hasDerivAt_inv hne).comp_hasFDerivAt x0 hden
  have hq := hnum.fun_mul hi
  have hF2 : HasDerivAt F F' (((x0 0 0 : ℂ) * Complex.I + x0 0 1) * ((x0 1 0 : ℂ) * Complex.I + x0 1 1)⁻¹) := by
    simpa [h00, h01, h10, h11] using hF
  have hc := hF2.comp_hasFDerivAt x0 hq
  refine ⟨_, (hd3.fun_mul hz).fun_mul hc, fun v => ?_⟩
  simp [h00, h01, h10, h11, cR_apply, cC_apply]
  linear_combination (-(v 1 0 : ℂ) * F') * Complex.I_mul_I

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

open Classical in

def iv (v : InfinitePlace F) (y : Fin 2 → Fin 2 → ℝ) : TR.Lie F 2 := fun a b w => if w = v then y a b else 0

def ivL (v : InfinitePlace F) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] TR.Lie F 2 :=
  LinearMap.toContinuousLinearMap
    { toFun := iv v
      map_add' := fun x y => by
        funext a b w
        by_cases h : w = v <;> simp [iv, h]
      map_smul' := fun s x => by
        funext a b w
        by_cases h : w = v <;> simp [iv, h] }

theorem ivL_apply (v : InfinitePlace F) (y : Fin 2 → Fin 2 → ℝ) : ivL v y = iv v y := rfl

open Classical in

def i0 (v : InfinitePlace F) : TR.Lie F 2 := fun a b w => if w = v then 0 else (1 : Matrix (Fin 2) (Fin 2) ℝ) a b

theorem embedded_archimedean_identity_eq_one (v : InfinitePlace F) : i0 v + ivL v (Matrix.of.symm 1) = TR.oneL F 2 := by
  funext a b w
  by_cases h : w = v
  · subst h
    simp [i0, ivL_apply, iv, TR.oneL, Matrix.one_apply, ite_apply]
  · simp [i0, ivL_apply, iv, TR.oneL, Matrix.one_apply, ite_apply, h]

open Classical in
theorem map_embedded_archimedean_matrix (v : InfinitePlace F) (x : Fin 2 → Fin 2 → ℝ) (w : InfinitePlace F) :
    (Matrix.of (i0 v + ivL v x)).map (fun r : TR.Rinf F => r w) = if w = v then Matrix.of x else 1 := by
  ext a b
  by_cases h : w = v
  · subst h
    simp [i0, ivL_apply, iv]
  · simp [i0, ivL_apply, iv, h]

theorem sv (i j a b : Fin 2) : (Matrix.of.symm (Matrix.single i j (1 : ℝ))) a b = if i = a ∧ j = b then 1 else 0 := rfl

theorem at_point (hB : B1b) (k : InfinitePlace F → ℕ) (f : X (InfinitePlace F) × GF F → ℂ) (φ : GA F 2 → ℂ)
    (hφ : φ ∈ TR.Sm F 2) (hhol : ∀ x, SepHol fun z => f (z, x)) (hrel : Rel k f φ) (v : InfinitePlace F) (G : GA F 2) :
    ∃ F0 F' : ℂ, φ G = F0 ∧ ∀ y : Fin 2 → Fin 2 → ℝ, TR.lieD (iv v y) φ G =
      (k v : ℂ) / 2 * (y 0 0 + y 1 1) * F0 - k v * (y 1 0 * Complex.I + y 1 1) * F0 +
        (y 0 0 * Complex.I + y 0 1 + y 1 0 - y 1 1 * Complex.I) * F' := by
  classical
  set g := Matrix.GeneralLinearGroup.map (TR.pInf F) G with hg
  set xf := Matrix.GeneralLinearGroup.map (pFin F) G with hxf
  have hG : TR.infGL F 2 g * finGL F 2 xf = G := TR.infGL_mul_finGL G
  set z : X (InfinitePlace F) := fun w => gv w g • iP with hz
  set gw := gv v g with hgw
  set C0 : ℂ := ∏ w ∈ Finset.univ.erase v, j1 (k w) (gv w g) iP with hC0
  have hC0ne : C0 ≠ 0 := Finset.prod_ne_zero_iff.2 fun w _ => hB.2.1 _ _ _
  set c1 : ℂ := ((|gw.val.det| ^ (-(k v : ℝ) / 2) : ℝ) : ℂ) with hc1
  have hc1ne : c1 ≠ 0 := by
    rw [hc1, Complex.ofReal_ne_zero]
    exact (Real.rpow_pos_of_pos (abs_pos.2 gw.det_ne_zero) _).ne'
  set Φ : P → ℂ := fun t => f (Function.update z v t, xf) with hΦ
  set Hf : ℂ → ℂ := fun τ => ext1 Φ (num gw τ / den gw τ) / (den gw τ ^ k v * c1 * C0) with hHf
  have hI : (Complex.I).im ≠ 0 := by simp
  have hden : den gw Complex.I ≠ 0 := den_ne gw hI
  have hdiff : DifferentiableAt ℂ Hf Complex.I := by
    have hn : DifferentiableAt ℂ (num gw) Complex.I := by unfold num; fun_prop
    have hd : DifferentiableAt ℂ (den gw) Complex.I := by unfold den; fun_prop
    have h1 : DifferentiableAt ℂ (fun τ => num gw τ / den gw τ) Complex.I := hn.div hd hden
    have h2 : DifferentiableAt ℂ (ext1 Φ) (num gw Complex.I / den gw Complex.I) := by
      have hopen : IsOpen {t : ℂ | t.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
      refine ((hhol xf).2 z v).differentiableAt (hopen.mem_nhds ?_)
      show (num gw Complex.I / den gw Complex.I).im ≠ 0
      rw [im_div]
      exact div_ne_zero (mul_ne_zero gw.det_ne_zero hI) (by simpa using hden)
    refine (h2.comp Complex.I h1).div ((hd.pow _).mul_const _ |>.mul_const _) ?_
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hden) hc1ne) hC0ne
  obtain ⟨L, hL, hv⟩ := key (k v) Hf _ hdiff.hasDerivAt (Matrix.of.symm 1) (by simp) (by simp) (by simp) (by simp)
  have hev : (fun x => TR.chart φ G (i0 v + ivL v x)) =ᶠ[𝓝 (Matrix.of.symm 1)] fun x : Fin 2 → Fin 2 → ℝ =>
      (((x 0 0 * x 1 1 - x 0 1 * x 1 0) ^ ((k v : ℝ) / 2) : ℝ) : ℂ) * ((x 1 0 : ℂ) * Complex.I + x 1 1) ^ (-(k v : ℤ)) *
        Hf (((x 0 0 : ℂ) * Complex.I + x 0 1) * ((x 1 0 : ℂ) * Complex.I + x 1 1)⁻¹) := by
    have hc : Continuous fun x : Fin 2 → Fin 2 → ℝ => x 0 0 * x 1 1 - x 0 1 * x 1 0 := by fun_prop
    have ho : {x : Fin 2 → Fin 2 → ℝ | 0 < x 0 0 * x 1 1 - x 0 1 * x 1 0} ∈ 𝓝 (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) ℝ)) :=
      (isOpen_lt continuous_const hc).mem_nhds (by simp)
    refine Filter.eventually_of_mem ho fun x hx => ?_
    have hx' : 0 < x 0 0 * x 1 1 - x 0 1 * x 1 0 := hx
    have hdx : (Matrix.of x).det = x 0 0 * x 1 1 - x 0 1 * x 1 0 := by rw [Matrix.det_fin_two]; rfl
    have hu : IsUnit (Matrix.of (i0 v + ivL v x)) := by
      rw [Matrix.isUnit_iff_isUnit_det, Pi.isUnit_iff]
      intro w
      rw [show (Matrix.of (i0 v + ivL v x)).det w = (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) w) (Matrix.of (i0 v + ivL v x)).det from rfl,
        RingHom.map_det]
      change IsUnit ((Matrix.of (i0 v + ivL v x)).map (fun r : TR.Rinf F => r w)).det
      rw [map_embedded_archimedean_matrix]
      split_ifs
      · exact isUnit_iff_ne_zero.2 (by rw [hdx]; exact hx'.ne')
      · simp
    set U := hu.unit with hU
    have hUv : ∀ w a b, (gv w U).val a b = (Matrix.of (i0 v + ivL v x)).map (fun r : TR.Rinf F => r w) a b := by
      intro w a b
      change (U : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) a b w = _
      rw [hU, hu.unit_spec]
      rfl
    have hU1 : ∀ w, w ≠ v → gv w U = 1 := fun w hw => Units.ext (Matrix.ext fun a b => by
      rw [hUv, map_embedded_archimedean_matrix, if_neg hw]; rfl)
    set m := gv v U with hm
    have hmv : ∀ a b, m.val a b = x a b := fun a b => by rw [hm, hUv, map_embedded_archimedean_matrix, if_pos rfl]; rfl
    have hmdet : m.val.det = x 0 0 * x 1 1 - x 0 1 * x 1 0 := by rw [Matrix.det_fin_two, hmv, hmv, hmv, hmv]
    simp only [TR.chart, dif_pos hu]
    rw [← hU]
    have e1 : G * TR.infGL F 2 U = TR.infGL F 2 (g * U) * finGL F 2 xf := by
      rw [← hG, mul_assoc, ← TR.infGL_comm, ← mul_assoc, ← map_mul]
    have hr := hrel (g * U) xf
    rw [← e1] at hr
    have hprod : ∏ w, j1 (k w) (gv w (g * U)) iP = j1 (k v) gw (m • iP) * j1 (k v) m iP * C0 := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), map_mul, ← hB.1]
      congr 1
      refine Finset.prod_congr rfl fun w hw => ?_
      rw [map_mul, hU1 w (Finset.ne_of_mem_erase hw), mul_one]
    have hpt : (fun w => gv w (g * U) • iP) = Function.update z v (gw • (m • iP)) := by
      funext w
      by_cases h : w = v
      · subst h
        rw [Function.update_self, map_mul, mul_smul]
      · rw [Function.update_of_ne h, map_mul, hU1 w h, mul_one]
    rw [hprod, hpt] at hr
    have hne1 := hB.2.1 (k v) gw (m • iP)
    have hne2 := hB.2.1 (k v) m iP
    have hφG : φ (G * TR.infGL F 2 U) = Φ (gw • (m • iP)) / (j1 (k v) gw (m • iP) * j1 (k v) m iP * C0) :=
      eq_div_of_mul_eq (mul_ne_zero (mul_ne_zero hne1 hne2) hC0ne) hr
    have hτ : ((x 0 0 : ℂ) * Complex.I + x 0 1) * ((x 1 0 : ℂ) * Complex.I + x 1 1)⁻¹ = (m • iP).1 := by
      rw [coe_smul, num, den, hmv, hmv, hmv, hmv, div_eq_mul_inv]
      rfl
    have hdenm : den m iP.1 = (x 1 0 : ℂ) * Complex.I + x 1 1 := by rw [den, hmv, hmv]; rfl
    have hdenne : (x 1 0 : ℂ) * Complex.I + x 1 1 ≠ 0 := by rw [← hdenm]; exact den_ne m (by simp [iP])
    have hHf : Hf (m • iP).1 = Φ (gw • (m • iP)) / (j1 (k v) gw (m • iP) * C0) := by
      simp only [hHf]
      rw [ext1, dif_pos (show (num gw (m • iP).1 / den gw (m • iP).1).im ≠ 0 from (gw • (m • iP)).2)]
      rfl
    rw [hτ, hHf, hφG]
    have hj : j1 (k v) m iP = ((x 1 0 : ℂ) * Complex.I + x 1 1) ^ k v *
        (((x 0 0 * x 1 1 - x 0 1 * x 1 0) ^ ((k v : ℝ) / 2) : ℝ) : ℂ)⁻¹ := by
      rw [j1, hdenm, hmdet, abs_of_pos hx', neg_div, Real.rpow_neg hx'.le, Complex.ofReal_inv]
    have hpos : (((x 0 0 * x 1 1 - x 0 1 * x 1 0) ^ ((k v : ℝ) / 2) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hx' _).ne'
    rw [hj, zpow_neg, zpow_natCast]
    field_simp
  have hF0 : φ G = Hf Complex.I := by
    have h1 := hev.eq_of_nhds
    simp only [embedded_archimedean_identity_eq_one, TR.oneL] at h1
    rw [show TR.chart φ G (TR.toL 1) = φ G by
      rw [show (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) = ((1 : GL (Fin 2) (TR.Rinf F)) : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) from rfl,
        TR.chart_val, map_one, mul_one]] at h1
    rw [h1]
    simp
  refine ⟨Hf Complex.I, deriv Hf Complex.I, hF0, fun y => ?_⟩
  have hcomp : HasFDerivAt (fun x => TR.chart φ G (i0 v + ivL v x))
      ((fderiv ℝ (TR.chart φ G) (TR.oneL F 2)).comp (ivL v)) (Matrix.of.symm 1) := by
    have h1 : HasFDerivAt (TR.chart φ G) (fderiv ℝ (TR.chart φ G) (TR.oneL F 2)) (i0 v + ivL v (Matrix.of.symm 1)) := by
      rw [embedded_archimedean_identity_eq_one]
      exact (TR.differentiableAt_chart hφ G).hasFDerivAt
    exact HasFDerivAt.comp (Matrix.of.symm 1) (f := fun x => i0 v + ivL v x) h1 ((ivL v).hasFDerivAt.const_add (i0 v))
  have huniq := hcomp.unique (hL.congr_of_eventuallyEq hev)
  have e : TR.lieD (iv v y) φ G = L y := by
    show (fderiv ℝ (TR.chart φ G) (TR.oneL F 2)) (ivL v y) = L y
    rw [← huniq]
    rfl
  rw [e, hv]

end UpperTheory.Esk.ArchimedeanEmbeddingLemmas

open UpperTheory.Esk.ArchimedeanEmbeddingLemmas in
theorem UpperTheory.Esk.hyperbolic_orbit_summable_proof : UpperTheory.Esk.Osg → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.H2c := by
  intro _ hB _ F _ _ _ k c _ ω χ _ _ _ _ f φ hform hrel h v
  have E : ∀ (i j : Fin 2) G, (TR.Eop v i j (⟨φ, h⟩ : TR.Sm F 2)).1 G = TR.lieD (iv v (Matrix.of.symm (Matrix.single i j 1))) φ G := by
    intro i j G
    rw [TR.Eop, TR.lie_apply]
    congr 1
    funext a b w
    by_cases hw : w = v
    · subst hw
      simp [iv, Matrix.single, ite_apply]
    · simp [iv, Matrix.single, ite_apply, Pi.single_apply, hw]
  constructor
  · refine Subtype.ext (funext fun G => ?_)
    obtain ⟨F0, F', h0, hD⟩ := at_point hB k f φ h (fun x => hform.hol x) hrel v G
    change (TR.Eop v 0 1 (⟨φ, h⟩ : TR.Sm F 2)).1 G - (TR.Eop v 1 0 (⟨φ, h⟩ : TR.Sm F 2)).1 G = Complex.I * k v * φ G
    rw [E, E, hD, hD, h0]
    simp only [sv, eq_false (show (1 : Fin 2) ≠ 0 by decide), eq_false (show (0 : Fin 2) ≠ 1 by decide), eq_self_iff_true,
      and_true, true_and, and_false, false_and, and_self, if_true, if_false, Complex.ofReal_zero, Complex.ofReal_one]
    ring
  · refine Subtype.ext (funext fun G => ?_)
    obtain ⟨F0, F', h0, hD⟩ := at_point hB k f φ h (fun x => hform.hol x) hrel v G
    change (TR.Eop v 0 0 (⟨φ, h⟩ : TR.Sm F 2)).1 G - (TR.Eop v 1 1 (⟨φ, h⟩ : TR.Sm F 2)).1 G =
      Complex.I * ((TR.Eop v 0 1 (⟨φ, h⟩ : TR.Sm F 2)).1 G + (TR.Eop v 1 0 (⟨φ, h⟩ : TR.Sm F 2)).1 G)
    rw [E, E, E, E, hD, hD, hD, hD]
    simp only [sv, eq_false (show (1 : Fin 2) ≠ 0 by decide), eq_false (show (0 : Fin 2) ≠ 1 by decide), eq_self_iff_true,
      and_true, true_and, and_false, false_and, and_self, if_true, if_false, Complex.ofReal_zero, Complex.ofReal_one]
    linear_combination (k v * F0) * Complex.I_mul_I
