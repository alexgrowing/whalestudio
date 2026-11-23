import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBddFormsOfWithSmoothings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaplacianPolynomialKillsHarishChandraFinit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaplacianPolynomialKernelOfPolynomialLaplacian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyMaximalCompactCasimirKillsKType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpGLImageBallMemNhds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
import GroundTheory.AutomorphicForms.HarishChandraRegularity

open NumberField MeasureTheory Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Petersson Formalism.L2.Host
open Filter Topology GlobalTheory.HCAlpha GlobalTheory.ExpDeriv
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.KeepOrth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem exists_poly_central {f : Sm E a} (h : IsAutForm f) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∃ p : Polynomial ℂ, p ≠ 0 ∧ Polynomial.aeval z p f = 0 := by
  have := h.zfin
  let L : Polynomial ℂ →ₗ[ℂ] Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z f) '' Zalg E a) :=
    LinearMap.codRestrict _ (LinearMap.applyₗ f ∘ₗ (Polynomial.aeval z).toLinearMap) fun p =>
      Submodule.subset_span ⟨_, (Algebra.adjoin_le (S := Zalg E a) (Set.singleton_subset_iff.2 hz))
        (Polynomial.aeval_mem_adjoin_singleton ℂ _), rfl⟩
  by_contra! hc
  have hi : Function.Injective L := (injective_iff_map_eq_zero L).2 fun p hp => by
    by_contra h0
    exact hc p h0 (congrArg Subtype.val hp)
  exact Polynomial.not_finite (Module.Finite.of_injective L hi)

theorem exists_kTypes {f : Sm E a} (h : IsAutForm f) : ∃ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W ∧
    ∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k f).1 g) ∈ W := by
  have := h.kfin
  let U := Submodule.span ℂ (Set.range fun k => cptRep E a k f)
  let v : Kinf E a → U := fun k => ⟨cptRep E a k f, Submodule.subset_span ⟨k, rfl⟩⟩
  let T : Module.Dual ℂ U →ₗ[ℂ] (Kinf E a → ℂ) :=
    { toFun := fun l k => l (v k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact ⟨LinearMap.range T, inferInstance, fun g =>
    ⟨(LinearMap.proj g).comp ((Sm E a).subtype.comp U.subtype), rfl⟩⟩

theorem exists_poly_lap {f : Sm E a} (h : IsAutForm f) :
    ∃ p : Polynomial ℂ, p ≠ 0 ∧ Polynomial.aeval (lapOp E a) p f = 0 := by
  obtain ⟨W, hW, hK⟩ := exists_kTypes h
  obtain ⟨q, hq0, hq⟩ := GlobalTheory.HCKTypes.exists_casK_poly E a W hW
  choose r hr0 hr using fun τ : E →+* ℂ => exists_poly_central h (GlobalTheory.CasCentre.cas_Eop_mem_Zalg E a τ)
  let A : Option (E →+* ℂ) → Module.End ℂ (Sm E a) := fun o => o.elim (casKOp E a) fun τ => Formalism.REAL.Cas (Eop τ)
  let c : Option (E →+* ℂ) → ℂ := fun o => o.elim 2 fun _ => 4
  let P : Option (E →+* ℂ) → Polynomial ℂ := fun o => o.elim q r
  have hZ : ∀ τ : E →+* ℂ, ∀ X, Commute (Formalism.REAL.Cas (Eop (a := a) τ)) (lie E a X) := fun τ X =>
    GlobalTheory.CuspRep.Zalg_mul_lie E a X _ (GlobalTheory.CasCentre.cas_Eop_mem_Zalg E a τ)
  have hc : ∀ i j, Commute (A i) (A j) := by
    rintro (_ | τ) (_ | τ')
    · exact Commute.refl _
    · exact (GlobalTheory.GLPoly.commute_casKOp' (hZ τ')).symm
    · exact GlobalTheory.GLPoly.commute_casKOp' (hZ τ)
    · exact GlobalTheory.GLPoly.commute_cas' (hZ τ) τ'
  have hP : ∀ i, P i ≠ 0 := by
    rintro (_ | τ)
    · exact hq0
    · exact hr0 τ
  obtain ⟨p, hp0, hp⟩ := GlobalTheory.CommutingPoly.exists_poly_annihilates_linear_combination A hc c P hP
  refine ⟨p, hp0, ?_⟩
  have e : ∑ i, c i • A i = lapOp E a := by
    rw [GlobalTheory.HCAlpha.lapOp_eq_casKOp_add_cas E a, Fintype.sum_option]; rfl
  rw [← e]
  refine hp f ?_
  rintro (_ | τ)
  · exact hq f hK
  · exact hr τ

section Analytic

open GlobalTheory.HCA GroundTheory.Automorphic

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem analyticOnNhd_along {F : Sm E a} {p : Polynomial ℂ} (hp : p ≠ 0) (hF : Polynomial.aeval (lapOp E a) p F = 0)
    (x : GA E a) (X : Lie E a) : AnalyticOnNhd ℝ (fun t : ℝ => F.1 (x * infGL E a (expGL X t))) Set.univ := by
  obtain ⟨d, b, P, hPm, -, hP⟩ := solG_of_polyLap E a p hp
  intro t₀ _
  obtain ⟨hf, h0⟩ := (mem_solG _ _).1 (hP F hF (x * infGL E a (expGL X t₀)))
  have han := (glH E a).analyticAt_of_aeval_laplacian_eq_zero (b.map (glH E a).lieEquiv.symm) P hPm ⟨_, hf⟩ h0 1
  let XL : glL E a := ⟨Matrix.of X, Submodule.mem_top⟩
  have hlin : AnalyticAt ℝ (fun t : ℝ => (t - t₀) • XL) t₀ :=
    (analyticAt_id.sub analyticAt_const).smul analyticAt_const
  refine (han.comp_of_eq hlin (by simp)).congr (Filter.Eventually.of_forall fun t => ?_)
  have e : (((glH E a).expG ((t - t₀) • XL) : glG E a) : GL (Fin a) (Cinf E)) = expGL X (t - t₀) := Units.ext rfl
  simp only [Function.comp_apply, glRes, one_mul, e]
  rw [mul_assoc, ← map_mul, ← expGL_add, add_sub_cancel]

end Analytic

theorem iteratedDeriv_along (X : Lie E a) (x : GA E a) (k : ℕ) (F : Sm E a) :
    iteratedDeriv k (fun t : ℝ => F.1 (x * infGL E a (expGL X t))) =
      fun t => ((lie E a X ^ k) F).1 (x * infGL E a (expGL X t)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ, ih, pow_succ']
    exact funext fun t => (hasDerivAt_along X _ x t).deriv

theorem eq_zero_along {F : Sm E a} {x : GA E a} {X : Lie E a}
    (hf : AnalyticOnNhd ℝ (fun t : ℝ => F.1 (x * infGL E a (expGL X t))) Set.univ)
    (h0 : ∀ k : ℕ, ((lie E a X ^ k) F).1 x = 0) (t : ℝ) : F.1 (x * infGL E a (expGL X t)) = 0 := by
  obtain ⟨p, r, hp⟩ := hf 0 (Set.mem_univ 0)
  have hF : ∀ n, iteratedFDeriv ℝ n (fun t : ℝ => F.1 (x * infGL E a (expGL X t))) 0 = 0 := by
    intro n
    ext m
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedDeriv_along]
    simp [expGL_zero, h0]
  have hev : (fun t : ℝ => F.1 (x * infGL E a (expGL X t))) =ᶠ[𝓝 0] 0 := by
    filter_upwards [Metric.eball_mem_nhds (0 : ℝ) hp.r_pos] with y hy
    have h := hp.hasSum_iteratedFDeriv hy
    simp only [hF, ContinuousMultilinearMap.zero_apply, smul_zero, zero_add] at h
    exact h.unique hasSum_zero
  exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) hev (Set.mem_univ t)

theorem eq_univ_of_exp {S : Set (GL (Fin a) (Cinf E))} (h1 : 1 ∈ S) (hS : ∀ y ∈ S, ∀ X t, y * expGL X t ∈ S) :
    S = Set.univ := by
  haveI : PreconnectedSpace (GL (Fin a) (Cinf E)) := ⟨by
    rw [← (GlobalTheory.CuspQuot.isOpenEmbedding_val (E := E) (a := a)).isInducing.isPreconnected_image]
    rw [Set.image_univ]
    exact GlobalTheory.AlgInfChar.isPreconnected_invSet (E := E) (a := a)⟩
  have hn : ∀ y : GL (Fin a) (Cinf E), ∀ᶠ z in 𝓝 y, ∃ X, z = y * expGL X 1 := fun y => by
    have h := GlobalTheory.GLFin.expGL_image_ball_mem_nhds E a 1 one_pos
    have h2 : Tendsto (fun z => y⁻¹ * z) (𝓝 y) (𝓝 1) := (continuous_const_mul y⁻¹).tendsto' y 1 (inv_mul_cancel y)
    filter_upwards [h2 h] with z hz
    obtain ⟨X, -, hX⟩ := hz
    exact ⟨X, by rw [show expGL X 1 = y⁻¹ * z from hX, mul_inv_cancel_left]⟩
  refine IsClopen.eq_univ ⟨⟨isOpen_iff_mem_nhds.2 fun y hy => ?_⟩, isOpen_iff_mem_nhds.2 fun y hy => ?_⟩ ⟨1, h1⟩
  · filter_upwards [hn y] with z hz hzS
    obtain ⟨X, rfl⟩ := hz
    have := hS _ hzS X (-1)
    rw [mul_assoc, ← expGL_add, add_neg_cancel, expGL_zero, mul_one] at this
    exact hy this
  · filter_upwards [hn y] with z hz
    obtain ⟨X, rfl⟩ := hz
    exact hS y hy X 1

variable (E a) in

abbrev bas : Module.Basis (Fin (Module.finrank ℝ (Lie E a))) ℝ (Lie E a) := Module.finBasis ℝ (Lie E a)

omit [IsTotallyComplex E] in

def crd (i : Fin (Module.finrank ℝ (Lie E a))) (z : Lie E a) : Lie E a →L[ℝ] ℝ :=
  (LinearMap.toContinuousLinearMap ((bas E a).coord i)).comp (lmul (invL z))

omit [IsTotallyComplex E] in
theorem contDiffOn_crd (i : Fin (Module.finrank ℝ (Lie E a))) : ContDiffOn ℝ (⊤ : ℕ∞) (crd i) (invSet E a) :=
  contDiffOn_clm_apply.2 fun v z hz => ((LinearMap.toContinuousLinearMap ((bas E a).coord i)).contDiff.contDiffAt.comp z
    (GlobalTheory.AutGrowth.contDiff_lmul_uncurry.contDiffAt.comp z
      ((contDiffAt_invL hz).prodMk (contDiffAt_const (c := v))))).contDiffWithinAt

theorem chart_lie (X : Lie E a) (φ : Sm E a) (g : GA E a) (z : Lie E a) :
    chart (lie E a X φ).1 g z = ∑ i, (bas E a).coord i X • chart (lie E a (bas E a i) φ).1 g z := by
  unfold chart
  split_ifs
  · conv_lhs => rw [← (bas E a).sum_repr X]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Finset.sum_apply,
      Module.Basis.coord_apply]
    rfl
  · simp

theorem hasFDerivAt_chart (φ : Sm E a) (g : GA E a) {z : Lie E a} (hz : z ∈ invSet E a) :
    HasFDerivAt (chart φ.1 g) (∑ i, (crd i z).smulRight (chart (lie E a (bas E a i) φ).1 g z)) z := by
  refine ((contDiffAt_chart φ.2 g hz).differentiableAt (by simp)).hasFDerivAt.congr_fderiv ?_
  ext1 v
  have e : rmul (lmul (invL z) v) z = v :=
    Matrix.mul_nonsing_inv_cancel_left _ _ ((Matrix.isUnit_iff_isUnit_det _).1 hz)
  have h := chart_lieD φ.2 (lmul (invL z) v) g hz
  rw [e] at h
  rw [← h]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
  exact chart_lie _ φ g z

variable {ω : HChar E} (μ : Measure (GA E a)) [μ.IsHaarMeasure] {ψ : GA E a → ℂ}

variable (ψ) in

def coef (φ : GA E a → ℂ) (x : GA E a) : ℂ := pet (latticeGL E a) μ (fun g => φ (g * x)) ψ

theorem chart_coef (φ : GA E a → ℂ) (x : GA E a) (z : Lie E a) :
    chart (coef μ ψ φ) x z = ∫ q, chart φ (q.out * x) z * conj (ψ q.out) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) := by
  unfold chart
  split_ifs
  · simp only [coef, pet, descend, mul_assoc]
  · simp

theorem integrable_chart (hω : ω.IsUnitary) (h' : ψ ∈ bddForms E a ω) {φ : GA E a → ℂ} (h : φ ∈ bddForms E a ω)
    (x : GA E a) (z : Lie E a) :
    Integrable (fun q => chart φ (q.out * x) z * conj (ψ q.out)) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) :=
  integrable_mul_conj μ hω (mul_right_mem_bddForms (chart_mem_bddForms h z) x) h'

theorem hasFDerivAt_coef (hω : ω.IsUnitary) (h' : ψ ∈ bddForms E a ω) {φ : Sm E a} (h : φ.1 ∈ bddForms E a ω)
    (hl : ∀ X, (lie E a X φ).1 ∈ bddForms E a ω) (x : GA E a) {z : Lie E a} (hz : z ∈ invSet E a) :
    HasFDerivAt (chart (coef μ ψ φ.1) x)
      (∑ i, (crd i z).smulRight (chart (coef μ ψ (lie E a (bas E a i) φ).1) x z)) z := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  obtain ⟨D, hD⟩ := h'.2.2.2
  choose C hC using fun i => (hl (bas E a i)).2.2.2
  have hs : ∀ᶠ y in 𝓝 z, y ∈ invSet E a ∧ ∀ i, ‖crd i y‖ ≤ ‖crd i z‖ + 1 := by
    refine Filter.Eventually.and (isOpen_invSet.mem_nhds hz) (eventually_all.2 fun i => ?_)
    exact (((contDiffOn_crd i).continuousOn.continuousAt (isOpen_invSet.mem_nhds hz)).norm.eventually_lt_const
      (lt_add_one _)).mono fun _ => le_of_lt
  have hi : ∀ i, Integrable (fun q : Quot (latticeGL E a) => (crd i z).smulRight
      (chart (lie E a (bas E a i) φ).1 (q.out * x) z * conj (ψ q.out))) (GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) :=
    fun i => (ContinuousLinearMap.smulRightL ℝ _ ℂ (crd i z)).integrable_comp (integrable_chart μ hω h' (hl _) x z)
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ)
    (F := fun y q => chart φ.1 (q.out * x) y * conj (ψ q.out))
    (F' := fun y q => ∑ i, (crd i y).smulRight (chart (lie E a (bas E a i) φ).1 (q.out * x) y * conj (ψ q.out)))
    (bound := fun _ => ∑ i, (‖crd i z‖ + 1) * (C i * D)) hs
    (.of_forall fun y => (integrable_chart μ hω h' h x y).1) (integrable_chart μ hω h' h x z)
    (integrable_finset_sum _ fun i _ => hi i).1
    (.of_forall fun q y hy => (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => by
      rw [ContinuousLinearMap.norm_smulRight_apply, norm_mul, Complex.norm_conj]
      exact mul_le_mul (hy.2 i) (mul_le_mul (GlobalTheory.CuspQuot.norm_chart_le (hC i) _ _) (hD _) (norm_nonneg _)
        ((norm_nonneg _).trans (hC i 1))) (by positivity) (by positivity)))
    (integrable_const _)
    (.of_forall fun q y hy => by
      refine ((hasFDerivAt_chart φ (q.out * x) hy.1).mul_const (conj (ψ q.out))).congr_fderiv ?_
      ext1 v
      simp [Finset.mul_sum, mul_comm, mul_left_comm])
  rw [integral_finset_sum _ fun i _ => hi i] at key
  rw [funext (chart_coef μ φ.1 x)]
  refine key.congr_fderiv (Finset.sum_congr rfl fun i _ => ?_)
  rw [chart_coef]
  exact (ContinuousLinearMap.smulRightL ℝ _ ℂ (crd i z)).integral_comp_comm (integrable_chart μ hω h' (hl _) x z)

variable {V : Submodule ℂ (Sm E a)}

theorem coef_mem_Sm (hω : ω.IsUnitary) (h' : ψ ∈ bddForms E a ω) (hV : ∀ φ ∈ V, φ.1 ∈ bddForms E a ω)
    (hl : ∀ X, ∀ φ ∈ V, lie E a X φ ∈ V) {φ : Sm E a} (hφ : φ ∈ V) : coef μ ψ φ.1 ∈ Sm E a := by
  intro x
  have hd := fun φ (hφ : φ ∈ V) z (hz : z ∈ invSet E a) =>
    hasFDerivAt_coef μ hω h' (hV φ hφ) (fun X => hV _ (hl X φ hφ)) x hz
  refine contDiffOn_infty.2 fun n => ?_
  induction n generalizing φ with
  | zero => exact contDiffOn_zero.2 fun z hz => (hd φ hφ z hz).continuousAt.continuousWithinAt
  | succ n ih =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_invSet]
    refine ⟨fun z hz => (hd φ hφ z hz).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    refine ContDiffOn.congr (ContDiffOn.sum fun i _ => ContDiffOn.smulRight ((contDiffOn_crd i).of_le (by
      exact_mod_cast le_top)) (ih (hl (bas E a i) φ hφ))) fun z hz => (hd φ hφ z hz).fderiv

theorem lieD_coef (hω : ω.IsUnitary) (h' : ψ ∈ bddForms E a ω) {φ : Sm E a} (h : φ.1 ∈ bddForms E a ω)
    (hl : ∀ X, (lie E a X φ).1 ∈ bddForms E a ω) (X : Lie E a) :
    lieD X (coef μ ψ φ.1) = coef μ ψ (lie E a X φ).1 := by
  funext x
  have e : ∀ F : GA E a → ℂ, F x = chart F x (oneL E a) := fun F => by simpa using (chart_val F x 1).symm
  have e1 : lmul (invL (oneL E a)) X = X := by
    change (1 : Matrix (Fin a) (Fin a) (Cinf E))⁻¹ * Matrix.of X = Matrix.of X
    simp
  rw [lieD, (hasFDerivAt_coef μ hω h' h hl x (z := oneL E a) isUnit_one).fderiv, e (coef μ ψ _)]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply, chart_coef, chart_lie X,
    Finset.sum_mul, smul_mul_assoc]
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (integral_finset_sum _ fun i _ =>
    (integrable_chart μ hω h' (hl (bas E a i)) x (oneL E a)).smul ((bas E a).coord i X)).symm
  simp only [Pi.smul_apply]
  rw [integral_smul, crd, ContinuousLinearMap.comp_apply, e1]
  rfl

def coefL (hω : ω.IsUnitary) (h' : ψ ∈ bddForms E a ω) (hV : ∀ φ ∈ V, φ.1 ∈ bddForms E a ω)
    (hl : ∀ X, ∀ φ ∈ V, lie E a X φ ∈ V) : V →ₗ[ℂ] Sm E a where
  toFun φ := ⟨coef μ ψ φ.1.1, coef_mem_Sm μ hω h' hV hl φ.2⟩
  map_add' φ φ' := Subtype.ext (funext fun x =>
    pet_add_left μ hω (mul_right_mem_bddForms (hV _ φ.2) x) (mul_right_mem_bddForms (hV _ φ'.2) x) h')
  map_smul' c φ := Subtype.ext (funext fun x => pet_smul_left μ c (fun g => φ.1.1 (g * x)) ψ)

theorem aeval_lapOp_comm (hl : ∀ X, ∀ φ ∈ V, lie E a X φ ∈ V) (T : V →ₗ[ℂ] Sm E a)
    (hT : ∀ X (φ : V), T ⟨_, hl X _ φ.2⟩ = lie E a X (T φ)) (p : Polynomial ℂ) (φ : V) :
    ∃ h : Polynomial.aeval (lapOp E a) p φ.1 ∈ V, T ⟨_, h⟩ = Polynomial.aeval (lapOp E a) p (T φ) := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {z | ∀ φ : V, ∃ h : z φ.1 ∈ V, T ⟨_, h⟩ = z (T φ)}
      mul_mem' := fun {x y} hx hy φ => by
        obtain ⟨h1, e1⟩ := hy φ
        obtain ⟨h2, e2⟩ := hx ⟨_, h1⟩
        exact ⟨h2, e2.trans (congrArg x e1)⟩
      add_mem' := fun {x y} hx hy φ => by
        obtain ⟨h1, e1⟩ := hx φ
        obtain ⟨h2, e2⟩ := hy φ
        exact ⟨add_mem h1 h2, (map_add T ⟨_, h1⟩ ⟨_, h2⟩).trans (congrArg₂ (· + ·) e1 e2)⟩
      algebraMap_mem' := fun c φ => ⟨V.smul_mem c φ.2, map_smul T c φ⟩ }
  have hL : ∀ X, lie E a X ∈ S := fun X φ => ⟨hl X _ φ.2, hT X φ⟩
  have hΔ : lapOp E a ∈ S :=
    S.sum_mem fun τ _ => S.sum_mem fun i _ => S.sum_mem fun j _ => S.add_mem (S.pow_mem (hL _) 2) (S.pow_mem (hL _) 2)
  exact (Algebra.adjoin_le (S := S) (Set.singleton_subset_iff.2 hΔ)) (Polynomial.aeval_mem_adjoin_singleton ℂ _) φ

theorem pet_translate_eq_zero (hω : ω.IsUnitary) (h' : ψ ∈ bddForms E a ω) (hV : ∀ φ ∈ V, φ.1 ∈ bddForms E a ω)
    (hl : ∀ X, ∀ φ ∈ V, lie E a X φ ∈ V) (hA : ∀ φ ∈ V, IsAutForm φ)
    (h0 : ∀ φ ∈ V, pet (latticeGL E a) μ φ.1 ψ = 0) {φ : Sm E a} (hφ : φ ∈ V) (y : GL (Fin a) (Cinf E)) :
    pet (latticeGL E a) μ (fun g => φ.1 (g * infGL E a y)) ψ = 0 := by
  let T := coefL μ hω h' hV hl
  have hT : ∀ X (φ : V), T ⟨_, hl X _ φ.2⟩ = lie E a X (T φ) := fun X φ =>
    Subtype.ext (lieD_coef μ hω h' (hV _ φ.2) (fun X => hV _ (hl X _ φ.2)) X).symm
  have key := eq_univ_of_exp (S := {y | ∀ φ : V, (T φ).1 (infGL E a y) = 0})
    (fun φ => by simpa [T, coefL, coef] using h0 _ φ.2) fun y hy X t φ => by
      obtain ⟨p, hp0, hp⟩ := exists_poly_lap (hA _ φ.2)
      obtain ⟨h1, e⟩ := aeval_lapOp_comm hl T hT p φ
      have e0 : (⟨_, h1⟩ : V) = 0 := Subtype.ext hp
      rw [e0, map_zero] at e
      rw [map_mul]
      refine eq_zero_along (analyticOnNhd_along hp0 e.symm _ X) (fun k => ?_) t
      suffices h : ∃ φ' : V, (lie E a X ^ k) (T φ) = T φ' by
        obtain ⟨φ', e'⟩ := h
        rw [e']; exact hy φ'
      induction k with
      | zero => exact ⟨φ, rfl⟩
      | succ k ih =>
        obtain ⟨φ', e'⟩ := ih
        exact ⟨_, by rw [pow_succ', Module.End.mul_apply, e', ← hT]⟩
  exact (key ▸ Set.mem_univ y : y ∈ {y | ∀ φ : V, (T φ).1 (infGL E a y) = 0}) ⟨φ, hφ⟩

theorem pet_eq_zero_of_orthogonal (hB : GlobalTheory.Published.CuspFormsBoundedGL) (E : Type) [Field E] [NumberField E]
    [IsTotallyComplex E] (a : ℕ) (π π' : CuspSub E a) (ω : HChar E) (hω : ω.IsUnitary) (h : π.HasCentChar ω)
    (h' : π'.HasCentChar ω) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (h0 : ∀ φ ∈ π.V, ∀ ψ ∈ π'.V, pet (latticeGL E a) μ φ.1 ψ.1 = 0) :
    (∀ φ ∈ π.V, ∀ ψ ∈ π'.V, ∀ y : GL (Fin a) (Cinf E),
      pet (latticeGL E a) μ (fun g => φ.1 (g * infGL E a y)) ψ.1 = 0) ∧
    ∀ F ∈ withSmoothings π, ∀ F' ∈ withSmoothings π', pet (latticeGL E a) μ F.1 F'.1 = 0 := by
  have b : ∀ φ ∈ π.V, φ.1 ∈ bddForms E a ω := fun φ => mem_bddForms_of_cuspSub hB hω h
  have b' : ∀ φ ∈ π'.V, φ.1 ∈ bddForms E a ω := fun φ => mem_bddForms_of_cuspSub hB hω h'
  have H : ∀ φ ∈ π.V, ∀ ψ ∈ π'.V, ∀ y : GL (Fin a) (Cinf E),
      pet (latticeGL E a) μ (fun g => φ.1 (g * infGL E a y)) ψ.1 = 0 := fun φ hφ ψ hψ y =>
    pet_translate_eq_zero μ hω (b' ψ hψ) b (fun X => π.stable (.lie X)) (fun φ hφ => (π.cusp φ hφ).1)
      (fun φ hφ => h0 φ hφ ψ hψ) hφ y
  refine ⟨H, ?_⟩

  have ext : ∀ (ρ : CuspSub E a), ρ.HasCentChar ω → ∀ ψ ∈ bddForms E a ω,
      (∀ φ ∈ ρ.V, ∀ y, pet (latticeGL E a) μ (fun g => φ.1 (g * infGL E a y)) ψ = 0) →
      ∀ F ∈ withSmoothings ρ, pet (latticeGL E a) μ F.1 ψ = 0 := by
    intro ρ hρ ψ hψ hy F hF
    let K : Submodule ℂ (Sm E a) :=
      { carrier := {F | F.1 ∈ bddForms E a ω ∧ pet (latticeGL E a) μ F.1 ψ = 0}
        add_mem' := fun {F G} hF hG => ⟨add_mem hF.1 hG.1, by
          rw [Submodule.coe_add, pet_add_left μ hω hF.1 hG.1 hψ, hF.2, hG.2, add_zero]⟩
        zero_mem' := ⟨zero_mem _, by simp [pet, descend]⟩
        smul_mem' := fun c F hF => ⟨Submodule.smul_mem _ c hF.1, by
          rw [Submodule.coe_smul, pet_smul_left, hF.2, mul_zero]⟩ }
    refine ((sup_le (fun φ hφ => ⟨mem_bddForms_of_cuspSub hB hω hρ hφ, by simpa using hy φ hφ 1⟩)
      (Submodule.span_le.2 ?_) : withSmoothings ρ ≤ K) hF).2
    rintro G ⟨f, φ, hf, hφ, e⟩
    have bφ := mem_bddForms_of_cuspSub hB hω hρ hφ
    change G.1 ∈ _ ∧ pet _ μ G.1 ψ = 0
    rw [e]
    refine ⟨by exact smoothing_mem_bddForms volume hf bφ, ?_⟩
    refine Eq.trans (by exact pet_smoothing_left μ (volume : Measure (Lie E a)) hω hf bφ hψ) ?_
    refine integral_eq_zero_of_ae (.of_forall fun x => mul_eq_zero_of_right _ ?_)
    unfold chart
    split_ifs
    · exact hy φ hφ _
    · simp [pet, descend]
  intro F hF F' hF'
  have bF := mem_bddForms_of_withSmoothings hB hω h hF
  rw [← conj_pet, ext π' h' F.1 bF (fun ψ hψ y => ?_) F' hF', map_zero]
  rw [← conj_pet, ext π h _ (mul_right_mem_bddForms (b' ψ hψ) _) (fun φ hφ x => ?_) F hF, map_zero]
  rw [← H φ hφ ψ hψ (y⁻¹ * x), ← pet_mul_right μ hω (mul_right_mem_bddForms (b φ hφ) _) (b' ψ hψ) (infGL E a y)]
  simp only [map_mul, map_inv, mul_assoc, mul_inv_cancel_left]

end GlobalTheory.KeepOrth

end
