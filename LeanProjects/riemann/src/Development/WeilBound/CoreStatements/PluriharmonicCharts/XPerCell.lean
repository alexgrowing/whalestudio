import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.LeviForms.HomDens
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace PositivityTheory.Xgp.per_cell

theorem inv_an {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (F : E → E) (a : E)
    (L : E →L[ℂ] E) (hF : AnalyticAt ℂ F a) (hL : HasFDerivAt F L a) (hi : Function.Injective L) :
    ∃ ψ : E → E, AnalyticAt ℂ ψ (F a) ∧ ψ (F a) = a ∧ (∀ᶠ y in 𝓝 (F a), F (ψ y) = y) ∧
      ∀ w, L (fderiv ℂ ψ (F a) w) = w := by
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  let L' : E ≃L[ℂ] E := (LinearEquiv.ofInjectiveEndo (L : E →ₗ[ℂ] E) hi).toContinuousLinearEquiv
  have hL' : HasFDerivAt F (L' : E →L[ℂ] E) a := by
    have : (L' : E →L[ℂ] E) = L := by ext w; rfl
    rwa [this]
  have hc : ContDiffAt ℂ ⊤ F a := hF.contDiffAt
  have hs := hc.hasStrictFDerivAt' hL' (by simp)
  refine ⟨hc.localInverse hL' (by simp), (hc.to_localInverse hL' (by simp)).analyticAt,
    hc.localInverse_apply_image hL' (by simp), hs.eventually_right_inverse, fun w => ?_⟩
  have h2 : HasFDerivAt (hc.localInverse hL' (by simp)) (L'.symm : E →L[ℂ] E) (F a) :=
    hs.to_localInverse.hasFDerivAt
  rw [h2.fderiv]
  exact L'.apply_symm_apply w

variable {N : ℕ}

noncomputable def ent (a b : Fin N) : (Pairs N → ℂ) →L[ℂ] ℂ :=
  if h : b < a then ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Pairs N => ℂ) ⟨(b, a), h⟩ else 0

theorem ent_apply (a b : Fin N) (z : Pairs N → ℂ) : ent a b z = zMat N z a b := by
  rw [zMat_apply, ent]
  split_ifs <;> rfl

theorem zMat_zero : zMat N 0 = 0 := by
  ext a b
  rw [← ent_apply]
  simp

theorem an_pow (k : ℕ) (a b : Fin N) (z : Pairs N → ℂ) : AnalyticAt ℂ (fun z => (zMat N z ^ k) a b) z := by
  induction k generalizing a b with
  | zero => simpa using analyticAt_const
  | succ k ih =>
    simp only [pow_succ, Matrix.mul_apply, ← ent_apply]
    exact Finset.analyticAt_fun_sum _ fun c _ => (ih a c).fun_mul ((ent c b).analyticAt z)

theorem der_pow (k : ℕ) (a b : Fin N) :
    HasFDerivAt (fun z => (zMat N z ^ k) a b) (if k = 1 then ent a b else 0) 0 := by
  cases k with
  | zero => simpa using hasFDerivAt_const _ _
  | succ k =>
    simp only [pow_succ, Matrix.mul_apply, ← ent_apply]
    have h := HasFDerivAt.fun_sum (u := Finset.univ) fun c _ =>
      ((an_pow k a c 0).differentiableAt.hasFDerivAt).mul ((ent c b).hasFDerivAt (x := 0))
    refine HasFDerivAt.congr_fderiv h (Eq.symm ?_)
    rw [zMat_zero]
    cases k with
    | zero => simp [Matrix.one_apply]
    | succ k => simp

theorem an_cell (a b : Fin N) (z : Pairs N → ℂ) : AnalyticAt ℂ (fun z => cellMat N z a b) z := by
  simp only [cellMat_eq, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.fun_mul (an_pow k a b z)

theorem der_cell (a b : Fin N) : HasFDerivAt (fun z => cellMat N z a b) (ent a b) 0 := by
  simp only [cellMat_eq, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have h := HasFDerivAt.fun_sum (u := Finset.range N) fun k _ =>
    (der_pow k a b).const_mul ((k.factorial : ℂ)⁻¹)
  refine HasFDerivAt.congr_fderiv h (Eq.symm ?_)
  by_cases hN : 1 < N
  · rw [Finset.sum_eq_single 1 (fun k _ hk => by simp [hk]) (fun h => absurd (Finset.mem_range.2 hN) h)]
    simp
  · have h0 : ent a b = 0 := by
      have : ¬ b < a := by
        have := a.2
        have := b.2
        rw [Fin.lt_def]
        omega
      simp [ent, this]
    simp [h0]

noncomputable def low : (Fin N → Fin N → ℂ) →L[ℂ] (Pairs N → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M p => M p.1.2 p.1.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

noncomputable def up : (Fin N → Fin N → ℂ) →L[ℂ] (Fin N → Fin N → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M a b => if b < a then 0 else M a b
      map_add' := fun _ _ => by ext a b; simp only [Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun _ _ => by ext a b; simp only [Pi.smul_apply]; split_ifs <;> simp }

theorem up_apply (M : Fin N → Fin N → ℂ) (a b : Fin N) : up M a b = if b < a then 0 else M a b := rfl

theorem up_tri (M : Fin N → Fin N → ℂ) : (Matrix.of (up M)).BlockTriangular id := fun a b h => by
  rw [Matrix.of_apply, up_apply, if_pos (show b < a from h)]

theorem key (b₀ U : Matrix (Fin N) (Fin N) ℂ) (hb : b₀.BlockTriangular id) (hd : IsUnit b₀.det)
    (hU : U.BlockTriangular id) (z : Pairs N → ℂ) :
    z = 0 ↔ (b₀⁻¹ * (zMat N z * b₀ + U)).BlockTriangular id := by
  let _ := Matrix.invertibleOfIsUnitDet b₀ hd
  have hi : b₀⁻¹.BlockTriangular id := blockTriangular_inv_of_blockTriangular hb
  constructor
  · rintro rfl
    rw [zMat_zero, Matrix.zero_mul, zero_add]
    exact hi.mul hU
  · intro h
    have h1 : ((b₀ * (b₀⁻¹ * (zMat N z * b₀ + U)) - U) * b₀⁻¹).BlockTriangular id := ((hb.mul h).sub hU).mul hi
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hd, add_sub_cancel_right,
      Matrix.mul_nonsing_inv_cancel_right _ _ hd] at h1
    funext p
    have := h1 (show id p.1.1 < id p.1.2 from p.2)
    rw [zMat_apply, dif_pos p.2] at this
    exact this

noncomputable def FF (M : Fin N → Fin N → ℂ) : Fin N → Fin N → ℂ :=
  fun a b => (cellMat N (low M) * Matrix.of (up M)) a b

noncomputable def LL (b₀ : Matrix (Fin N) (Fin N) ℂ) : (Fin N → Fin N → ℂ) →L[ℂ] (Fin N → Fin N → ℂ) :=
  ContinuousLinearMap.pi fun a => ContinuousLinearMap.pi fun b =>
    (∑ c, b₀ c b • (ent a c).comp low) +
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) b).comp
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => Fin N → ℂ) a).comp up))

theorem LL_apply (b₀ : Matrix (Fin N) (Fin N) ℂ) (M : Fin N → Fin N → ℂ) :
    Matrix.of (LL b₀ M) = zMat N (low M) * b₀ + Matrix.of (up M) := by
  ext a b
  simp [LL, Matrix.mul_apply, ent_apply, mul_comm]

theorem an_FF (M : Fin N → Fin N → ℂ) : AnalyticAt ℂ (FF (N := N)) M := by
  refine analyticAt_pi_iff.2 fun a => analyticAt_pi_iff.2 fun b => ?_
  simp only [FF, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.analyticAt_fun_sum _ fun c _ => AnalyticAt.fun_mul ?_ ?_
  · exact (an_cell a c _).comp (low.analyticAt M)
  · exact analyticAt_pi_iff.1 (analyticAt_pi_iff.1 (up.analyticAt M) c) b

theorem low_tri {b₀ : Matrix (Fin N) (Fin N) ℂ} (hb : b₀.BlockTriangular id) : low (fun a b => b₀ a b) = 0 := by
  funext p
  exact hb (show id p.1.1 < id p.1.2 from p.2)

theorem up_of_tri {b₀ : Matrix (Fin N) (Fin N) ℂ} (hb : b₀.BlockTriangular id) :
    up (fun a b => b₀ a b) = fun a b => b₀ a b := by
  funext a b
  rw [up_apply]
  split_ifs with h
  · exact (hb (show id b < id a from h)).symm
  · rfl

theorem der_FF {b₀ : Matrix (Fin N) (Fin N) ℂ} (hb : b₀.BlockTriangular id) :
    HasFDerivAt FF (LL b₀) (fun a b => b₀ a b) := by
  refine hasFDerivAt_pi.2 fun a => hasFDerivAt_pi.2 fun b => ?_
  simp only [FF, Matrix.mul_apply, Matrix.of_apply]
  have h1 : ∀ c, HasFDerivAt (fun M : Fin N → Fin N → ℂ => cellMat N (low M) a c) ((ent a c).comp low)
      (fun a b => b₀ a b) := fun c => by
    have h := der_cell a c
    rw [← low_tri hb] at h
    exact h.comp _ low.hasFDerivAt
  have h2 : ∀ c, HasFDerivAt (fun M : Fin N → Fin N → ℂ => up M c b)
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) b).comp
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => Fin N → ℂ) c).comp up)) (fun a b => b₀ a b) :=
    fun c => ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) b).comp
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => Fin N → ℂ) c).comp up)).hasFDerivAt
  have h := HasFDerivAt.fun_sum (u := Finset.univ) fun c _ => (h1 c).mul (h2 c)
  refine HasFDerivAt.congr_fderiv h (Eq.symm ?_)
  rw [low_tri hb, up_of_tri hb, cellMat_zero N, Finset.sum_add_distrib, add_comm]
  congr 1
  simp [Matrix.one_apply]

theorem inj_LL {b₀ : Matrix (Fin N) (Fin N) ℂ} (hb : b₀.BlockTriangular id) (hd : IsUnit b₀.det) :
    Function.Injective (LL b₀) := by
  refine (injective_iff_map_eq_zero (LL b₀)).2 fun M hM => ?_
  have h := LL_apply b₀ M
  rw [hM] at h
  have h0 : low M = 0 := (key b₀ _ hb hd (up_tri M) _).2 (by
    rw [← h]
    intro a b _
    simp [Matrix.mul_apply])
  rw [h0, zMat_zero, Matrix.zero_mul, zero_add] at h
  funext a b
  by_cases hab : b < a
  · exact congrFun h0 ⟨(b, a), hab⟩
  · have := congrFun (congrFun h a) b
    rw [Matrix.of_apply, Matrix.of_apply, up_apply, if_neg hab] at this
    exact this.symm

end PositivityTheory.Xgp.per_cell

open PositivityTheory.Xgp.per_cell in

theorem PositivityTheory.Xgp.t_per_cell : ∀ (e N : ℕ) (g : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) (x₀ : Fin e → ℂ), (∀ a b, AnalyticAt ℂ (fun x => g x a b) x₀) → (g x₀).BlockTriangular id → IsUnit (g x₀).det → ∃ (z : (Fin e → ℂ) → Pairs N → ℂ) (b : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ), AnalyticAt ℂ z x₀ ∧ (∀ p q, AnalyticAt ℂ (fun x => b x p q) x₀) ∧ z x₀ = 0 ∧ (∀ᶠ x in 𝓝 x₀, (b x).BlockTriangular id ∧ IsUnit (b x).det ∧ g x = cellMat N (z x) * b x) ∧ ∀ v, fderiv ℂ z x₀ v = 0 ↔ ((g x₀)⁻¹ * Matrix.of fun p q => fderiv ℂ (fun x => g x p q) x₀ v).BlockTriangular id := by
  intro e N g x₀ hg hb hd
  obtain ⟨ψ, hψ, hψ0, hev, hder⟩ := inv_an FF _ _ (an_FF _) (der_FF hb) (inj_LL hb hd)
  have hF0 : FF (fun a b => g x₀ a b) = fun a b => g x₀ a b := by
    funext a b
    rw [FF, low_tri hb, up_of_tri hb, cellMat_zero N, Matrix.one_mul]
    rfl
  rw [hF0] at hψ hψ0 hev hder
  let G : (Fin e → ℂ) → Fin N → Fin N → ℂ := fun x a b => g x a b
  have hG : AnalyticAt ℂ G x₀ := analyticAt_pi_iff.2 fun a => analyticAt_pi_iff.2 fun b => hg a b
  have hM : AnalyticAt ℂ (ψ ∘ G) x₀ := AnalyticAt.comp (f := G) hψ hG
  have hB : ∀ p q, AnalyticAt ℂ (fun x => up (ψ (G x)) p q) x₀ := fun p q =>
    analyticAt_pi_iff.1 (analyticAt_pi_iff.1 ((up.analyticAt _).comp hM) p) q
  refine ⟨fun x => low (ψ (G x)), fun x => Matrix.of (up (ψ (G x))), (low.analyticAt _).comp hM, hB, ?_, ?_,
    fun v => ?_⟩
  · show low (ψ fun a b => g x₀ a b) = 0
    rw [hψ0, low_tri hb]
  · have hc : ContinuousAt (fun x => (Matrix.of (up (ψ (G x)))).det) x₀ :=
      (continuous_id.matrix_det).continuousAt.comp
        (continuousAt_pi.2 fun p => continuousAt_pi.2 fun q => (hB p q).continuousAt)
    have h0 : (Matrix.of (up (ψ (G x₀)))).det ≠ 0 := by
      show (Matrix.of (up (ψ fun a b => g x₀ a b))).det ≠ 0
      rw [hψ0, up_of_tri hb]
      exact hd.ne_zero
    filter_upwards [hc.eventually_ne h0, hG.continuousAt.eventually hev] with x h1 h2
    refine ⟨up_tri _, h1.isUnit, ?_⟩
    ext a b
    exact (congrFun (congrFun h2 a) b).symm
  · have h1 : HasFDerivAt (fun x => low (ψ (G x))) (low.comp ((fderiv ℂ ψ (G x₀)).comp (fderiv ℂ G x₀))) x₀ :=
      low.hasFDerivAt.comp _ (HasFDerivAt.comp (f := G) _ hψ.differentiableAt.hasFDerivAt
        hG.differentiableAt.hasFDerivAt)
    have h2 : (Matrix.of fun p q => fderiv ℂ (fun x => g x p q) x₀ v) = Matrix.of (fderiv ℂ G x₀ v) := by
      ext p q
      have h3 := hasFDerivAt_pi'.1 (hasFDerivAt_pi'.1 hG.differentiableAt.hasFDerivAt p) q
      rw [Matrix.of_apply, Matrix.of_apply, h3.fderiv]
      rfl
    rw [h1.fderiv, h2, ← hder (fderiv ℂ G x₀ v), LL_apply]
    exact key _ _ hb hd (up_tri _) _
