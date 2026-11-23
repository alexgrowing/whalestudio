import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsSmoothPts
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace ProjLine

section Homog

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem isMultiHomog_zero (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

theorem isMultiHomog_one : IsMultiHomog (1 : MRing ι) 0 := by
  intro m hm k
  rw [support_one] at hm
  · rw [Finset.mem_singleton] at hm
    subst hm
    simp

theorem mhNeg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm
  rw [support_neg] at hm
  exact hf m hm

theorem mhAdd {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  intro m hm
  classical
  rcases Finset.mem_union.mp (support_add hm) with h | h
  · exact hf m h
  · exact hg m h

theorem mhMul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  intro m hm k
  classical
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
  simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, hf m₁ hm₁ k, hg m₂ hm₂ k]

theorem isMultiHomog_X (p : Σ k, ι k) [DecidableEq K] :
    IsMultiHomog (X p : MRing ι) (fun k => if k = p.1 then 1 else 0) := by
  intro m hm k
  classical
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨k₀, i₀⟩ := p
  by_cases hk : k = k₀
  · subst hk
    simp [Finsupp.single_apply]
  · simp only [hk, if_false]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hk (congrArg Sigma.fst h).symm

end Homog

abbrev Kfr : Type := FractionRing (MRing (GlobalTheory (Fin 2)))

abbrev Xk (i : Fin 2) : Kfr := algebraMap (MRing (GlobalTheory (Fin 2))) Kfr (X ⟨(), i⟩)

theorem Xk_ne_zero (i : Fin 2) : Xk i ≠ 0 := by
  rw [Ne, ← map_zero (algebraMap (MRing (GlobalTheory (Fin 2))) Kfr),
    (IsFractionRing.injective (MRing (GlobalTheory (Fin 2))) Kfr).eq_iff]
  exact X_ne_zero _

def u : Kfr := Xk 1 / Xk 0

abbrev FnField : Type := Subfield.closure ({u} : Set Kfr)

def uF : FnField := ⟨u, Subfield.subset_closure rfl⟩

def y : Ix (Fin 2) → FnField := fun p => ![1, uF] p.2

@[simp] theorem y_zero : y ⟨(), 0⟩ = 1 := rfl
@[simp] theorem y_one : y ⟨(), 1⟩ = uF := rfl

abbrev incl : FnField →+* Kfr := (Subfield.closure ({u} : Set Kfr)).subtype

theorem incl_y_mul (p : Ix (Fin 2)) : incl (y p) * Xk 0 = algebraMap _ Kfr (X p : MRing (GlobalTheory (Fin 2))) := by
  obtain ⟨⟨⟩, i⟩ := p
  fin_cases i
  · simp [y]
  · simp only [y, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    change u * Xk 0 = Xk 1
    rw [u, div_mul_cancel₀ _ (Xk_ne_zero 0)]

theorem eval_coneMap (f : MRing (GlobalTheory (Fin 2))) :
    Polynomial.eval₂ incl (Xk 0) (coneMap ℤ y f) = algebraMap _ Kfr f := by
  have h : (Polynomial.eval₂RingHom incl (Xk 0)).comp (coneMap ℤ y).toRingHom =
      algebraMap (MRing (GlobalTheory (Fin 2))) Kfr := by
    refine MvPolynomial.ringHom_ext (fun n => by simp) (fun p => ?_)
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      coneMap, aeval_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X]
    exact incl_y_mul p
  exact congrArg (fun φ : MRing (GlobalTheory (Fin 2)) →+* Kfr => φ f) h

theorem coordIdeal_y : coordIdeal ℤ y = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Ideal.mem_bot]
  have h0 : coneMap ℤ y f = 0 := hf
  have h1 := eval_coneMap f
  rw [h0, Polynomial.eval₂_zero] at h1
  exact (IsFractionRing.injective (MRing (GlobalTheory (Fin 2))) Kfr) (by rw [← h1, map_zero])

theorem eval_mConeMap (f : MRing (GlobalTheory (Fin 2))) :
    MvPolynomial.eval₂ incl (fun _ => Xk 0) (mConeMap y f) = algebraMap _ Kfr f := by
  have h : (MvPolynomial.eval₂Hom incl (fun _ : Unit => Xk 0)).comp (mConeMap y).toRingHom =
      algebraMap (MRing (GlobalTheory (Fin 2))) Kfr := by
    refine MvPolynomial.ringHom_ext (fun n => by simp) (fun p => ?_)
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      mConeMap, aeval_X, coe_eval₂Hom, eval₂_mul, eval₂_C, eval₂_X]
    exact incl_y_mul p
  exact congrArg (fun φ : MRing (GlobalTheory (Fin 2)) →+* Kfr => φ f) h

theorem mCoordIdeal_y : mCoordIdeal (ι := GlobalTheory (Fin 2)) y = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Ideal.mem_bot]
  have h0 : mConeMap y f = 0 := hf
  have h1 := eval_mConeMap f
  rw [h0, eval₂_zero] at h1
  exact (IsFractionRing.injective (MRing (GlobalTheory (Fin 2))) Kfr) (by rw [← h1, map_zero])

theorem isArithVar_y : IsArithVar (ι := GlobalTheory (Fin 2)) (coordIdeal ℤ y) 2 := by
  rw [coordIdeal_y]
  exact GroundTheory.Heights₂.Heights.Inter.isArithVar_projLine

theorem isArithVar_y' : IsArithVar (ι := GlobalTheory (Fin 2)) (mCoordIdeal y) 2 := by
  rw [mCoordIdeal_y]
  exact GroundTheory.Heights₂.Heights.Inter.isArithVar_projLine

theorem linearIndependent_y : LinearIndependent ℤ y := by
  rw [Fintype.linearIndependent_iff]
  intro g hg p
  have hs : (g ⟨(), 0⟩ : FnField) + (g ⟨(), 1⟩ : FnField) * uF = 0 := by
    rw [Fintype.sum_sigma] at hg
    simpa [Fin.sum_univ_two, zsmul_eq_mul] using hg
  have hK : algebraMap (MRing (GlobalTheory (Fin 2))) Kfr (C (g ⟨(), 0⟩) * X ⟨(), 0⟩ + C (g ⟨(), 1⟩) * X ⟨(), 1⟩) = 0 := by
    have := congrArg (fun t => incl t * Xk 0) hs
    simp only [map_add, map_mul, map_intCast, map_zero, zero_mul] at this
    rw [map_add, map_mul, map_mul, ← this]
    have hu : incl uF * Xk 0 = Xk 1 := incl_y_mul ⟨(), 1⟩
    simp only [map_intCast, eq_intCast]
    rw [add_mul, mul_assoc, hu]
  have hP : C (g ⟨(), 0⟩) * X ⟨(), 0⟩ + C (g ⟨(), 1⟩) * (X ⟨(), 1⟩ : MRing (GlobalTheory (Fin 2))) = 0 :=
    (IsFractionRing.injective (MRing (GlobalTheory (Fin 2))) Kfr) (by rw [hK, map_zero])
  obtain ⟨⟨⟩, i⟩ := p
  fin_cases i
  · have := congrArg (eval (fun q : Ix (Fin 2) => ![(1 : ℤ), 0] q.2)) hP
    simpa using this
  · have := congrArg (eval (fun q : Ix (Fin 2) => ![(0 : ℤ), 1] q.2)) hP
    simpa using this

theorem birational_y : Birational (ι := GlobalTheory (Fin 2)) y := by
  intro s
  obtain ⟨s, hs⟩ := s
  induction hs using Subfield.closure_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨fun _ => 1, X ⟨(), 1⟩, X ⟨(), 0⟩, ?_, ?_, ?_, ?_⟩
    · convert isMultiHomog_X (ι := GlobalTheory (Fin 2)) ⟨(), 1⟩ using 1
      funext k
      simp
    · convert isMultiHomog_X (ι := GlobalTheory (Fin 2)) ⟨(), 0⟩ using 1
      funext k
      simp
    · simp
    · simp only [aeval_X, y_zero, y_one, mul_one]
      rfl
  | one =>
    refine ⟨0, 1, 1, isMultiHomog_one, isMultiHomog_one, by simp, ?_⟩
    simp only [map_one, mul_one]
    rfl
  | add a b ha hb iha ihb =>
    obtain ⟨d₁, g₁, h₁, hg₁, hh₁, hne₁, he₁⟩ := iha
    obtain ⟨d₂, g₂, h₂, hg₂, hh₂, hne₂, he₂⟩ := ihb
    have hsum : IsMultiHomog (g₁ * h₂ + g₂ * h₁) (d₁ + d₂) := by
      refine mhAdd (mhMul hg₁ hh₂) ?_
      rw [add_comm d₁]
      exact mhMul hg₂ hh₁
    refine ⟨d₁ + d₂, g₁ * h₂ + g₂ * h₁, h₁ * h₂, hsum, mhMul hh₁ hh₂, ?_, ?_⟩
    · rw [map_mul]
      exact mul_ne_zero hne₁ hne₂
    · rw [map_add, map_mul, map_mul, map_mul, he₁, he₂]
      have : (⟨a + b, add_mem ha hb⟩ : FnField) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
      rw [this]
      ring
  | neg a ha iha =>
    obtain ⟨d, g, h, hg, hh, hne, he⟩ := iha
    refine ⟨d, -g, h, mhNeg hg, hh, hne, ?_⟩
    rw [map_neg, he]
    have : (⟨-a, neg_mem ha⟩ : FnField) = -⟨a, ha⟩ := rfl
    rw [this]
    ring
  | inv a ha iha =>
    obtain ⟨d, g, h, hg, hh, hne, he⟩ := iha
    by_cases ha0 : (⟨a, ha⟩ : FnField) = 0
    · refine ⟨0, 0, 1, isMultiHomog_zero _, isMultiHomog_one, by simp, ?_⟩
      have : (⟨a⁻¹, inv_mem ha⟩ : FnField) = (⟨a, ha⟩ : FnField)⁻¹ := rfl
      rw [this, ha0]
      simp
    · have hg0 : aeval y g ≠ 0 := by
        rw [he]
        exact mul_ne_zero ha0 hne
      refine ⟨d, h, g, hh, hg, hg0, ?_⟩
      have : (⟨a⁻¹, inv_mem ha⟩ : FnField) = (⟨a, ha⟩ : FnField)⁻¹ := rfl
      rw [this, he]
      field_simp
  | mul a b ha hb iha ihb =>
    obtain ⟨d₁, g₁, h₁, hg₁, hh₁, hne₁, he₁⟩ := iha
    obtain ⟨d₂, g₂, h₂, hg₂, hh₂, hne₂, he₂⟩ := ihb
    refine ⟨d₁ + d₂, g₁ * g₂, h₁ * h₂, mhMul hg₁ hg₂, mhMul hh₁ hh₂, ?_, ?_⟩
    · rw [map_mul]
      exact mul_ne_zero hne₁ hne₂
    · rw [map_mul, map_mul, he₁, he₂]
      have : (⟨a * b, mul_mem ha hb⟩ : FnField) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
      rw [this]
      ring

section FS

open scoped Topology

variable {J : Type} [Fintype J]

abbrev eL : (J → ℂ) →L[ℝ] EuclideanSpace ℂ J :=
  ((EuclideanSpace.equiv J ℂ).symm.toContinuousLinearMap).restrictScalars ℝ

theorem eL_apply (z : J → ℂ) : eL z = WithLp.toLp 2 z := rfl

def reInner : (J → ℂ) →L[ℝ] ((J → ℂ) →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ (J → ℂ) (EuclideanSpace ℂ J) ℝ).flip eL).comp
    ((innerSL ℝ (E := EuclideanSpace ℂ J)).comp eL)

theorem reInner_apply (y v : J → ℂ) : reInner y v = inner ℝ (eL y) (eL v) := rfl

theorem realInner_eq (x y : EuclideanSpace ℂ J) : inner ℝ x y = RCLike.re (inner ℂ x y) := by
  rw [PiLp.inner_apply, PiLp.inner_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => real_inner_eq_re_inner ℂ _ _

def normSqE (z : J → ℂ) : ℝ := ‖eL z‖ ^ 2

theorem hasFDerivAt_normSqE (z : J → ℂ) : HasFDerivAt normSqE (2 • reInner z) z :=
  eL.hasFDerivAt.norm_sq

theorem normSqE_pos {z : J → ℂ} (hz : z ≠ 0) : 0 < normSqE z := by
  unfold normSqE
  have : eL z ≠ 0 := fun h => hz (by
    have := congrArg (fun v : EuclideanSpace ℂ J => v.ofLp) h
    simpa [eL_apply] using this)
  positivity

theorem log_fs_eq : (fun z => Real.log ((fsMetric J).ρ z)) = fun z => (1 / 2) * Real.log (normSqE z) := by
  funext z
  change Real.log ‖WithLp.toLp 2 z‖ = _
  rw [normSqE, eL_apply, Real.log_pow]
  push_cast
  ring

theorem hasFDerivAt_log_fs {y : J → ℂ} (hy : y ≠ 0) :
    HasFDerivAt (fun z => Real.log ((fsMetric J).ρ z)) ((normSqE y)⁻¹ • reInner y) y := by
  rw [log_fs_eq]
  have h := ((hasFDerivAt_normSqE y).log (normSqE_pos hy).ne').const_mul (1 / 2 : ℝ)
  refine h.congr_fderiv ?_
  ext v
  simp
  ring

theorem leviForm_log_fs_nonneg {z : J → ℂ} (hz : z ≠ 0) (w : J → ℂ) :
    0 ≤ leviForm (fun z => Real.log ((fsMetric J).ρ z)) z w := by
  set G : (J → ℂ) → ((J → ℂ) →L[ℝ] ℝ) := fun y => (normSqE y)⁻¹ • reInner y with hG
  have hev : fderiv ℝ (fun z => Real.log ((fsMetric J).ρ z)) =ᶠ[𝓝 z] G := by
    filter_upwards [isOpen_ne.mem_nhds hz] with y hy
    exact (hasFDerivAt_log_fs hy).fderiv
  have hq := normSqE_pos hz
  have hc : HasFDerivAt (fun y => (normSqE y)⁻¹) ((-(normSqE z ^ 2)⁻¹) • (2 • reInner z)) z :=
    (hasDerivAt_inv hq.ne').comp_hasFDerivAt z (hasFDerivAt_normSqE z)
  have hGd : HasFDerivAt G ((normSqE z)⁻¹ • reInner + ((-(normSqE z ^ 2)⁻¹) • (2 • reInner z)).smulRight (reInner z)) z :=
    hc.smul reInner.hasFDerivAt
  have hD : ∀ v, fderiv ℝ (fderiv ℝ (fun z => Real.log ((fsMetric J).ρ z))) z v v =
      (normSqE z)⁻¹ * inner ℝ (eL v) (eL v) - 2 * (normSqE z ^ 2)⁻¹ * inner ℝ (eL z) (eL v) ^ 2 := by
    intro v
    rw [hev.fderiv_eq, hGd.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul, nsmul_eq_mul, reInner_apply]
    push_cast
    ring
  unfold leviForm
  rw [hD, hD]
  have hI : eL (Complex.I • w) = Complex.I • eL w := by
    rw [eL_apply, eL_apply, WithLp.toLp_smul]
  rw [hI]
  set q := normSqE z
  have hq' : q = ‖eL z‖ ^ 2 := rfl
  set c : ℂ := inner ℂ (eL z) (eL w) with hcdef
  have h1 : inner ℝ (eL w) (eL w) = ‖eL w‖ ^ 2 := real_inner_self_eq_norm_sq _
  have h2 : inner ℝ (Complex.I • eL w) (Complex.I • eL w) = ‖eL w‖ ^ 2 := by
    rw [real_inner_self_eq_norm_sq, norm_smul, Complex.norm_I, one_mul]
  have h3 : inner ℝ (eL z) (eL w) = RCLike.re c := realInner_eq _ _
  have h4 : inner ℝ (eL z) (Complex.I • eL w) = RCLike.re (Complex.I * c) := by
    rw [realInner_eq, inner_smul_right]
  simp only [h1, h2, h3, h4]
  have hcs : ‖c‖ ^ 2 ≤ q * ‖eL w‖ ^ 2 := by
    rw [hq', ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
  have hre : RCLike.re c ^ 2 + RCLike.re (Complex.I * c) ^ 2 = ‖c‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [RCLike.re_to_complex, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_sub]
    ring
  have key : 0 ≤ q⁻¹ * ‖eL w‖ ^ 2 - 2 * (q ^ 2)⁻¹ * RCLike.re c ^ 2 +
      (q⁻¹ * ‖eL w‖ ^ 2 - 2 * (q ^ 2)⁻¹ * RCLike.re (Complex.I * c) ^ 2) := by
    have h2 : q⁻¹ * ‖eL w‖ ^ 2 - 2 * (q ^ 2)⁻¹ * RCLike.re c ^ 2 +
        (q⁻¹ * ‖eL w‖ ^ 2 - 2 * (q ^ 2)⁻¹ * RCLike.re (Complex.I * c) ^ 2) =
        2 * (q ^ 2)⁻¹ * (q * ‖eL w‖ ^ 2 - ‖c‖ ^ 2) := by
      rw [← hre]
      field_simp
      ring
    rw [h2]
    have : 0 ≤ q * ‖eL w‖ ^ 2 - ‖c‖ ^ 2 := by linarith
    positivity
  linarith

theorem isSmoothMetric_fs : IsSmoothMetric (fsMetric J) := by
  unfold IsSmoothMetric
  intro z hz
  have h : (fsMetric J).ρ = fun z => ‖eL z‖ := rfl
  rw [h]
  have hne : eL z ≠ 0 := fun h0 => hz (by
    have := congrArg (fun v : EuclideanSpace ℂ J => v.ofLp) h0
    simpa [eL_apply] using this)
  exact ((contDiffAt_norm ℝ hne).comp z (ContinuousLinearMap.contDiff (eL (J := J))).contDiffAt).contDiffWithinAt

theorem isConjInvariant_fs : IsConjInvariant (fsMetric J) := by
  intro z
  change ‖WithLp.toLp 2 _‖ = ‖WithLp.toLp 2 z‖
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp

theorem isSmoothHerm_fs (κ : Type) [Fintype κ] : IsSmoothHerm (HermLine.ofCone (fsMetric (Ix κ))) := by
  refine (isSmoothMetric_fs (J := Ix κ)).mono fun z hz h0 => ?_
  obtain ⟨i, hi⟩ := hz ()
  exact hi (congrFun h0 _)

theorem isSemipositiveRel_fs {κ : Type} [Fintype κ] (P0 P : Ideal (MRing (GlobalTheory κ))) :
    IsSemipositiveRel P0 P (HermLine.ofCone (fsMetric (Ix κ))) := by
  refine ⟨isSmoothHerm_fs κ, fun z hz w _ => ?_⟩
  have hz0 : z ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ := hz.1 ()
    exact hi (congrFun h0 _)
  exact leviForm_log_fs_nonneg hz0 w

theorem isConjInvariantH_fs (κ : Type) [Fintype κ] : IsConjInvariantH (HermLine.ofCone (fsMetric (Ix κ))) :=
  fun z => isConjInvariant_fs z

end FS

end ProjLine

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
