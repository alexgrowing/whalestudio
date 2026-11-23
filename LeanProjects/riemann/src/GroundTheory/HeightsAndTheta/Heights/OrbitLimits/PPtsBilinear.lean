import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CasChainA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsBilinear
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsIntegrable
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff

namespace PointsBilinear

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem contDiffAt_comp {D : ℕ} {u : ((Σ k, ι k) → ℂ) → ℝ} (hu : IsDegZeroSmooth u)
    {γ : (Fin D → ℂ) → (Σ k, ι k) → ℂ} {y : Fin D → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y') (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0) :
    ContDiffAt ℝ 2 (fun y' => u (γ y')) y := by
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.mp hγ
  have hdU : DifferentiableOn ℂ γ U := fun y' h => (hU y' h).differentiableWithinAt
  have hc : ContDiffAt ℝ ∞ γ y :=
    ((ReciprocityTheory.ChartRestriction.DS.S7.cca_contDiffOn hUo hdU).contDiffAt (hUo.mem_nhds hyU)).restrict_scalars ℝ
  have hρ : ContDiffAt ℝ ∞ u (γ y) := hu.1.contDiffAt (isOpen_blockNonzero.mem_nhds hy)
  exact_mod_cast (contDiffAt_infty.mp (hρ.comp y hc)) 2

theorem cxHessian_sum {D : ℕ} {T : Type} [Fintype T] (f : T → (Fin D → ℂ) → ℝ) {y : Fin D → ℂ}
    (hf : ∀ t, ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (f t) y') :
    cxHessian (fun y' => ∑ t, f t y') y = ∑ t, cxHessian (f t) y := by
  have h1 : fderiv ℝ (fun y' => ∑ t, f t y') =ᶠ[𝓝 y] fun y' => ∑ t, fderiv ℝ (f t) y' := by
    filter_upwards [eventually_all.mpr hf] with y' hy'
    exact fderiv_fun_sum fun t _ => (hy' t).differentiableAt (by norm_num)
  have h2 : fderiv ℝ (fderiv ℝ (fun y' => ∑ t, f t y')) y = ∑ t, fderiv ℝ (fderiv ℝ (f t)) y := by
    rw [h1.fderiv_eq]
    exact fderiv_fun_sum fun t _ =>
      ((hf t).self_of_nhds.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  ext i j
  simp only [cxHessian, h2, FunLike.coe_sum, Finset.sum_apply, Matrix.sum_apply]
  push_cast
  rw [← Finset.sum_div]
  congr 1
  simp only [Finset.sum_add_distrib]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]

theorem mixedDisc_update_sum {D : ℕ} {T : Type} [Fintype T] (A : Fin D → Matrix (Fin D) (Fin D) ℂ)
    (k : Fin D) (B : T → Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (Function.update A k (∑ t, B t)) = ∑ t, mixedDisc (Function.update A k (B t)) := by
  obtain ⟨M, hM⟩ := ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := D)
  have e : ∀ C, mixedDisc (Function.update A k C) = M.toLinearMap A k C := fun C => by
    rw [MultilinearMap.toLinearMap_apply, hM]
    rfl
  simp only [e, map_sum]

theorem cxHessian_cons {n : ℕ} (L : Fin n → HermLine ι) (f v : ((Σ k, ι k) → ℂ) → ℝ)
    (γ : (Fin (n + 1) → ℂ) → (Σ k, ι k) → ℂ) (y : Fin (n + 1) → ℂ) :
    (fun k => cxHessian
        (fun y' => (Fin.cons f (pot L) : Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) k (γ y')) y) =
      Function.update (fun k => cxHessian
        (fun y' => (Fin.cons v (pot L) : Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) k (γ y')) y) 0
        (cxHessian (fun y' => f (γ y')) y) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · rw [Function.update_self]
    simp only [Fin.cons_zero]
  · rw [Function.update_of_ne (Fin.succ_ne_zero j)]
    simp only [Fin.cons_succ]

theorem maDensity_cons_sum {n : ℕ} (L : Fin n → HermLine ι) {T : Type} [Fintype T]
    {u : T → ((Σ k, ι k) → ℂ) → ℝ} (hu : ∀ t, IsDegZeroSmooth (u t))
    {γ : (Fin (n + 1) → ℂ) → (Σ k, ι k) → ℂ} {y : Fin (n + 1) → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ ∀ k, ∃ i, γ y' ⟨k, i⟩ ≠ 0) :
    maDensity (fun j y' => (Fin.cons (fun z => ∑ t, u t z) (pot L) :
        Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) j (γ y')) y =
      ∑ t, maDensity (fun j y' => (Fin.cons (u t) (pot L) :
        Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) j (γ y')) y := by
  have hev := hγ.eventually_nhds
  have hc : ∀ t, ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => u t (γ y'')) y' := fun t => by
    filter_upwards [hev] with y' hy'
    exact contDiffAt_comp (hu t) (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hH := cxHessian_sum (fun t y' => u t (γ y')) hc
  simp only [maDensity]
  rw [cxHessian_cons L _ (fun _ => 0) γ y]
  simp only [hH, mixedDisc_update_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [cxHessian_cons L (u t) (fun _ => 0) γ y]

omit [∀ k, Fintype (ι k)] in

theorem sheetDensity_sum_left {n : ℕ} (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (φ : Fin n → ((Σ k, ι k) → ℂ) → ℝ)
    {T : Type} [Fintype T] (u : T → ((Σ k, ι k) → ℂ) → ℝ) (y : Fin n → ℂ)
    (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ (fun z => ∑ t, u t z) y w = ∑ t, sheetDensity P Ψ φ (u t) y w := by
  unfold sheetDensity
  by_cases h : ∃ γ, IsSheet P Ψ y w γ
  · simp only [dif_pos h, Finset.sum_mul]
  · simp only [dif_neg h, Finset.sum_const_zero]

theorem sheetDensity_sum_right {n : ℕ} (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1 + 1) → ℂ)) (L : Fin n → HermLine ι)
    {T : Type} [Fintype T] {u : T → ((Σ k, ι k) → ℂ) → ℝ} (hu : ∀ t, IsDegZeroSmooth (u t))
    (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ (Fin.cons (fun z => ∑ t, u t z) (pot L)) g y w =
      ∑ t, sheetDensity P Ψ (Fin.cons (u t) (pot L)) g y w := by
  unfold sheetDensity
  by_cases h : ∃ γ, IsSheet P Ψ y w γ
  · simp only [dif_pos h]
    have hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ h.choose y' ∧ ∀ k, ∃ i, h.choose y' ⟨k, i⟩ ≠ 0 := by
      filter_upwards [h.choose_spec.2] with y' hy'
      exact ⟨hy'.1, hy'.2.1.1⟩
    rw [maDensity_cons_sum L hu hγ, Finset.mul_sum]
  · simp only [dif_neg h, Finset.sum_const_zero]

theorem finsum_mem_sum_comm {α T : Type*} [Fintype T] {S : Set α} (hS : S.Finite) (F : T → α → ℝ) :
    ∑ᶠ w ∈ S, ∑ t, F t w = ∑ t, ∑ᶠ w ∈ S, F t w := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => (finsum_mem_eq_finite_toFinset_sum _ hS).symm

theorem isSmoothHerm_ofWeight {w : ((Σ k, ι k) → ℂ) → ℝ}
    (hw : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → w (fun p => c p.1 * z p) = w z)
    (hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) :
    IsSmoothHerm (HermLine.ofWeight w hw) := by
  have e : (HermLine.ofWeight w hw).h = fun z => Real.exp (-w z) := rfl
  unfold IsSmoothHerm
  rw [e]
  exact Real.contDiff_exp.comp_contDiffOn hs.neg

theorem integrable_fibreSum (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {n : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1 + 1) → ℂ)) (L : Fin n → HermLine ι)
    {f g : ((Σ k, ι k) → ℂ) → ℝ} (hP : IsArithVar P (n + 2)) (hΨ : IsGoodProj P Ψ)
    (hL : ∀ j, IsSmoothHerm (L j)) (hf : IsDegZeroSmooth f) (hg : IsDegZeroSmooth g) :
    Integrable (fun y => ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ (Fin.cons f (pot L)) g y w) := by
  have hf' : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → -f (fun p => c p.1 * z p) = -f z :=
    fun c z hc => by simp only [hf.2 c z hc]
  have hF := isSmoothHerm_ofWeight (w := fun z => -f z) hf' hf.1.neg
  have hG := isSmoothHerm_ofWeight hg.2 hg.1
  have hLF : ∀ j, IsSmoothHerm ((Fin.cons (HermLine.ofWeight (fun z => -f z) hf') L : Fin (n + 1) → HermLine ι) j) := by
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [Fin.cons_zero] using hF
    · simpa only [Fin.cons_succ] using hL j
  have hpot : pot (Fin.cons (HermLine.ofWeight (fun z => -f z) hf') L : Fin (n + 1) → HermLine ι) = Fin.cons f (pot L) := by
    funext j z
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [pot, HermLine.ofWeight, Real.log_exp]
    · simp [pot]
  have hlog : logNorm (HermLine.ofWeight g hg.2) 1 = g := by
    funext z
    simp [logNorm, HermLine.ofWeight, Real.log_exp]
  have h1 : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  have hm : IsMultiHomog (1 : MRing ι) (fun _ => 0) := by
    intro m hm k
    rw [MvPolynomial.support_one] at hm
    simp only [Finset.mem_singleton] at hm
    subst hm
    simp
  have hsec : IsSectionOn P (HermLine.ofWeight g hg.2) 1 :=
    ⟨fun _ => 0, fun k => by simp [HermLine.ofWeight], hm, h1⟩
  have := hInt K ι P (n + 1) Ψ _ _ 1 hP hΨ hLF hG hsec
  rwa [hpot, hlog] at this

end PointsBilinear

open PointsBilinear in

theorem PtsBilinear.proof (hAbs : Inter.PtsAbsIntegrable.Statement) (hMeas : PtsSumMeasurable.Statement) :
    PtsBilinear.Statement := by
  have hInt := PtsIntegrable.of_found hAbs hMeas
  intro K _ ι _ P n L T _ u v hP hL hu hv
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1 + 1) → ℂ), IsGoodProj P Ψ
  · simp only [dif_pos hΨ]
    have hfin := fibreFinite K ι P (n + 1) hΨ.choose hP hΨ.choose_spec
    unfold ptsIntegralAt
    constructor
    · rw [← integral_finsetSum _ fun t _ =>
        integrable_fibreSum hInt hΨ.choose L hP hΨ.choose_spec hL hv (hu t)]
      congr 1
      funext y
      rw [finsum_mem_congr rfl fun w _ => sheetDensity_sum_left P hΨ.choose _ u y w,
        finsum_mem_sum_comm (hfin y)]
    · rw [← integral_finsetSum _ fun t _ =>
        integrable_fibreSum hInt hΨ.choose L hP hΨ.choose_spec hL (hu t) hv]
      congr 1
      funext y
      rw [finsum_mem_congr rfl fun w _ => sheetDensity_sum_right P hΨ.choose L hu v y w,
        finsum_mem_sum_comm (hfin y)]
  · simp only [dif_neg hΨ, Finset.sum_const_zero, and_self]

end GroundTheory.Heights₂.Heights
