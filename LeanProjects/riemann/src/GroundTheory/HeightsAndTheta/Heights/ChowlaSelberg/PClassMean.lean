import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic Filter Topology
open scoped nonZeroDivisors Real ModularForm UpperHalfPlane

noncomputable section

namespace ClassMean

theorem volume_real_fundamentalDomain_basisOneI :
    MeasureTheory.volume.real (ZSpan.fundamentalDomain Complex.basisOneI) = 1 := by
  rw [MeasureTheory.measureReal_congr
    (ZSpan.fundamentalDomain_ae_parallelepiped Complex.basisOneI MeasureTheory.volume),
    MeasureTheory.measureReal_def]
  have h : parallelepiped (⇑Complex.basisOneI) = parallelepiped (⇑Complex.orthonormalBasisOneI) := by
    rw [Complex.coe_orthonormalBasisOneI, Complex.coe_basisOneI]
  rw [h, Complex.orthonormalBasisOneI.volume_parallelepiped]
  simp

theorem latticeArea_periodPair (L : PeriodPair) :
    latticeArea L.lattice = |L.ω₁.re * L.ω₂.im - L.ω₂.re * L.ω₁.im| := by
  rw [latticeArea, ZLattice.covolume_eq_det_mul_measureReal L.lattice MeasureTheory.volume
    L.latticeBasis Complex.basisOneI, volume_real_fundamentalDomain_basisOneI, mul_one,
    Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply, Complex.coe_basisOneI_repr]

theorem scaleLattice_latticeOfTau (c : ℂ) (τ : ℍ) :
    scaleLattice c (latticeOfTau τ).lattice = Submodule.span ℤ {c * τ, c} := by
  rw [scaleLattice, PeriodPair.lattice, Submodule.map_span, Set.image_pair]
  simp

def scaledPair (c : ℂ) (hc : c ≠ 0) (τ : ℍ) : PeriodPair where
  ω₁ := c * τ
  ω₂ := c
  indep := by
    refine LinearIndependent.pair_iff.2 fun s t h ↦ ?_
    have h' : c * ((s : ℂ) * τ + t) = 0 := by
      rw [← h, Complex.real_smul, Complex.real_smul]; ring
    have h'' := (mul_eq_zero.1 h').resolve_left hc
    refine LinearIndependent.pair_iff.1 (latticeOfTau τ).indep s t ?_
    simpa [Complex.real_smul] using h''

theorem scaledPair_lattice (c : ℂ) (hc : c ≠ 0) (τ : ℍ) :
    (scaledPair c hc τ).lattice = scaleLattice c (latticeOfTau τ).lattice := by
  rw [scaleLattice_latticeOfTau]; rfl

theorem latticeArea_scaleLattice (c : ℂ) (hc : c ≠ 0) (τ : ℍ) :
    latticeArea (scaleLattice c (latticeOfTau τ).lattice) = ‖c‖ ^ 2 * τ.im := by
  rw [← scaledPair_lattice c hc τ, latticeArea_periodPair]
  have : (scaledPair c hc τ).ω₁.re * (scaledPair c hc τ).ω₂.im -
      (scaledPair c hc τ).ω₂.re * (scaledPair c hc τ).ω₁.im = -(‖c‖ ^ 2 * τ.im) := by
    simp only [scaledPair, Complex.mul_re, Complex.mul_im, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply, UpperHalfPlane.coe_im, UpperHalfPlane.coe_re]
    ring
  rw [this, abs_neg, abs_of_nonneg (by positivity)]

theorem epsteinSum_scaleLattice (c : ℂ) (hc : c ≠ 0) (τ : ℍ) {s : ℝ} (hs : 0 < s) :
    epsteinSum (scaleLattice c (latticeOfTau τ).lattice) s = kroneckerSum τ s := by
  have harea := latticeArea_scaleLattice c hc τ
  rw [← scaledPair_lattice c hc τ] at harea ⊢
  unfold epsteinSum kroneckerSum
  rw [harea, ← (scaledPair c hc τ).latticeEquivProd.symm.toEquiv.tsum_eq]
  refine tsum_congr fun p ↦ ?_
  simp only [LinearEquiv.coe_toEquiv, PeriodPair.latticeEquiv_symm_apply]
  have key : (p.1 : ℂ) * (scaledPair c hc τ).ω₁ + p.2 * (scaledPair c hc τ).ω₂ =
      c * (p.1 * τ + p.2) := by
    simp only [scaledPair]; ring
  rw [key]
  have h2s : 2 * s ≠ 0 := by positivity
  by_cases hp : p = 0
  · subst hp; simp
  rw [if_neg hp]
  split_ifs with h0
  · rw [(mul_eq_zero.1 h0).resolve_left hc, norm_zero, Real.zero_rpow h2s, div_zero]
  have hc' : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hpow : (‖c‖ ^ 2) ^ s = ‖c‖ ^ (2 * s) := by rw [Real.rpow_mul hc'.le, Real.rpow_two]
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
    Real.mul_rpow (by positivity) τ.im_pos.le, hpow,
    mul_div_mul_left _ _ (Real.rpow_pos_of_pos hc' _).ne']

theorem span_neg_pair (a b : ℂ) :
    Submodule.span ℤ {-a, b} = Submodule.span ℤ ({a, b} : Set ℂ) := by
  rw [Submodule.span_insert, Submodule.span_insert, ← Set.neg_singleton, Submodule.span_neg]

theorem exists_eq_scaleLattice (L : PeriodPair) :
    ∃ (τ : ℍ) (c : ℂ), c ≠ 0 ∧ L.lattice = scaleLattice c (latticeOfTau τ).lattice := by
  have h2 : L.ω₂ ≠ 0 := by simpa using L.indep.ne_zero 1
  set t := L.ω₁ / L.ω₂ with ht_def
  have h1 : L.ω₁ = t * L.ω₂ := (div_mul_cancel₀ _ h2).symm
  have ht : t.im ≠ 0 := by
    intro h
    have e : L.ω₁ = (t.re : ℂ) * L.ω₂ := by
      rw [h1]; congr 1; exact Complex.ext (by simp) (by simp [h])
    have := LinearIndependent.pair_iff.1 L.indep 1 (-t.re)
      (by rw [Complex.real_smul, Complex.real_smul, e]; push_cast; ring)
    exact one_ne_zero this.1
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · refine ⟨⟨-t, by simpa using neg_pos.2 hneg⟩, L.ω₂, h2, ?_⟩
    rw [scaleLattice_latticeOfTau, PeriodPair.lattice, h1]
    rw [show L.ω₂ * -t = -(t * L.ω₂) by ring, span_neg_pair]
  · refine ⟨⟨t, hpos⟩, L.ω₂, h2, ?_⟩
    rw [scaleLattice_latticeOfTau, PeriodPair.lattice, h1]
    rw [mul_comm]

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

theorem discr_neg (S : PrimeDiscriminant K) : discr K < 0 := by
  rw [S.discr_eq]; simpa using S.prime.pos

theorem isTotallyComplex (S : PrimeDiscriminant K) : IsTotallyComplex K :=
  nrRealPlaces_eq_zero_iff.1 (Quadratic.places_of_discr_neg K (discr_neg S)).1

theorem exists_classLattice_eq (S : PrimeDiscriminant K) (σ : K →+* ℂ) (C : ClassGroup (𝓞 K)) :
    ∃ (τ : ℍ) (c : ℂ), c ≠ 0 ∧ classLattice σ C = scaleLattice c (latticeOfTau τ).lattice := by
  have := isTotallyComplex S
  have hK : Module.finrank ℚ K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K
  have e : classLattice σ C =
      (idealPeriodPair σ hK (FractionalIdeal.mk0 K (classRep C))).lattice := by
    rw [lattice_idealPeriodPair]; rfl
  rw [e]; exact exists_eq_scaleLattice _

theorem LFunction_one_eq (S : PrimeDiscriminant K) :
    DirichletCharacter.LFunction (Quadratic.kronecker K) 1 =
      (((Units.torsionOrder K : ℝ)⁻¹ * (2 / Real.sqrt S.d) * classNumber K * π : ℝ) : ℂ) := by
  have hcn := Quadratic.classNumber_eq_of_discr_neg K (discr_neg S)
  have habs : |((discr K : ℤ) : ℝ)| = S.d := by
    rw [S.discr_eq]; push_cast; rw [abs_neg]; exact abs_of_nonneg (Nat.cast_nonneg _)
  rw [habs] at hcn
  have hd : (0 : ℝ) < S.d := by exact_mod_cast S.prime.pos
  have hw : (Units.torsionOrder K : ℂ) ≠ 0 := by exact_mod_cast Units.torsionOrder_ne_zero K
  have hs : ((Real.sqrt S.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hd).ne'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  rw [hcn]
  field_simp

end ClassMean

open ClassMean in

theorem ClassMean.proof {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]
    (S : PrimeDiscriminant K) (hKL : KroneckerLimit.Statement) (hCE : ClassEpstein.Statement S)
    (hZF : ZetaFactor.Statement S) (hPT : PhTau.Statement) (hPS : PhScale.Statement) :
    ClassMean.Statement S := by
  intro σ
  classical
  have hd : (0 : ℝ) < S.d := by exact_mod_cast S.prime.pos
  have hsq : 0 < Real.sqrt S.d := Real.sqrt_pos.2 hd
  have ha : 0 < 2 / Real.sqrt S.d := by positivity
  have hw : (0 : ℝ) < Units.torsionOrder K := by
    exact_mod_cast Nat.pos_of_ne_zero (Units.torsionOrder_ne_zero K)
  have hh : (0 : ℝ) < classNumber K := by exact_mod_cast Fintype.card_pos
  choose τ c hc hΛ using fun C ↦ exists_classLattice_eq S σ C

  have hph : ∀ C, classLogPeriod σ C =
      Real.log (4 * π) + 2 * Real.log (Real.sqrt (τ C).im * ‖η (τ C : ℂ)‖ ^ 2) := by
    intro C
    have hη : 0 < ‖η (τ C : ℂ)‖ := norm_pos_iff.2 (ModularForm.eta_ne_zero (τ C).im_pos)
    have hy := (τ C).im_pos
    rw [classLogPeriod, hΛ C, hPS _ _ (hc C), hPT]
    have e : 4 * π * (τ C).im * ‖η (τ C : ℂ)‖ ^ 4 =
        4 * π * (Real.sqrt (τ C).im * ‖η (τ C : ℂ)‖ ^ 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hy.le]; ring
    have hpos : 0 < Real.sqrt (τ C).im * ‖η (τ C : ℂ)‖ ^ 2 :=
      mul_pos (Real.sqrt_pos.2 hy) (pow_pos hη 2)
    rw [e, Real.log_mul (by positivity) (pow_pos hpos 2).ne', Real.log_pow]
    push_cast; ring

  have hzeta : ∀ s : ℝ, 1 < s → riemannZeta s * DirichletCharacter.LFunction (Quadratic.kronecker K) s =
      (((Units.torsionOrder K : ℝ)⁻¹ * (2 / Real.sqrt S.d) ^ s *
        ∑ C, kroneckerSum (τ C) s : ℝ) : ℂ) := by
    intro s hs
    obtain ⟨h1, h2⟩ := hZF s hs
    rw [← h1, ← h2, Finset.mul_sum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun C _ ↦ ?_
    rw [hCE σ C (FractionalIdeal.mk0 K (classRep C)) (by rw [ClassGroup.mk_mk0, mk0_classGroupRep]) s hs]
    change ((_ * _ * epsteinSum (classLattice σ C) s : ℝ) : ℂ) = _
    rw [hΛ C, epsteinSum_scaleLattice _ (hc C) _ (by linarith)]

  have hF : Tendsto (fun s : ℝ ↦ ∑ C, kroneckerSum (τ C) s - classNumber K * π / (s - 1)) (𝓝[>] 1)
      (𝓝 (2 * π * ∑ C, (Real.eulerMascheroniConstant - Real.log 2 -
        Real.log (Real.sqrt (τ C).im * ‖η (τ C : ℂ)‖ ^ 2)))) := by
    rw [Finset.mul_sum]
    refine (tendsto_finsetSum Finset.univ fun C _ ↦ hKL (τ C)).congr fun s ↦ ?_
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_assoc]
    rfl

  set Lf := DirichletCharacter.LFunction (Quadratic.kronecker K) with hLf
  set a : ℝ := 2 / Real.sqrt S.d with ha_def
  set w : ℝ := (Units.torsionOrder K : ℝ) with hw_def
  set h : ℝ := (classNumber K : ℝ) with hh_def
  set F : ℝ → ℝ := fun s ↦ ∑ C, kroneckerSum (τ C) s with hF_def
  set B : ℝ := ∑ C, (Real.eulerMascheroniConstant - Real.log 2 -
    Real.log (Real.sqrt (τ C).im * ‖η (τ C : ℂ)‖ ^ 2)) with hB_def
  have hL1 : Lf 1 = ((w⁻¹ * a * h * π : ℝ) : ℂ) := LFunction_one_eq S
  have hcplx : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun s hs ↦ ?_⟩
    · simpa using (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    · simpa [Complex.ofReal_eq_one] using (ne_of_gt hs)
  have hdiff := DirichletCharacter.differentiable_LFunction (Quadratic.kronecker_ne_one K)
  have hD : Tendsto (fun s : ℝ ↦ (Lf s - Lf 1) / ((s : ℂ) - 1)) (𝓝[>] 1) (𝓝 (deriv Lf 1)) := by
    refine ((hasDerivAt_iff_tendsto_slope.1 (hdiff 1).hasDerivAt).comp hcplx).congr fun s ↦ ?_
    simp [slope_def_field, hLf]
  have hLc : Tendsto (fun s : ℝ ↦ Lf s) (𝓝[>] 1) (𝓝 (Lf 1)) :=
    (hdiff.continuous.tendsto 1).comp (hcplx.mono_right nhdsWithin_le_nhds)
  have hA : Tendsto (fun s : ℝ ↦ (a ^ s - a) / (s - 1)) (𝓝[>] 1) (𝓝 (a * Real.log a)) := by
    have hder := (Real.hasStrictDerivAt_const_rpow ha 1).hasDerivAt
    have hsl := (hasDerivAt_iff_tendsto_slope.1 hder).mono_left
      (nhdsWithin_mono _ fun x (hx : 1 < x) ↦ ne_of_gt hx)
    rw [Real.rpow_one] at hsl
    refine hsl.congr fun s ↦ ?_
    simp [slope_def_field, Real.rpow_one]
  have hP : Tendsto (fun s : ℝ ↦ a ^ s) (𝓝[>] 1) (𝓝 a) := by
    simpa using ((Real.continuousAt_const_rpow ha.ne' (b := 1)).tendsto).mono_left nhdsWithin_le_nhds
  have hlim1 : Tendsto (fun s : ℝ ↦ (Lf s - Lf 1) / ((s : ℂ) - 1) +
      (riemannZeta s - 1 / ((s : ℂ) - 1)) * Lf s) (𝓝[>] 1)
      (𝓝 (deriv Lf 1 + Real.eulerMascheroniConstant * Lf 1)) :=
    hD.add (ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right.mul hLc)
  have hlim2 : Tendsto (fun s : ℝ ↦ ((w⁻¹ * ((a ^ s - a) / (s - 1) * h * π +
      a ^ s * (F s - h * π / (s - 1))) : ℝ) : ℂ)) (𝓝[>] 1)
      (𝓝 ((w⁻¹ * (a * Real.log a * h * π + a * (2 * π * B)) : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp
      (Tendsto.const_mul w⁻¹ (((hA.mul_const h).mul_const π).add (hP.mul hF)))
  have heq : ∀ s : ℝ, 1 < s → (Lf s - Lf 1) / ((s : ℂ) - 1) +
      (riemannZeta s - 1 / ((s : ℂ) - 1)) * Lf s =
      ((w⁻¹ * ((a ^ s - a) / (s - 1) * h * π + a ^ s * (F s - h * π / (s - 1))) : ℝ) : ℂ) := by
    intro s hs
    have hz : riemannZeta s * Lf s = ((w⁻¹ * a ^ s * F s : ℝ) : ℂ) := hzeta s hs
    have hx : (s : ℂ) - 1 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast (ne_of_gt hs))
    have hxr : s - 1 ≠ 0 := sub_ne_zero.2 (ne_of_gt hs)
    generalize a ^ s = P at hz ⊢
    generalize F s = Fs at hz ⊢
    generalize riemannZeta s = Z at hz ⊢
    generalize Lf s = Ls at hz ⊢
    rw [hL1]
    push_cast at hz ⊢
    field_simp
    linear_combination ((s : ℂ) - 1) * hz
  have hlim1' : Tendsto (fun s : ℝ ↦ ((w⁻¹ * ((a ^ s - a) / (s - 1) * h * π +
      a ^ s * (F s - h * π / (s - 1))) : ℝ) : ℂ)) (𝓝[>] 1)
      (𝓝 (deriv Lf 1 + Real.eulerMascheroniConstant * Lf 1)) :=
    hlim1.congr' (eventually_nhdsWithin_of_forall fun s hs ↦ heq s hs)
  have key : deriv Lf 1 + Real.eulerMascheroniConstant * Lf 1 =
      ((w⁻¹ * (a * Real.log a * h * π + a * (2 * π * B)) : ℝ) : ℂ) :=
    tendsto_nhds_unique hlim1' hlim2

  set T : ℝ := ∑ C, Real.log (Real.sqrt (τ C).im * ‖η (τ C : ℂ)‖ ^ 2) with hT_def
  have hcm : classMean σ = h⁻¹ * (h * Real.log (4 * π) + 2 * T) := by
    rw [classMean]
    simp only [hph, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum]
    rfl
  have hB : B = h * Real.eulerMascheroniConstant - h * Real.log 2 - T := by
    rw [hB_def, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
    rfl
  have hL' : deriv Lf 1 = ((w⁻¹ * (a * Real.log a * h * π + a * (2 * π * B)) -
      Real.eulerMascheroniConstant * (w⁻¹ * a * h * π) : ℝ) : ℂ) := by
    rw [hL1] at key
    push_cast at key ⊢
    linear_combination key
  have hw0 : w ≠ 0 := hw.ne'
  have hh0 : h ≠ 0 := hh.ne'
  have ha0 : a ≠ 0 := ha.ne'
  have hπ0 : π ≠ 0 := Real.pi_ne_zero
  have hl4 : Real.log (4 * π) = 2 * Real.log 2 + Real.log π := by
    rw [Real.log_mul (by norm_num) hπ0, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have hl2 : Real.log (2 * π / Real.sqrt S.d) = Real.log 2 + Real.log π - Real.log (Real.sqrt S.d) := by
    rw [Real.log_div (by positivity) hsq.ne', Real.log_mul two_ne_zero hπ0]
  have hla : Real.log a = Real.log 2 - Real.log (Real.sqrt S.d) :=
    Real.log_div two_ne_zero hsq.ne'
  have hreal : classMean σ = Real.eulerMascheroniConstant + Real.log (2 * π / Real.sqrt S.d) -
      (w⁻¹ * (a * Real.log a * h * π + a * (2 * π * B)) -
        Real.eulerMascheroniConstant * (w⁻¹ * a * h * π)) / (w⁻¹ * a * h * π) := by
    rw [hcm, hB, hl4, hl2, hla]
    field_simp
    ring
  rw [hL', hL1, hreal]
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
