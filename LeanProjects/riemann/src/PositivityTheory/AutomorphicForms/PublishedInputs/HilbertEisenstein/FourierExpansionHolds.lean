import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SExpDefs
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.MixedFourierArchSchwartz
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.UnitaryTransvectionZeroSecondMemClosure
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.PointwiseThetaExpansion
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.LocalExpansionHolds
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.AbsoluteConvergenceHolds
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.MeasurePreservingPhiA
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.IdeleModuleFiniteEmbeddingUnit

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published Filter Topology

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem norm_omega {ω : HChar F} (hfin : IsOfFinOrder ω) (τ : IdeleGroup F) :
    ‖((ω.1 τ : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_iff_pow_eq_one).1 hfin
  have h : ((ω.1 τ : ℂˣ) : ℂ) ^ n = 1 := by
    have h1 : (ω ^ n).1 τ = 1 := by rw [hpow]; rfl
    rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, ← Subgroup.coe_pow, h1, Units.val_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 (by rw [← norm_pow, h, norm_one])

theorem norm_ex (ξ : F) (x : UpperTheory.V.TR.Rinf F) : ‖ex ξ x‖ = 1 := by
  have : 2 * Real.pi * Complex.I * ∑ v, (reAt v ξ : ℂ) * (x v : ℂ) =
      ((2 * Real.pi * ∑ v, reAt v ξ * x v : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [ex, this, Complex.norm_exp_ofReal_mul_I]

theorem norm_wt {ω : HChar F} (hfin : IsOfFinOrder ω) (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) :
    ‖wt ω t u‖ = (t : ℝ) := by
  rw [wt, norm_mul, norm_inv, norm_omega hfin, inv_one, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos t.2]

theorem continuous_wt (ω : HChar F) : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F => wt ω p.1 p.2 := by
  have hω : Continuous ω.1 := ω.2.1
  have ht : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F => tau p.1 p.2 :=
    ((continuous_moduleSection (w0 F)).comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have h1 : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F => ((ω.1 (tau p.1 p.2) : ℂˣ) : ℂ)⁻¹ := by
    have : Continuous fun p : {r : ℝ // 0 < r} × normOneSubgroup F => (((ω.1 (tau p.1 p.2))⁻¹ : ℂˣ) : ℂ) :=
      Units.continuous_val.comp ((hω.comp ht).inv)
    simpa using this
  exact h1.mul (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst))

theorem norm_infEq (r : UpperTheory.V.TR.Rinf F) (w : InfinitePlace F) : ‖UpperTheory.V.TR.infEq F r w‖ = |r w| := by
  have hv := IsTotallyReal.isReal w
  have h := (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.dist_eq (r w) 0
  have h0 : (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm 0 = 0 :=
    map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm
  rw [h0, dist_zero_right, dist_zero_right, Real.norm_eq_abs] at h
  exact h

theorem infId_val (y : (UpperTheory.V.TR.Rinf F)ˣ) :
    ((UpperTheory.V.TR.infId F y : (Ad F)ˣ) : Ad F) = (UpperTheory.V.TR.infEq F y.val, 1) := by
  change 1 - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F y.val = _
  refine Prod.ext ?_ ?_
  · change (1 : InfiniteAdeleRing F) - UpperTheory.V.TR.infEq F 1 + UpperTheory.V.TR.infEq F y.val = _
    rw [map_one, sub_self, zero_add]
  · change (1 : Af F) - 0 + 0 = 1
    rw [sub_zero, add_zero]

theorem finId_val (yf : (Af F)ˣ) : ((finId F yf : (Ad F)ˣ) : Ad F) = (1, (yf : Af F)) := by
  change 1 - sFin F 1 + sFin F yf.val = _
  refine Prod.ext ?_ ?_
  · change (1 : InfiniteAdeleRing F) - 0 + 0 = 1
    rw [sub_zero, add_zero]
  · change (1 : Af F) - 1 + (yf : Af F) = _
    rw [sub_self, zero_add]

theorem absD_gPt (x : UpperTheory.V.TR.Rinf F) (y : (UpperTheory.V.TR.Rinf F)ˣ) (hy : ∀ v, 0 < y.val v) (yf : (Af F)ˣ) :
    absD (gPt x y yf) = (∏ v, y.val v) * absF yf := by
  have hdet1 : Matrix.GeneralLinearGroup.det (aff y x) = y := by
    ext1
    simp [aff, Matrix.det_fin_two_of]
  have hdet2 : Matrix.GeneralLinearGroup.det (aff yf (0 : Af F)) = yf := by
    ext1
    simp [aff, Matrix.det_fin_two_of]
  unfold absD gPt
  rw [map_mul, UpperTheory.V.TR.det_infGL, UpperTheory.V.TR.det_finGL, hdet1, hdet2, map_mul]
  change (IdeleGroup.ideleModule F _ : ℝ) * (IdeleGroup.ideleModule F _ : ℝ) = _
  rw [ideleModule_eq, ideleModule_eq]
  simp only [infId_val, finId_val]
  have h1 : ∏ w : InfinitePlace F, ‖UpperTheory.V.TR.infEq F y.val w‖ ^ w.mult = ∏ v, y.val v := by
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [(IsTotallyReal.isReal w).mult_eq_one, pow_one, norm_infEq, abs_of_pos (hy w)]
  have h2 : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(1 : Af F) v‖ = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => by simp
  have h3 : ∏ w : InfinitePlace F, ‖(1 : InfiniteAdeleRing F) w‖ ^ w.mult = 1 :=
    Finset.prod_eq_one fun w _ => (by rw [norm_one, one_pow] : ‖(1 : w.Completion)‖ ^ w.mult = 1)
  rw [h1, h2, h3, mul_one, one_mul]
  rfl

theorem gPt_eq (x : UpperTheory.V.TR.Rinf F) (y : (UpperTheory.V.TR.Rinf F)ˣ) (yf : (Af F)ˣ) :
    UpperTheory.V.TR.infGL F 2 (aff y x) * finGL F 2 (aff yf 0) = gPt x y yf := rfl

theorem coefAt_const_mul (a : ℂ) (d : Ideal (𝓞 F) → ℂ) (z : Af F) :
    coefAt (fun 𝔪 => a * d 𝔪) z = a * coefAt d z := by
  unfold coefAt
  split_ifs <;> simp

theorem ne_zero_of_pos {ξ : F} (h : ∀ v, 0 < reAt v ξ) : ξ ≠ 0 := by
  rintro rfl
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  simpa [reAt] using h v

theorem sExp_assembly (hPt : SPoint) (hZ : SZero) (hNl : SNull) (hA : SAbs) (hU : SUnfold) (hL : SLocal) :
    SInt → SExp := by
  intro hI F _ _ _ ω c H
  obtain ⟨C₀, hC₀, hloc⟩ := hL F ω c H
  refine ⟨C₀, ∫ p, zeroRow c (tau p.1 p.2) * wt ω p.1 p.2 ∂(muE F), hC₀, ?_⟩
  intro x y hy yf
  set Y := yAd y yf
  set g := gPt x y yf
  set D : ℂ := ((absD g ^ ((1 : ℝ) / 2) : ℝ) : ℂ) with hDdef
  set A0 : {r : ℝ // 0 < r} × normOneSubgroup F → ℂ := fun p => zeroRow c (tau p.1 p.2) * wt ω p.1 p.2
  set N : {r : ℝ // 0 < r} × normOneSubgroup F → ℂ := fun p => coefK c Y (tau p.1 p.2) 0 * wt ω p.1 p.2
  set Sf : Fˣ → {r : ℝ // 0 < r} × normOneSubgroup F → ℂ :=
    fun ξ p => ex (ξ : F) x * coefK c Y (tau p.1 p.2) ξ * wt ω p.1 p.2
  set S : {r : ℝ // 0 < r} × normOneSubgroup F → ℂ := fun p => ∑' ξ : Fˣ, Sf ξ p
  obtain ⟨hmeas, hsum, hint⟩ := hA F ω c H y hy yf
  have hfin := H.fin

  have hpt : ∀ p : {r : ℝ // 0 < r} × normOneSubgroup F, eisInt ω (Phi c) g p.1 p.2 = (A0 p + N p + S p) * D := by
    intro p
    have h := hPt F ω c H x y hy yf (tau p.1 p.2)
    simp only [eisInt, A0, N, S, Sf]
    change thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) (tau p.1 p.2) * g) * _ * _ * _ = _
    rw [h, tsum_mul_right]
    simp only [wt, tau, hDdef]
    ring
  have hDpos : 0 < absD g := (IdeleGroup.ideleModule F _).2
  have hD0 : D ≠ 0 := by
    rw [hDdef, Complex.ofReal_ne_zero]
    exact (Real.rpow_pos_of_pos hDpos _).ne'

  have hT : Integrable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => eisInt ω (Phi c) g p.1 p.2) (muE F) :=
    hI F ω c H g
  have hA0 : Integrable A0 (muE F) := hZ F ω c H
  have hSfm : ∀ ξ : Fˣ, AEStronglyMeasurable (Sf ξ) (muE F) := fun ξ =>
    (aestronglyMeasurable_const.mul (hmeas ξ)).mul (continuous_wt ω).aestronglyMeasurable
  have hSfb : ∀ ξ : Fˣ, ∀ p, ‖Sf ξ p‖ = ‖coefK c Y (tau p.1 p.2) ξ‖ * (p.1 : ℝ) := by
    intro ξ p
    simp only [Sf, norm_mul, norm_ex, norm_wt hfin, one_mul]
  have hSsum : ∀ p, HasSum (fun ξ : Fˣ => Sf ξ p) (S p) := by
    intro p
    refine Summable.hasSum (Summable.of_norm ?_)
    simp only [hSfb]
    exact (hsum p).mul_right _
  have hbound : Integrable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
      ∑' ξ : Fˣ, ‖coefK c Y (tau p.1 p.2) ξ‖ * (p.1 : ℝ)) (muE F) := by
    simp only [tsum_mul_right]
    exact hint
  have hSint : HasSum (fun ξ : Fˣ => ∫ p, Sf ξ p ∂(muE F)) (∫ p, S p ∂(muE F)) :=
    hasSum_integral_of_dominated_convergence (fun ξ p => ‖coefK c Y (tau p.1 p.2) ξ‖ * (p.1 : ℝ)) hSfm
      (fun ξ => Eventually.of_forall fun p => (hSfb ξ p).le)
      (Eventually.of_forall fun p => (hsum p).mul_right _) hbound (Eventually.of_forall hSsum)
  have hSm : AEStronglyMeasurable S (muE F) := by
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop) (f := fun s p => ∑ ξ ∈ s, Sf ξ p)
      (fun s => by
        have h := Finset.aestronglyMeasurable_sum (μ := muE F) s fun ξ _ => hSfm ξ
        convert h using 1
        funext p
        simp [Finset.sum_apply]) (Eventually.of_forall fun p => (hSsum p))
  have hS : Integrable S (muE F) := by
    refine hbound.mono' hSm (Eventually.of_forall fun p => ?_)
    rw [← (hSsum p).tsum_eq]
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
    · simp only [hSfb]; exact (hsum p).mul_right _
    · simp only [hSfb]
  have hN : Integrable N (muE F) := by
    have h1 : Integrable (fun p => eisInt ω (Phi c) g p.1 p.2 / D - A0 p - S p) (muE F) :=
      ((hT.div_const D).sub hA0).sub hS
    refine h1.congr (Eventually.of_forall fun p => ?_)
    simp only [hpt p]
    field_simp
    ring

  have hN0 : ∫ p, N p ∂(muE F) = 0 := by
    rw [integral_prod N hN]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hN.prod_right_ae] with t ht
    have h2 : IntegrableOn (fun u => coefK c Y (tau t u) 0 * ((ω.1 (tau t u) : ℂˣ) : ℂ)⁻¹)
        (normOneFundamentalDomain F) (normOneMeasure F) := by
      have h3 := ht.mul_const (((t : ℝ) : ℂ)⁻¹)
      refine h3.congr (Eventually.of_forall fun u => ?_)
      have ht0 : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 t.2.ne'
      simp only [N, wt]
      field_simp
    have h4 := hNl F ω c H y yf t h2
    simp only [Pi.zero_apply, N, wt]
    simp_rw [← mul_assoc]
    rw [integral_mul_const, h4, zero_mul]

  have hcoef : ∀ ξ : Fˣ, ∫ p, Sf ξ p ∂(muE F) = ex (ξ : F) x * (C₀ * if ∀ v, 0 < reAt v (ξ : F) then
        coefAt (divS ω c) (algebraMap F (Af F) (ξ : F) * (yf : Af F)) *
          Complex.exp (-(2 * Real.pi : ℂ) * ∑ v, (reAt v (ξ : F) : ℂ) * (y.val v : ℂ))
      else 0) := by
    intro ξ
    obtain ⟨hi, he⟩ := hloc y hy yf ξ
    simp only [Sf, mul_assoc]
    rw [integral_const_mul, hU F ω c H Y ξ hi, he]

  have htot : Eis ω (Phi c) g = (∫ p, A0 p ∂(muE F) + ∫ p, S p ∂(muE F)) * D := by
    have h1 : Eis ω (Phi c) g = ∫ p, eisInt ω (Phi c) g p.1 p.2 ∂(muE F) := by
      rw [Eis, integral_prod _ hT]
    rw [h1]
    simp only [hpt]
    rw [integral_mul_const, integral_add (f := fun a => A0 a + N a) (hA0.add hN) hS, integral_add hA0 hN, hN0,
      add_zero]
  have hDeq : D = ((((∏ v, y.val v) * absF yf) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) := by
    rw [hDdef, absD_gPt x y hy yf]
    norm_num
  have hval : Eis ω (Phi c) (UpperTheory.V.TR.infGL F 2 (aff y x) * finGL F 2 (aff yf 0)) /
      ((((∏ v, y.val v) * absF yf) ^ (((1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) - ∫ p, A0 p ∂(muE F) = ∫ p, S p ∂(muE F) := by
    rw [gPt_eq, ← hDeq, htot]
    field_simp
    ring
  rw [hval]
  let e : {ξ : F // ∀ v, 0 < reAt v ξ} → Fˣ := fun ξ => Units.mk0 ξ.1 (ne_zero_of_pos ξ.2)
  have he : Function.Injective e := fun a b h => Subtype.ext (congrArg Units.val h)
  have hout : ∀ ξ ∉ Set.range e, (fun ξ : Fˣ => ∫ p, Sf ξ p ∂(muE F)) ξ = 0 := by
    intro ξ hξ
    simp only [hcoef]
    rw [if_neg, mul_zero, mul_zero]
    intro hpos
    exact hξ ⟨⟨ξ, hpos⟩, Units.ext rfl⟩
  have h2 := (he.hasSum_iff hout).2 hSint
  convert h2 using 1
  funext ξ
  simp only [Function.comp_apply, hcoef, e, Units.val_mk0]
  have hξ2 := ξ.2
  simp only [hξ2, implies_true, ↓reduceIte]
  show coefAt (fun 𝔪 => C₀ * divS ω c 𝔪) _ * _ = _
  rw [coefAt_const_mul, ex]
  have hs : ∑ v, (reAt v ξ.1 : ℂ) * ((x v : ℂ) + Complex.I * (y.val v : ℂ)) =
      ∑ v, (reAt v ξ.1 : ℂ) * (x v : ℂ) + Complex.I * ∑ v, (reAt v ξ.1 : ℂ) * (y.val v : ℂ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  have hexp : Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v ξ.1 : ℂ) * ((x v : ℂ) + Complex.I * (y.val v : ℂ))) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v ξ.1 : ℂ) * (x v : ℂ)) *
        Complex.exp (-(2 * Real.pi : ℂ) * ∑ v, (reAt v ξ.1 : ℂ) * (y.val v : ℂ)) := by
    rw [← Complex.exp_add, hs]
    congr 1
    linear_combination (2 * (Real.pi : ℂ) * ∑ v, (reAt v ξ.1 : ℂ) * (y.val v : ℂ)) * Complex.I_sq
  rw [hexp]
  ring

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

namespace UpperTheory.HilbertEisensteinWeightOne

theorem fourier_expansion_holds : SPois → SInt → SSmooth → SExp := fun hP hI _ =>
  FourierExpansionEisenstein.sExp_assembly (FourierExpansionEisenstein.pointwise_theta_expansion hP FourierExpansionEisenstein.finite_expansion_holds FourierExpansionEisenstein.kernel_expansion_holds) FourierExpansionEisenstein.zero_term_holds
    (FourierExpansionEisenstein.null_term_holds FourierExpansionEisenstein.finite_expansion_holds FourierExpansionEisenstein.kernel_expansion_holds) (FourierExpansionEisenstein.absolute_convergence_holds FourierExpansionEisenstein.finite_expansion_holds FourierExpansionEisenstein.kernel_expansion_holds) FourierExpansionEisenstein.sUnfold_statement (FourierExpansionEisenstein.local_expansion_holds FourierExpansionEisenstein.finite_expansion_holds FourierExpansionEisenstein.kernel_expansion_holds) hI

end UpperTheory.HilbertEisensteinWeightOne
