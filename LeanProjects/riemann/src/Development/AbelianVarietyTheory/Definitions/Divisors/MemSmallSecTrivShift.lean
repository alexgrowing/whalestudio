import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.VolumeBallOne

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V cHess leviV wd wdb bas)
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open scoped ContDiff ENNReal

namespace GlobalTheory.ArithHeightModel

variable {k : Type} [CommRing k] {σ : k →+* ℂ} {D : ℕ}

def pt (σ : k →+* ℂ) (v : V D) : CxPts (CanonLB.affStr k D) σ :=
  ofHom (isAffineOpen_top _) ((MvPolynomial.eval₂Hom σ fun a => v a).comp
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin D) k))).hom.hom) fun a => by
    have := RingHom.congr_fun (CanonLB.polyFn_comp k D) a
    rw [← this]
    simp [CanonLB.polyFn]

theorem ev_pt (v : V D) (P : MvPolynomial (Fin D) k) :
    ev _ σ ⊤ (CanonLB.polyFn P) (pt σ v) = MvPolynomial.eval₂Hom σ (fun a => v a) P := by
  rw [pt, ev_ofHom]
  simp [CanonLB.polyFn]

theorem polyFn_surj : Function.Surjective (CanonLB.polyFn : MvPolynomial (Fin D) k → _) :=
  (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin D) k))).inv).2

theorem diff_pt (a : Γ(Sp (MvPolynomial (Fin D) k), ⊤)) :
    DifferentiableOn ℂ (ev (CanonLB.affStr k D) σ ⊤ a ∘ pt σ) univ := by
  obtain ⟨P, rfl⟩ := polyFn_surj a
  refine Differentiable.differentiableOn ?_
  have : ev (CanonLB.affStr k D) σ ⊤ (CanonLB.polyFn P) ∘ pt σ =
    fun v : V D => MvPolynomial.eval₂Hom σ (fun a => v a) P := funext fun v => ev_pt v P
  rw [this]
  clear this
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p n hp =>
    simp only [map_mul, MvPolynomial.eval₂Hom_X']
    exact hp.mul (EuclideanSpace.proj (𝕜 := ℂ) n : V D →L[ℂ] ℂ).differentiable

def std (σ : k →+* ℂ) (D : ℕ) : AlgChart (CanonLB.affStr k D) σ D where
  e :=
    { toFun := fun z => WithLp.toLp 2 fun a => AnReadModel.X a z
      invFun := pt σ
      source := univ
      target := univ
      map_source' := fun _ _ => trivial
      map_target' := fun _ _ => trivial
      left_inv' := fun z _ => Subtype.ext (ext_of_valR (isAffineOpen_top _) le_top le_top fun a => by
        obtain ⟨P, rfl⟩ := polyFn_surj a
        refine (ev_pt _ P).trans (Eq.trans ?_ (ev_eq (mem_ptsIn_top (y := z)) _).symm)
        refine RingHom.congr_fun (g := (evHom (mem_ptsIn_top (y := z))).comp CanonLB.polyFn)
          (MvPolynomial.ringHom_ext (fun c => ?_) fun c => ?_) P
        · rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, ← ev_eq]
          exact ((congrArg (ev _ σ ⊤ · z) (RingHom.congr_fun (CanonLB.polyFn_comp k D) c)).trans
            (ev_algX mem_ptsIn_top c)).symm
        · rw [MvPolynomial.eval₂Hom_X', RingHom.comp_apply, ← ev_eq]
          rfl)
      right_inv' := fun v _ => by
        ext a
        exact (ev_pt v _).trans (MvPolynomial.eval₂Hom_X' _ _ a)
      open_source := isOpen_univ
      open_target := isOpen_univ
      continuousOn_toFun := (PiLp.continuous_toLp 2 _).comp_continuousOn
        ((continuousOn_pi.2 fun a => continuousOn_ev _).mono fun _ _ => mem_ptsIn_top)
      continuousOn_invFun := (holo_of_affine (isAffineOpen_top _) isOpen_univ
        (fun _ _ => mem_ptsIn_top) diff_pt).1 }
  U := ⊤
  affine := isAffineOpen_top _
  x a := CanonLB.polyFn (MvPolynomial.X a)
  etale := by
    have he : MvPolynomial.eval₂Hom (algX (CanonLB.affStr k D) ⊤)
        (fun a => CanonLB.polyFn (MvPolynomial.X a)) = CanonLB.polyFn :=
      MvPolynomial.ringHom_ext (fun a => (MvPolynomial.eval₂Hom_C _ _ a).trans
        (RingHom.congr_fun (CanonLB.polyFn_comp k D) a).symm) fun a => MvPolynomial.eval₂Hom_X' _ _ a
    rw [he]
    exact RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin D) k))).inv)
  source_subset _ _ := mem_ptsIn_top
  apply_eq _ _ _ := rfl
  holo := (holo_of_affine (isAffineOpen_top _) isOpen_univ (fun _ _ => mem_ptsIn_top) diff_pt).2

def u (v : V 1) : ℝ := 1 + ((v 0).re ^ 2 + (v 0).im ^ 2)

theorem u_pos (v : V 1) : 0 < u v := by unfold u; positivity

def crd : V 1 →L[ℝ] ℂ := (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1) : V 1 →L[ℂ] ℂ).restrictScalars ℝ

theorem hasFDerivAt_u (v : V 1) : HasFDerivAt u
    ((2 * (v 0).re) • Complex.reCLM.comp crd + (2 * (v 0).im) • Complex.imCLM.comp crd) v := by
  have h₁ := (Complex.reCLM.comp crd).hasFDerivAt (x := v)
  have h₂ := (Complex.imCLM.comp crd).hasFDerivAt (x := v)
  refine HasFDerivAt.congr_fderiv (((h₁.pow 2).add (h₂.pow 2)).const_add 1) ?_
  ext w
  simp [crd]

theorem wdb_log : wdb 1 0 (fun v => (Real.log (u v) : ℂ)) = fun v => v 0 * ((u v)⁻¹ : ℝ) := by
  funext v
  have h := Complex.ofRealCLM.hasFDerivAt.comp v ((hasFDerivAt_u v).log (u_pos v).ne')
  have h' : HasFDerivAt (fun v => (Real.log (u v) : ℂ)) _ v := h
  rw [wdb, h'.fderiv]
  have h2 := Complex.re_add_im (v 0)
  simp [crd, bas]
  linear_combination (u v : ℂ)⁻¹ * h2

theorem cHess_log (v : V 1) : cHess 1 (fun v => (Real.log (u v) : ℂ)) v 0 0 = ((u v ^ 2)⁻¹ : ℝ) := by
  have h := crd.hasFDerivAt.mul (Complex.ofRealCLM.hasFDerivAt.comp v
    ((hasDerivAt_inv (u_pos v).ne').comp_hasFDerivAt v (hasFDerivAt_u v)))
  have h' : HasFDerivAt (fun v : V 1 => v 0 * (((u v)⁻¹ : ℝ) : ℂ)) _ v := h
  rw [cHess, Matrix.of_apply, wdb_log, wd, h'.fderiv]
  have h0 : (u v : ℂ) ≠ 0 := by exact_mod_cast (u_pos v).ne'
  have h1 : (u v : ℂ) = 1 + ((v 0).re ^ 2 + (v 0).im ^ 2) := by simp [u]
  have h2 := Complex.re_add_im (v 0)
  simp [crd, bas]
  field_simp
  linear_combination (exp := 1) 2 * h1 + (2 * (v 0).re - 2 * Complex.I * (v 0).im) * h2 + (2 * (v 0).im ^ 2 - u v) * Complex.I_mul_I

theorem integral_dens : ∫ v : V 1, 1 / Real.pi * (u v ^ 2)⁻¹ = 1 := by
  have hd : Module.finrank ℝ (V 1) = 2 := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (V 1)]; simp
  have hu (v : V 1) : u v = 1 + ‖v‖ ^ 2 := by
    rw [u, EuclideanSpace.norm_sq_eq, Fin.sum_univ_one, Complex.sq_norm, Complex.normSq_apply]
    ring
  have : Nontrivial (V 1) := inferInstance
  have h := integral_fun_norm_addHaar (volume : Measure (V 1))
    (fun r => 1 / Real.pi * ((1 + r ^ 2) ^ 2)⁻¹)
  have hr : ∫ r in Ioi (0 : ℝ), r * ((1 + r ^ 2) ^ 2)⁻¹ = 0 - -(2 * (1 + (0 : ℝ) ^ 2))⁻¹ := by
    refine integral_Ioi_of_hasDerivAt_of_nonneg' (g := fun r => -(2 * (1 + r ^ 2))⁻¹)
      (fun r _ => ?_) (fun r hr => mul_nonneg (le_of_lt hr) (by positivity)) ?_
    · have : (2 * (1 + r ^ 2)) ≠ 0 := by positivity
      refine HasDerivAt.congr_deriv
        ((((hasDerivAt_pow 2 r).const_add 1).const_mul 2).inv this).neg ?_
      field_simp
      simp
    · rw [← neg_zero]
      exact (tendsto_inv_atTop_zero.comp (Tendsto.const_mul_atTop two_pos
        (tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop two_ne_zero)))).neg
  simp only [hu]
  rw [h, hd, Measure.real, AnReadModel.volume_ball_one, ENNReal.toReal_ofReal Real.pi_pos.le]
  simp only [smul_eq_mul, Nat.reduceSub, pow_one, mul_left_comm _ (1 / Real.pi), integral_const_mul, hr]
  have := Real.pi_pos
  field_simp
  norm_num

def fsLine (σ : k →+* ℂ) : Weight (CanonLB.affStr k 1) σ (LB.triv _) :=
  Weight.ofFun fun z => Real.log (u ((std σ 1).e z))

theorem isCInf_fsLine : (fsLine σ).IsCInf := Weight.isCInf_ofFun fun y => by
  refine cInfAt_of_chart isOpen_univ (std σ 1) ?_ trivial trivial
  have hc : ContDiff ℝ ∞ u := contDiff_const.add (((Complex.reCLM.comp crd).contDiff.pow 2).add
    ((Complex.imCLM.comp crd).contDiff.pow 2))
  exact (hc.log fun v => (u_pos v).ne').contDiffOn.congr fun v _ =>
    congrArg (fun w => Real.log (u w)) ((std σ 1).e.right_inv trivial)

theorem chernDens_fsLine (v : V 1) : (std σ 1).chernDens (fsLine σ) ((std σ 1).e.symm v) =
    1 / Real.pi * (u v ^ 2)⁻¹ := by
  have e : (fun w => ((fsLine σ).φ (pick (fsLine σ).isLB ((std σ 1).e.symm v))
      ((std σ 1).e.symm w) : ℂ)) = fun w => (Real.log (u w) : ℂ) := funext fun w =>
    congrArg (fun w => (Real.log (u w) : ℂ)) ((std σ 1).e.right_inv trivial)
  rw [AlgChart.chernDens, AlgChart.hess, e, (std σ 1).e.right_inv trivial, Matrix.det_unique]
  erw [cHess_log]
  rw [Complex.ofReal_re]
  simp

theorem chernInt_fsLine : (fsLine σ).ChernIntegrableOn 1 univ (fun _ => 1) ∧
    (fsLine σ).chernInt 1 univ (fun _ => 1) = 1 := by
  have : Smooth (CanonLB.affStr k 1) := SmoothOfRelativeDimension.smooth 1 _
  have : QuasiCompact (CanonLB.affStr k 1) := inferInstance
  have him : (std σ 1).e '' univ = univ := (std σ 1).e.image_source_eq_target
  have hn (v : V 1) : 0 ≤ 1 / Real.pi * (u v ^ 2)⁻¹ := by have := Real.pi_pos; positivity
  have h₁ : (fsLine σ).chernPart 1 1 univ = 1 := by
    rw [Weight.chernPart_apply isCInf_fsLine 1 (std σ 1) .univ fun _ _ => trivial, him]
    simp only [chernDens_fsLine, Units.val_one, Int.cast_one, one_mul, Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.of_integral_ne_zero
      (integral_dens.trans_ne one_ne_zero)) (.of_forall hn), integral_dens, ENNReal.ofReal_one]
  have h₂ : (fsLine σ).chernPart 1 (-1) = 0 := by
    rw [← Measure.measure_univ_eq_zero,
      Weight.chernPart_apply isCInf_fsLine (-1) (std σ 1) .univ fun _ _ => trivial, him]
    refine setLIntegral_eq_zero .univ fun v _ => ENNReal.ofReal_eq_zero.2 ?_
    rw [chernDens_fsLine]
    simpa using hn v
  have : IsProbabilityMeasure ((fsLine σ).chernPart 1 1) := ⟨h₁⟩
  refine ⟨⟨integrableOn_univ.2 (integrable_const _), h₂ ▸ integrableOn_univ.2 (integrable_const _)⟩, ?_⟩
  simp [Weight.chernInt, h₂]

theorem not_isArithVar_zmod (n : ℕ) [NeZero n] {X : Scheme.{0}} (p : X ⟶ Sp (ZMod n)) (D : ℕ) :
    ¬ IsArithVar p D := fun h =>
  have := h.charZero_base
  NeZero.ne n (Nat.cast_eq_zero.1 (ZMod.natCast_self n))

theorem not_isArithVar_rat {X : Scheme.{0}} (p : X ⟶ Sp ℚ) (D : ℕ) : ¬ IsArithVar p D := fun h =>
  have := h.finite
  Int.not_isField ((Algebra.IsIntegral.isField_iff_isField (R := ℤ) (S := ℚ)
    Int.cast_injective).2 (Field.toIsField ℚ))

def trivShift (k : Type) [CommRing k] (t : ℝ) : HermLB (𝟙 (Sp k)) :=
  (HermLB.triv _).shift (fun _ => t) fun _ => rfl

theorem selfInter_trivShift [IsDomain k] [CharZero k] [Module.Finite ℤ k] (hd : ringKrullDim k = 1)
    {t a : ℝ} (h : (trivShift k t).IsSelfInter a) : a = t * Nat.card (k →+* ℂ) := by
  obtain ⟨f, hf, rfl⟩ := h
  have hX := ArithBase.isArithVar_id hd
  have := hX.isLocallyNoetherian
  have := hX.finite_emb
  let i := 𝟙 (Sp k)
  have hr : IsRatSec ((trivShift k t).restr i).B fun _ => 1 := fun a b h => by
    obtain rfl : a = b := Subsingleton.elim (α := PUnit → PUnit) _ _
    have := congrArg (fun u : Γ(Sp k, _)ˣ => fnOf _ h.1 u.val)
      (((trivShift k t).restr i).isLB.g_self a)
    rw [Units.val_one, map_one] at this
    exact (this.symm.trans (fnOf_resG _ h.1 _)).trans (mul_one _).symm
  have h₁ (z : Sp k) : (((trivShift k t).restr i).div hr).mult z = 0 :=
    have ⟨a, ha⟩ := exists_chart ((trivShift k t).restr i).isLB z
    ((presents_divOfRatSec _ hr).isEqn a z ha).mult_eq.trans (unitAt_one z).ord_eq_zero
  have h₂ (σ) (y : CxPts (i ≫ 𝟙 _) σ) :
      logNorm (((trivShift k t).restr i).φ σ) (fun _ => 1) y = -t := by
    have e := ratVal_fnOf (y := y) mem_ptsIn_top trivial 1
    rw [map_one, ev_one mem_ptsIn_top] at e
    have e' : _ = 0 + 2 * t := ((trivShift k t).φ σ).pull_φ i rfl
      (pick (((trivShift k t).restr i).φ σ).isLB y) y
    rw [logNorm, Units.val_one, e]
    exact (congrArg (_ - · / 2) e').trans (by simp)
  have h₃ (σ : k →+* ℂ) : ∑ᶠ _ : CxPts (i ≫ 𝟙 _) σ, -t = -t :=
    finsum_eq_single _ ⟨spMap σ, by simp [i]⟩ fun y hy =>
      absurd (Subtype.ext (by simpa [i] using y.2)) hy
  refine (hf.point _ i hX.charZero hX.dim_eq _ hr).trans ?_
  have := Fintype.ofFinite (k →+* ℂ)
  simp [HermLB.curveDeg, h₁, h₂, h₃, finsum_eq_sum_of_fintype, mul_comm]

theorem isNef_trivShift_iff (t : ℝ) : (ArithBase.trivShift t).IsNef 0 ↔ 0 ≤ t := by
  rw [(ArithBase.isArithHeight_trivShift t).isNef_iff ArithBase.isArithVar_int]
  refine ⟨fun h => ?_, fun ht => ⟨(HermLB.isNef_triv _ 0).semiPos.shift _ _, fun Z i _ _ _ => ?_⟩⟩
  · refine (h.2 _ (𝟙 _) ArithBase.isArithVar_int.dim_eq).trans_eq (if_pos (Ideal.ext fun n => ?_))
    exact (ArithBase.mem_asIdeal_iff (𝟙 (Sp ℤ)) n).trans
      (have := ArithBase.isArithVar_int.charZero; Int.cast_eq_zero)
  · split_ifs
    · exact ht
    · exact Real.log_natCast_nonneg _

theorem mem_smallSec_trivShift (t : ℝ) (s : (trivShift k t).B.Sec) :
    s ∈ (trivShift k t).smallSec ↔
      ∀ σ (y : CxPts (𝟙 (Sp k)) σ), ‖ev _ σ ⊤ (s.f PUnit.unit) y‖ ≤ Real.exp t := by
  refine forall₂_congr fun σ y => ?_
  change ‖ev _ σ ⊤ (s.f PUnit.unit) y‖ ^ 2 * Real.exp (-(0 + 2 * t)) ≤ 1 ↔ _
  rw [zero_add, Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _), one_mul, two_mul, Real.exp_add, ← sq,
    sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le]

end GlobalTheory.ArithHeightModel
