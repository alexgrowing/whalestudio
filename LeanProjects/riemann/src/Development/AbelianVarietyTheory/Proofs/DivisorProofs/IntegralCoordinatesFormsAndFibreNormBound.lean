import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylTensorEvaluationTranslateKronecker
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulNormDualWeylTensorEvaluationLeFibreNormStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MetricDataUnique
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MetricChangeOfFrame
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsMetricConjugateFramedPoint
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CuspFormBoundedBySupNormAtGoodEmbeddingAllEmbedd
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.PointwiseNormSectionEqFlagDomainNorm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RecordAtOfIsArcFr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceBoundSplitOfIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SupAtUnit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain

noncomputable section

namespace GlobalTheory.DefPt.IntNorm

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

open GlobalTheory.Frames GlobalTheory.LamT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_bc {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (y : FrPt Xo c S) : ∃ z, FrMap φ y z :=
  GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c S T φ y

theorem metric_of_archFr {y₀ : FrPt Xo c c.F} {σ : c.F →+* ℂ} {N : ℝ} {X : Mats Dw ℂ} (h : ArchFr y₀ σ N X)
    {z y : FrPt Xo c (CAt σ)} (hz : FrMap (Algebra.ofId c.F (CAt σ)) y₀ z) {Y Gr : Mats Dw ℂ} {s : ℂ} {M : ℝ}
    (hy : FrChg (S := CAt σ) (fun τ => (Y τ)ᵀ) s z y) (hm : IsMetric y M Gr) :
    M = ‖s‖ ^ 2 * N ∧ ∀ τ, ∃ W : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ, Y τ = X τ * W ∧ Wᴴ * W = Gr τ := by
  obtain ⟨y₁, hy₁, -⟩ := existsUnique_frChg E H Dw l Xo c (CAt σ) z (fun τ => (X τ)ᵀ) 1 fun τ => by
    have : IsUnit ((X τ)ᵀ).det := by rw [Matrix.det_transpose]; exact (h.2.1 τ).isUnit
    exact this
  have hm₁ := h.2.2 z y₁ hz hy₁
  obtain ⟨g, a, -, hg⟩ := (frChg_exists_unique E H Dw l Xo c (CAt σ) y₁ y).1 (hy.1.trans hy₁.1.symm)
  obtain ⟨e1, e2⟩ := (frChg_exists_unique E H Dw l Xo c (CAt σ) z y).2 _ _ _ _ hy
    ((frChg_refl_and_comp E H Dw l Xo c (CAt σ) z y₁ y).2 _ _ _ _ hy₁ hg)
  have hm₂ := GlobalTheory.MetricChange.isMetric_frChg E H Dw l Xo c σ y₁ y N _
    (fun b => Matrix.transpose (show Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ from g b))
    (show ℂ from (a : CAt σ)) (Units.ne_zero (M₀ := ℂ) a) hg hm₁
  obtain ⟨hN, hG⟩ := GlobalTheory.LamT.MetUniq.isMetric_unique E H Dw l Xo c σ y _ _ _ _ hm hm₂
  have e3 : s = (show ℂ from (a : CAt σ)) := e2.trans (mul_one _)
  refine ⟨by rw [hN, e3], fun τ => ⟨Matrix.transpose (show Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ from g τ), ?_, ?_⟩⟩
  · have e4 : (Y τ)ᵀ = (show Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ from g τ) * (X τ)ᵀ := congrFun e1 τ
    rw [← Matrix.transpose_transpose (Y τ), e4, Matrix.transpose_mul, Matrix.transpose_transpose]
  · rw [congrFun hG τ, Matrix.mul_one]

theorem isMetric_conj_one {σ : c.F →+* ℂ} {y : FrPt Xo c (CAt σ)} {y' : FrPt Xo c (CAt ((starRingEnd ℂ).comp σ))} {N : ℝ}
    (hpq : 1 ≤ Dw.p + Dw.q) (h : FrMap (GlobalTheory.FrameNorm.conjAlg σ) y y') (hm : IsMetric y N fun _ => 1) :
    IsMetric y' N fun _ => 1 := by
  have hm' := GlobalTheory.LamT.isMetric_conj E H Dw l Xo c σ y y' N (fun _ => 1) hpq h hm
  have h1 : (fun b : E →+* ℂ => ((1 : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)).map (starRingEnd ℂ)) =
      fun _ => 1 := funext fun b => Matrix.map_one _ (map_zero _) (map_one _)
  rwa [h1] at hm'

theorem archFr_conj (hpq : 1 ≤ Dw.p + Dw.q) {y₀ : FrPt Xo c c.F} {σ : c.F →+* ℂ} {N N' : ℝ} {X X' : Mats Dw ℂ}
    (h : ArchFr y₀ σ N X) (h' : ArchFr y₀ ((starRingEnd ℂ).comp σ) N' X') :
    N' = N ∧ ∀ τ, ‖(X' τ).det‖ = ‖(X τ).det‖ := by
  obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F (CAt σ)) y₀
  obtain ⟨y, hy, -⟩ := existsUnique_frChg E H Dw l Xo c (CAt σ) z (fun τ => (X τ)ᵀ) 1 fun τ => by
    have : IsUnit ((X τ)ᵀ).det := by rw [Matrix.det_transpose]; exact (h.2.1 τ).isUnit
    exact this
  have hm := h.2.2 z y hz hy
  obtain ⟨z', hz'⟩ := exists_bc (GlobalTheory.FrameNorm.conjAlg σ) z
  obtain ⟨y', hy'⟩ := exists_bc (GlobalTheory.FrameNorm.conjAlg σ) y
  have h0 := ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans _ _ hz hz'
  rw [Subsingleton.elim ((GlobalTheory.FrameNorm.conjAlg σ).comp _) (Algebra.ofId _ _)] at h0
  have hc := (ChgBC.frChg_baseChange E H Dw l Xo c _ _ (GlobalTheory.FrameNorm.conjAlg σ) z y z' y' _ _ hy hz').1 hy'
  obtain ⟨hN, hW⟩ := metric_of_archFr h' h0 (Y := fun τ => (X τ).map (starRingEnd ℂ)) hc (isMetric_conj_one hpq hy' hm)
  refine ⟨?_, fun τ => ?_⟩
  · rw [hN]
    have : (GlobalTheory.FrameNorm.conjAlg σ) ((1 : (CAt σ)ˣ) : CAt σ) = 1 := map_one _
    rw [this]
    exact (show ‖(1 : ℂ)‖ ^ 2 * N' = N' by simp).symm
  · obtain ⟨W, h1, h2⟩ := hW τ
    have h3 : ‖W.det‖ = 1 := by
      have h4 := congrArg (fun M => ‖Matrix.det M‖) h2
      simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star, Matrix.det_one, norm_one] at h4
      nlinarith [norm_nonneg W.det]
    have h5 := congrArg (fun M => ‖Matrix.det M‖) h1
    simp only [Matrix.det_mul, norm_mul, h3, mul_one] at h5
    rw [← h5, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Complex.norm_conj]

theorem mem_range_of_le_one {w : HeightOneSpectrum (𝓞 c.F)} {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ}
    (ho : OverLa w T.V io e) {b : c.F} (hb : w.valuation c.F b ≤ 1) : io b ∈ Set.range (algebraMap T.V T.Fr) := by
  by_cases h0 : b = 0
  · exact ⟨0, by simp [h0]⟩
  refine GlobalTheory.ArcQ.RecFr.mem_of_vV_nonneg ?_
  rw [ho.2]
  refine mul_nonneg (Nat.cast_nonneg _) ?_
  have := (WithZero.log_le_log ((Valuation.ne_zero_iff _).2 h0) one_ne_zero).2 hb
  simp only [WithZero.log_one] at this
  simp only [vLa]
  omega

theorem map_tval {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ} (la : ∀ t, Fin (N t) → ℕ) {S S' : Type} [CommRing S]
    [CommRing S'] (φ : S →+* S') (x : TIdx la → S) (y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) S) :
    φ (tval la x y) = tval la (fun I => φ (x I)) fun t => (y t).map φ := by
  simp only [tval, map_sum, map_mul, map_prod]
  refine Finset.sum_congr rfl fun I _ => congrArg _ (Finset.prod_congr rfl fun t _ => ?_)
  generalize intVec (la t) (I t) = p
  induction p using MvPolynomial.induction_on with
  | C a => simp [GlobalTheory.DualWeyl.evalAt]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    simp [GlobalTheory.DualWeyl.evalAt]

theorem val_nonneg {Z : Comp Xo c} (P : PtData Z) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {x : TIdx (part Dw a) → c.F} {f : Rul Xo c}
    (hr : Reads Z P.y₀ a n x f) (hx : x ∈ locLat (P.matA a n)) (w : HeightOneSpectrum (𝓞 c.F)) :
    ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v f := by
  intro v hv
  rcases mem_valOn_or (Z := Z) hv with h | h
  swap
  · rw [h f hr.1]; exact le_top
  obtain ⟨⟨q, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩ := h
  letI := io.toAlgebra
  show 0 ≤ nval T.V e (evR Xo c f y.1)
  obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F T.Fr) P.y₀
  obtain ⟨ha, hB, hl⟩ := P.loc w
  obtain ⟨Y, u, hY, hc⟩ := hl T io e ho y.1 z y.2.2 hz ((P.only _ y.1 hy.2).trans hz.1.symm)
  have hev := hr.2 T.Fr z y.1 (fun τ => (P.B w τ).map io * (Y τ).map (algebraMap T.V T.Fr)) _ (fun τ => by
      rw [Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det]
      exact ((hB τ).isUnit.map io).mul ((hY τ).map _))
    ((ha.isUnit.map io).mul (u.isUnit.map _)) hz hc
  have hmv := GlobalTheory.DefPt.tval_translate _ _ (part Dw a) c.F T.Fr io x (P.B w) fun τ => (Y τ).map (algebraMap T.V T.Fr)
  choose x' hx' using fun I => mem_range_of_le_one ho (hx w I)
  refine ReciprocityTheory.ChartRestriction.G.PullbackSections.nval_nonneg_of_int e ⟨(u : T.V) ^ n * tval (part Dw a) x' Y, ?_⟩
  rw [hev, map_mul, map_tval, map_pow]
  erw [hmv]
  simp only [hx', PtData.matA, fibA, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, map_pow, tval,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun I _ => by ring

theorem cabs_le_matNorm {Z : Comp Xo c} (P : PtData Z) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hd : Dom a n)
    {x : TIdx (part Dw a) → c.F} {f : Rul Xo c} (hr : Reads Z P.y₀ a n x f) {σ : c.F →+* ℂ} {y : FrPt Xo c (CAt σ)}
    (hy : y.x = spMap (algebraMap c.F (CAt σ)) ≫ P.y₀.x) (hm : IsMetric y 1 fun _ => 1) :
    cabs (evR Xo c f y) ≤ matNorm (P.matY a n) σ x := by
  obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F (CAt σ)) P.y₀
  obtain ⟨g, s, hg, hc⟩ := (frChg_exists_unique E H Dw l Xo c (CAt σ) z y).1 (hy.trans hz.1.symm)
  have hev := hr.2 (CAt σ) z y (fun τ => (g τ)ᵀ) s (fun τ => by rw [Matrix.det_transpose]; exact hg τ) s.isUnit hz hc
  obtain ⟨hN, hW⟩ := metric_of_archFr (P.arch σ) hz
    (Y := fun τ => Matrix.transpose (show Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ from g τ)) hc hm
  choose W hW1 hW2 using hW
  have hs : cabs (s : CAt σ) = (Real.sqrt (P.N σ))⁻¹ := by
    rw [← Real.sqrt_inv, ← eq_inv_of_mul_eq_one_left hN.symm]
    exact (Real.sqrt_sq (norm_nonneg (show ℂ from (s : CAt σ)))).symm
  have hb := GlobalTheory.T.mul_norm_dualWeylTensorEvaluation_le_fibreNorm _ _ (part Dw a) (fun τ i j hij => hd.1 τ hij) (fun I => σ (x I)) (P.X σ)
    (fun τ => ⟨W τ, Matrix.mem_unitaryGroup_iff'.2 (hW2 τ)⟩) ((Real.sqrt (P.N σ))⁻¹ ^ n) (by positivity)
  refine le_trans (le_of_eq ?_) hb
  have e : (fun τ => P.X σ τ * W τ) =
      fun τ => Matrix.transpose (show Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ from g τ) :=
    funext fun τ => (hW1 τ).symm
  rw [hev, GlobalTheory.FrameNorm.Comparison₂.cabs_mul, ← hs, e]
  congr 1
  exact norm_pow (α := ℂ) _ _

theorem cabs_le_matNorm_conj (hpq : 1 ≤ Dw.p + Dw.q) {Z : Comp Xo c} (P : PtData Z) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    (hd : Dom a n) {x : TIdx (part Dw a) → c.F} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) (hr : Reads Z P.y₀ a n x f)
    {σ σ' : c.F →+* ℂ} (hσ : σ' = (starRingEnd ℂ).comp σ) {y : FrPt Xo c (CAt σ)}
    (hy : y.x = spMap (algebraMap c.F (CAt σ)) ≫ P.y₀.x) (hm : IsMetric y 1 fun _ => 1) :
    cabs (evR Xo c f y) ≤ matNorm (P.matY a n) σ' x := by
  subst hσ
  have hB : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨y', hy'⟩ := exists_bc (GlobalTheory.FrameNorm.conjAlg σ) y
  have hx : y'.x = spMap (algebraMap c.F (CAt ((starRingEnd ℂ).comp σ))) ≫ P.y₀.x := by
    rw [hy'.1, hy, ← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp]
    rfl
  have hb := cabs_le_matNorm P hd hr hx (isMetric_conj_one hpq hy' hm)
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  have hev := evR_frMap (GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c).2.2.1 f hf.1
    (GlobalTheory.FrameNorm.conjAlg σ) y (GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c (CAt σ) y) y' hy'
  rw [hev] at hb
  refine le_trans (le_of_eq ?_) hb
  exact (Complex.norm_conj _).symm

theorem exists_ortho {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {ξ : ℝ} (hσ : GoodEmb c σ) (hU : IsUnf U)
    (hξ : ∀ k (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = ξ) (hpq : 1 ≤ Dw.p + Dw.q) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hd : Dom a n)
    {f : Rul Xo c} (hf : f ∈ sec Xo c a n) (k : U.Comp) (x : (U.X k).dom) :
    ∃ y : FrPt Xo c (CAt σ), y.x = (U.un k x).x ∧ IsMetric y 1 (fun _ => 1) ∧
      homN U ξ (wtZ a n) f ⟨k, x.1⟩ = cabs (evR Xo c f y) := by
  have hB : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  obtain ⟨-, -, -, -, -, -, hwt⟩ := GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c
  have hsec := hU.2.2.2.2.1 a n hd f hf k
  have hb := FrameDegreeData.bOf_mem (U.X k) x.2
  have hz := OrthogonalFrameDomain.rmul_mem_dom (U.X k) x.2 hb
  have ho := FrameDegreeData.ortho_bOf (U.X k) x.2
  have hp := FrameDegreeData.pnorm_rmul (U.X k) _ _ hsec.2.1 x.1 x.2 _ hb
  obtain ⟨t₀, ht₀⟩ := (hU.2.2.2.1 k k x ⟨_, hz⟩).2 ⟨1, one_mem _, _, hb, by
    have : lact (1 : GL (Fin r) E) x.1 = x.1 := by
      funext τ
      simp only [lact, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
      rfl
    rw [this]⟩
  obtain ⟨g₀, -, -, hg₀⟩ := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) _ _ (U.un k x)).1 t₀).1 ht₀
  have hx₀ := hg₀.1
  clear hg₀ ht₀
  generalize rmul x.1 (FrameDegreeData.bOf (U.X k) x.1) = z at hz ho hp hx₀
  have hξ0 : 0 < ξ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    rw [← hξ k τ]
    exact norm_pos_iff.2 ((map_ne_zero τ).2 (U.X k).ξ0_ne)
  have hκ : 0 < 2 * Real.pi * ξ := by positivity
  have hm0 := GlobalTheory.OrthoMetric.isMetric_of_isOrtho E H Dw l Xo c σ r U ξ hσ hU hpq k ⟨z, hz⟩ (hξ k) ho
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (Real.sqrt (2 * Real.pi * ξ))⁻¹ := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hρκ : ρ * (2 * Real.pi * ξ) * ρ = 1 := by
    have := Real.mul_self_sqrt hκ.le
    have h2 := Real.sqrt_pos.2 hκ
    rw [hρ]
    generalize Real.sqrt (2 * Real.pi * ξ) = q at this h2
    rw [← this]
    field_simp
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
  let Y : Mats Dw ℂ := fun _ => (ρ : ℂ) • 1
  obtain ⟨y, hy, -⟩ := existsUnique_frChg E H Dw l Xo c (CAt σ) (U.un k ⟨z, hz⟩) (fun τ => (Y τ)ᵀ) 1 fun τ => by
    have : IsUnit ((Y τ)ᵀ).det := by simp [Y, hρc]
    exact this
  have hm1 := GlobalTheory.MetricChange.isMetric_frChg E H Dw l Xo c σ _ y 1 _ Y 1 one_ne_zero hy hm0
  have hG : (fun b => (Y b)ᴴ * (((2 * Real.pi * ξ : ℝ) : ℂ) • (1 : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)) * Y b) =
      fun _ => 1 := by
    funext b
    have h3 : (ρ : ℂ) * ((2 * Real.pi * ξ : ℝ) : ℂ) * ρ = 1 := by exact_mod_cast hρκ
    simp only [Y, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one,
      smul_smul, Complex.star_def, Complex.conj_ofReal]
    rw [← mul_assoc, h3, one_smul]
  rw [hG, norm_one, one_pow, mul_one] at hm1
  refine ⟨y, hy.1.trans hx₀, hm1, ?_⟩
  let t : Formalism.L2.Pj.Ix Dw → (CAt σ)ˣ := fun i => i.elim 1 fun _ => Units.mk0 (G₀ := ℂ) ρ hρc
  have ht : FrBor t (U.un k ⟨z, hz⟩) y := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c (CAt σ) _ y y).1 t).2
    ⟨_, fun τ i j hij => show (Y τ)ᵀ i j = 0 by simp [Y, hij.ne'], fun τ i => show (Y τ)ᵀ i i = (ρ : ℂ) by simp [Y], hy⟩
  have hev := hwt (CAt σ) (GlobalTheory.FrameNorm.Comparison₂.isReduced_cAt σ) a n f hf t _ _ ht
  have hlie : ∏ p : Σ τ : E →+* ℂ, Fin (Dw.mult τ), ρ ^ a (p.1, p.2) = lieFac Dw ξ a := by
    have hs : ρ = Real.exp (-(1 / 2) * Real.log (2 * Real.pi * ξ)) := by
      rw [hρ, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hκ, ← Real.exp_neg]
      congr 1; ring
    simp only [hs, ← Real.exp_nat_mul]
    rw [← Real.exp_sum, lieFac, ← Finset.sum_mul]
    congr 1
    rw [Fintype.sum_sigma]
    ring
  have hw : cabs (wchar (ex Dw a n) t) = lieFac Dw ξ a := by
    have h1 : cabs (t none : CAt σ) = 1 := norm_one (α := ℂ)
    rw [GlobalTheory.FrameNorm.Comparison₂.cabs_wchar, Fintype.prod_option, h1, one_pow, one_mul, ← hlie]
    refine Finset.prod_congr rfl fun p _ => ?_
    have h2 : cabs (t (some p) : CAt σ) = ρ := show ‖(ρ : ℂ)‖ = ρ by rw [Complex.norm_real, Real.norm_of_nonneg hρ0.le]
    rw [h2]
    rfl
  have hrd : ‖rdU U f k z‖ = cabs (evR Xo c f (U.un k ⟨z, hz⟩)) := by
    have e : rdU U f k z = toC (evR Xo c f (U.un k ⟨z, hz⟩)) := dif_pos hz
    rw [e]; rfl
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.pnorm_unit _ _ _ (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho _ ho), hrd] at hp
  rw [hev, GlobalTheory.FrameNorm.Comparison₂.cabs_mul, hw, homN, lieFacZ_wtZ, modelWt_wtZ, hp]
  rfl

theorem integral_and_norm_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), DefCase U ξ → Dom a n → ∀ (Z : Comp Xo c) (P : PtData Z), (∀ σ, P.N ((starRingEnd ℂ).comp σ) = P.N σ ∧ ∀ τ, ‖(P.X ((starRingEnd ℂ).comp σ) τ).det‖ = ‖(P.X σ τ).det‖) ∧ ∀ (x : TIdx (part Dw a) → c.F) (f : Rul Xo c), f ∈ sec Xo c a n → Reads Z P.y₀ a n x f → (x ∈ locLat (P.matA a n) → ∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v f) ∧ ∀ σ, ∀ z ∈ framesOn (U (goodOf c σ)) Z, homN (U (goodOf c σ)) ξ (wtZ a n) f z ≤ matNorm (P.matY a n) σ x := by
  intro E _ _ _ H Dw l Xo c r U ξ a n hD hd Z P
  have hpq : 1 ≤ Dw.p + Dw.q := hD.p.trans (Nat.le_add_right _ _)
  refine ⟨fun σ => archFr_conj hpq (P.arch σ) (P.arch _), fun x f hf hr => ⟨val_nonneg P hr, fun σ z hz => ?_⟩⟩
  obtain ⟨h, hZ⟩ := hz
  have hg := goodEmb_goodOf c σ
  obtain ⟨y, hy, hm, hn⟩ := exists_ortho hg (hD.unf _ hg) (hD.xi _ hg) hpq hd hf z.1 ⟨z.2, h⟩
  have hx := hy.trans (P.only _ _ hZ)
  refine le_trans (le_of_eq hn) ?_
  clear hn hy hZ
  by_cases hσ : GoodEmb c σ
  · have e : goodOf c σ = σ := if_pos hσ
    have := cabs_le_matNorm P hd hr hx hm
    exact this.trans (le_of_eq (by rw [e]))
  · have e : goodOf c σ = (starRingEnd ℂ).comp σ := if_neg hσ
    exact cabs_le_matNorm_conj hpq P hd hf hr (by rw [e]; ext b; simp) hx hm

end GlobalTheory.DefPt.IntNorm

end
