import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteAndFinrankLeOfPointwise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedFrameSumPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWeightSpreadLeExponentNormAddStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspSquareIntegrableIffUnfolded
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevGeo.RankBd

theorem supConst_nonneg (E : Type) [Field E] [NumberField E] (r d M : ℕ) (w : ℝ) : 0 ≤ supConst E r d M w := by
  unfold supConst locConst massLev GlobalTheory.UCls.massBd multBd
  have h1 : 0 ≤ rdE E := Real.rpow_nonneg (abs_nonneg _) _
  have h2 : Even (2 * fdeg E * r ^ 2) := by rw [mul_assoc]; exact even_two_mul _
  refine mul_nonneg (mul_nonneg (div_nonneg (by positivity) (pow_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg _)) _))
    (h2.pow_nonneg _)) ?_
  have := Real.rpow_nonneg h1 ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2)
  positivity

variable {D : D7} {r : ℕ} {Comp : Type} [Fintype Comp] {X : Comp → Data D.host.E r}

theorem pnorm_fac_pos (Y : Data D.host.E r) (la : Wt Y.Ψ r) {x : Frame Y.Ψ r} (hx : x ∈ Y.dom) :
    0 < ∏ τ, ∏ i : Fin r, ‖dmin Y.Gm x τ i.succ / dmin Y.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) := by
  have hne : ∀ τ i, dmin Y.Gm x τ i ≠ 0 := fun τ i h => by
    have := (hx τ).2 i
    rw [h] at this
    simp at this
  refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
  exact norm_pos_iff.2 (div_ne_zero (hne τ _) (hne τ _))

theorem eLpNorm_sq_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hm : AEStronglyMeasurable f μ) {B : ℝ} (hB : ∀ x, f x ≤ B) :
    eLpNorm f 2 μ ^ 2 = ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) := by
  have hint : Integrable (fun x => f x ^ 2) μ :=
    Integrable.of_bound (hm.pow 2) (B ^ 2) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (hf0 x) (hB x) 2)
  rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => by positivity),
    eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal (hf0 x), ← ENNReal.ofReal_pow (hf0 x)]

open scoped TensorProduct

open scoped TensorProduct

variable {D : D7} {r : ℕ} {Comp : Type} [Fintype Comp] {X : Comp → Data D.host.E r}

theorem finrank_le_of_sup (V : HSp D) (dict : GA D V → Σ k, Frame (X k).Ψ r) (la : ∀ k, Wt (X k).Ψ r)
    {Kf : Subgroup (GA D V)} {th : ∀ k, (X k).Ψ → (GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {hr : V.rank = r} {N : ℕ} (hN : 0 < N) (hth : ∀ k τ, StandardLattice.IsInfEmb τ.1 (th k τ))
    (hd : DictIsUnif V dict Kf th hr) (hK : IsLevelK V N Kf)
    (hu : ∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1)
    (S : Submodule ℂ (FDSec X))
    (hS : ∀ P ∈ S, P ∈ holSub X la ∧ (∀ k, ContinuousOn (P k) (X k).dom) ∧
      (∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (lact γ x) = P k x) ∧ (∀ k x, x ∉ (X k).dom → P k x = 0))
    {C : ℝ} (hC : 0 ≤ C)
    (hsup : ∀ P ∈ S, supE X la P ^ 2 ≤ ENNReal.ofReal C * petE V dict (muQ1 V) la P ^ 2) :
    FiniteDimensional ℂ S ∧ (Module.finrank ℂ S : ℝ) ≤ C := by

  have hpt : ∀ (P : FDSec X) (g : GA D V), ptN la P (dict g) = ‖P (dict g).1 (dict g).2‖ := fun P g =>
    pnorm_eq_of_unit _ _ _ _ (hu g)
  have hdom : ∀ g, (dict g).2 ∈ (X (dict g).1).dom := hd.2.2.2.1
  have hle : ∀ (P : FDSec X) (g : GA D V), ENNReal.ofReal ‖P (dict g).1 (dict g).2‖ ≤ supE X la P := fun P g => by
    rw [← hpt]
    exact le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)) ⟨(dict g).1, ⟨_, hdom g⟩⟩
  have hmeas : ∀ P ∈ S, AEStronglyMeasurable (fun q : AutQ V => ‖P (dict q.out).1 (dict q.out).2‖) (muQ1 V) := by
    intro P hP
    obtain ⟨-, hc, hΓ, -⟩ := hS P hP
    have hmu : MuUnit V dict (fun _ => 1) := ⟨fun _ _ => (mul_one 1).symm, fun _ => norm_one, fun _ _ => rfl, hu⟩
    have h := GlobalTheory.PeterssonCompare.measurable_onQ_adel V hN hth hd hK hmu continuous_const P hc hΓ
    have e : (fun q : AutQ V => ‖P (dict q.out).1 (dict q.out).2‖) = fun q => ‖onQ V (adel V dict (fun _ => 1) P) q‖ := by
      funext q
      simp [onQ, adel]
    rw [e]
    exact h.norm.aestronglyMeasurable
  have hpet : ∀ P ∈ S, petE V dict (muQ1 V) la P ^ 2 =
      ENNReal.ofReal (∫ q, ‖P (dict q.out).1 (dict q.out).2‖ ^ 2 ∂(muQ1 V)) := by
    intro P hP
    have hfin := supE_ne_top X la (hS P hP).1
    have e : petE V dict (muQ1 V) la P = eLpNorm (fun q : AutQ V => ‖P (dict q.out).1 (dict q.out).2‖) 2 (muQ1 V) := by
      unfold petE
      congr 1
      funext q
      exact hpt P _
    rw [e]
    exact eLpNorm_sq_eq (fun _ => norm_nonneg _) (hmeas P hP) (B := (supE X la P).toReal) fun q =>
      (ENNReal.ofReal_le_iff_le_toReal hfin).1 (hle P _)
  refine GlobalTheory.Bergman.finite_and_finrank_le_of_pointwise (μ := muQ1 V)
    (fun q (P : S) => ‖(P : FDSec X) (dict q.out).1 (dict q.out).2‖)
    (fun q => ⟨(LinearMap.proj (R := ℂ) (φ := fun _ : Frame (X (dict q.out).1).Ψ r => ℂ) (dict q.out).2 ∘ₗ
      LinearMap.proj (R := ℂ) (φ := fun k => Frame (X k).Ψ r → ℂ) (dict q.out).1) ∘ₗ S.subtype, fun P => rfl⟩)
    (fun P => hmeas P P.2) ?_ hC ?_
  · intro P hP0
    have h0 : petE V dict (muQ1 V) la (P : FDSec X) = 0 := by
      have e : (fun q : AutQ V => ptN la (P : FDSec X) (dict q.out)) = fun _ => 0 := by
        funext q
        rw [hpt]
        exact hP0 q
      unfold petE
      rw [e]
      exact eLpNorm_zero
    have hs := hsup P P.2
    rw [h0] at hs
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, nonpos_iff_eq_zero,
      pow_eq_zero_iff] at hs
    obtain ⟨-, -, -, hoff⟩ := hS P P.2
    refine Subtype.ext (funext fun k => funext fun x => ?_)
    by_cases hx : x ∈ (X k).dom
    · have h1 : ENNReal.ofReal ((X k).pnorm (la k) ((P : FDSec X) k) x) ≤ supE X la P :=
        le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) ((P : FDSec X) p.1) p.2)) ⟨k, ⟨x, hx⟩⟩
      rw [hs, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
      have h2 : ‖(P : FDSec X) k x‖ * _ ≤ 0 := h1
      have h3 := pnorm_fac_pos (X k) (la k) hx
      have h4 : ‖(P : FDSec X) k x‖ ≤ 0 := nonpos_of_mul_nonpos_left h2 h3
      simpa using h4
    · simpa using hoff k x hx
  · intro P q
    have h1 := hle (P : FDSec X) q.out
    have h2 := hsup P P.2
    rw [hpet P P.2] at h2
    have h3 : ENNReal.ofReal (‖(P : FDSec X) (dict q.out).1 (dict q.out).2‖ ^ 2) ≤
        ENNReal.ofReal (C * ∫ q, ‖(P : FDSec X) (dict q.out).1 (dict q.out).2‖ ^ 2 ∂(muQ1 V)) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_mul hC]
      exact (pow_le_pow_left' h1 2).trans h2
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (integral_nonneg fun _ => by positivity))).1 h3

open Module

set_option maxHeartbeats 1000000 in

theorem finrank_cuspW_le : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional c.F (cuspW Xo c U (wtZ a n)) ∧ (Module.finrank c.F (cuspW Xo c U (wtZ a n)) : ℝ) ≤ supConst D.host.E D.R.r D.host.d l.M (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1) := by
  intro hM hT D j H Dw l Xo c U dict hL a n hDom
  obtain ⟨σ, hσ⟩ : ∃ σ : c.F →+* ℂ, GoodEmb c σ := ⟨_, goodEmb_goodOf c c.F.val.toRingHom⟩
  obtain ⟨Kf, th, hr, hK, hth, hd, hu⟩ := hL.dictU σ hσ
  have hU : IsUnf (U σ) := hL.unf σ hσ
  obtain ⟨w, hw_def⟩ : ∃ w : ℝ, w = ((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1 := ⟨_, rfl⟩
  rw [← hw_def]
  have hw : 0 < w := by rw [hw_def]; positivity
  have hspread : ∀ k, (∑ τ, ((U σ).X k).spread (laU (U σ) a n k) τ) ≤ w := fun k =>
    (GlobalTheory.T.sum_weightSpread_le_exponentNorm_add D j H Dw l Xo c U dict hL σ hσ a n k).trans (by rw [hw_def]; linarith)
  have hχ := hL.chiTriv σ hσ a n hDom
  have hsup := GlobalTheory.T.weighted_frame_sum_positive hM hT D j H Dw l Xo c U dict hL σ hσ (laU (U σ) a n) w hw hspread hχ
  obtain ⟨Cw, hCw⟩ : ∃ Cw, Cw = cuspW Xo c U (wtZ a n) := ⟨_, rfl⟩
  rw [← hCw]
  have hsecOf : ∀ f ∈ Cw, f ∈ sec Xo c a n := fun f hf => by
    rw [hCw, cuspW_wtZ] at hf
    exact cusp_le_sec Xo c U a n hf

  have hgen : ∀ f ∈ Cw, rdU (U σ) f ∈ holSub (U σ).X (laU (U σ) a n) ∧
      (∀ k, ContinuousOn (rdU (U σ) f k) ((U σ).X k).dom) ∧
      (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, rdU (U σ) f k (lact γ x) = rdU (U σ) f k x) ∧
      (∀ k x, x ∉ ((U σ).X k).dom → rdU (U σ) f k x = 0) := by
    intro f hf
    have hs := hU.2.2.2.2.1 a n hDom f (hsecOf f hf)
    refine ⟨?_, fun k => (hs k).1.continuousOn, fun k γ hγ x hx => ?_, fun k x hx => ?_⟩
    · rw [hCw] at hf
      have := (mem_cuspW.1 hf).2 σ hσ
      rwa [modelWt_wtZ] at this
    · rw [(hs k).2.2 γ hγ x hx, hχ k γ hγ, one_mul]
    · classical
      show (if h : x ∈ ((U σ).X k).dom then _ else 0) = 0
      rw [dif_neg hx]
  obtain ⟨S, hS_def⟩ : ∃ S : Submodule ℂ (FDSec (U σ).X), S = Submodule.span ℂ (rdU (U σ) '' (Cw : Set (Rul Xo c))) :=
    ⟨_, rfl⟩
  have hS : ∀ P ∈ S, P ∈ holSub (U σ).X (laU (U σ) a n) ∧ (∀ k, ContinuousOn (P k) ((U σ).X k).dom) ∧
      (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, P k (lact γ x) = P k x) ∧
      (∀ k x, x ∉ ((U σ).X k).dom → P k x = 0) := by
    intro P hP
    rw [hS_def] at hP
    induction hP using Submodule.span_induction with
    | mem P hP =>
      obtain ⟨f, hf, rfl⟩ := hP
      exact hgen f hf
    | zero => exact ⟨Submodule.zero_mem _, fun k => continuousOn_const, fun _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩
    | add P Q _ _ hP hQ =>
      refine ⟨Submodule.add_mem _ hP.1 hQ.1, fun k => (hP.2.1 k).add (hQ.2.1 k), fun k γ hγ x hx => ?_,
        fun k x hx => ?_⟩
      · simp only [Pi.add_apply]
        rw [hP.2.2.1 k γ hγ x hx, hQ.2.2.1 k γ hγ x hx]
      · simp only [Pi.add_apply]
        rw [hP.2.2.2 k x hx, hQ.2.2.2 k x hx, add_zero]
    | smul z P _ hP =>
      refine ⟨Submodule.smul_mem _ z hP.1, fun k => (hP.2.1 k).const_smul z, fun k γ hγ x hx => ?_,
        fun k x hx => ?_⟩
      · simp only [Pi.smul_apply]
        rw [hP.2.2.1 k γ hγ x hx]
      · simp only [Pi.smul_apply]
        rw [hP.2.2.2 k x hx, smul_zero]
  obtain ⟨hSfin, hSle⟩ := finrank_le_of_sup (D.sp.W j) (dict σ) (laU (U σ) a n) (Nat.pos_of_ne_zero (by
      have := l.three_le; omega)) hth hd hK hu S hS (supConst_nonneg _ _ _ _ _) fun P hP => hsup P (hS P hP).1

  have hind : ∀ (m : ℕ) (b : Fin m → Rul Xo c), (∀ i, b i ∈ Cw) → LinearIndependent c.F b →
      LinearIndependent ℂ (fun i => rdU (U σ) (b i)) := fun m b hb hli =>
    (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.lawsFieldsSeparately.2.1 _ H Dw l Xo c σ _
      (Formalism.L2.PjFree.Unf.ofPj (U σ)) ((Formalism.L2.PjFree.isUnf_ofPj _).2 hU) a n).1 m b (fun i => hsecOf _ (hb i)) hli
  have hcard : ∀ s : Finset Cw, LinearIndependent c.F (fun i : s => (i : Cw)) → s.card ≤ finrank ℂ S := by
    intro s hs
    let e : Fin s.card ≃ s := s.equivFin.symm
    let b : Fin s.card → Rul Xo c := fun i => ((e i : Cw) : Rul Xo c)
    have hb : LinearIndependent c.F b :=
      ((hs.comp e e.injective).map' Cw.subtype (Submodule.ker_subtype _))
    have hrd := hind s.card b (fun i => (e i : Cw).2) hb
    let v : Fin s.card → S := fun i => ⟨rdU (U σ) (b i), hS_def ▸ Submodule.subset_span ⟨b i, (e i : Cw).2, rfl⟩⟩
    have hv : LinearIndependent ℂ v := LinearIndependent.of_comp S.subtype hrd
    simpa using hv.fintype_card_le_finrank
  haveI : Module.Free c.F Cw := Module.Free.of_divisionRing c.F Cw
  have hrank : Module.rank c.F Cw ≤ ((finrank ℂ S : ℕ) : Cardinal) := rank_le hcard
  have hfin : FiniteDimensional c.F Cw :=
    Module.rank_lt_aleph0_iff.1 (lt_of_le_of_lt hrank (Cardinal.nat_lt_aleph0 _))
  have h2 : finrank c.F Cw ≤ finrank ℂ S := finrank_le_of_rank_le hrank
  refine ⟨hfin, le_trans ?_ hSle⟩
  exact Nat.cast_le.2 h2

end GlobalTheory.LevGeo.RankBd
