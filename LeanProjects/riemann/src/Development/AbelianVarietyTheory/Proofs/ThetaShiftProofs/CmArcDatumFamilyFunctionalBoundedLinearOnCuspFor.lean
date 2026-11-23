import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridgeAlt
import Formalism.LocalToGlobal.ProjectiveLattices.RecConj
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NormCmArcCoefficientFunctionalLeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmValueLineLengthConjEqStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NdegLineOptionLe
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmArcDatumFunctionalFiniteIntegralityBoundStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumCoefficientFunctionalLinearDegree
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LamDegreeParameters
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ModelsAtOfGoodLevel
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TransvInOfHasPrinc

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM.RunNum

theorem sum_extendByZero_fin_eq_sum_of_eq {p m : ℕ} (f : Fin p → ℕ) (h : m = p) : ∑ i : Fin m, ext0 f i = ∑ i, f i := by
  subst h
  exact Finset.sum_congr rfl fun i _ => by simp [ext0]

theorem conj_rt_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (τ : E →+* ℂ)
    (h : τ (H.rt : E) = H.rt0) : conjEmb τ (H.rt : E) ≠ H.rt0 := by
  intro h'
  have h1 : starRingEnd ℂ H.rt0 = H.rt0 := by
    have h0 : starRingEnd ℂ (τ (H.rt : E)) = H.rt0 := h'
    rwa [h] at h0
  have h2 : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h1
  have h3 := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp [pow_two, h2] at h3
  nlinarith [mul_self_nonneg H.rt0.re]

theorem absA_wtA {D : D7} (T : Core D) (j : ℕ) (hD : IsDatW D j (T.Q.Dw j)) (hH : T.Q.PinHost)
    (w : WeightFamilies.Wt D j) :
    absA (T.Q.Dw j) (wtA w) = ∑ t, ((∑ i, w.aP t i) + ∑ i, w.aM t i) := by
  classical
  simp only [absA, wtA]
  rw [Finset.sum_congr rfl fun σ _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Finset.sum_add_distrib]
  have ht := hH.2.2.2 t
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [Finset.sum_eq_single (DV.tauEmb D t)]
    · simp only [if_true]
      exact sum_extendByZero_fin_eq_sum_of_eq _ (by rw [← hD.1]; simp [Datum.mult, ht])
    · intro b _ hb; simp [hb]
    · simp
  · rw [Finset.sum_eq_single (conjEmb (DV.tauEmb D t))]
    · simp only [if_true]
      exact sum_extendByZero_fin_eq_sum_of_eq _ (by rw [← hD.2.1]; simp [Datum.mult, conj_rt_ne _ _ ht])
    · intro b _ hb; simp [hb]
    · simp

theorem absA_add_le_size {D : D7} (T : Core D) (hp : T.Q.Pins) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) :
    (absA (T.Q.Dw j) (wtA w) : ℝ) + (D.R.f : ℝ) * D.R.r * w.n ≤ w.size := by
  rw [absA_wtA T j (hp.2.2.2 j hj) hp.1 w]
  unfold WeightFamilies.Wt.size
  push_cast
  have h1 : (1 : ℝ) ≤ max ((D.R.sigW j).2 : ℝ) 1 := le_max_right _ _
  have h2 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * w.n := by positivity
  nlinarith

theorem pnorm_le_sup {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type} [Fintype Comp]
    (X : Comp → Data E r) (la) {P : FDSec X} (hP : P ∈ holSub X la) (p : FPt X) :
    (X p.1).pnorm (la p.1) (P p.1) p.2 ≤ Formalism.L2.Pj.supN X la P := by
  unfold Formalism.L2.Pj.supN
  rw [← ENNReal.ofReal_le_iff_le_toReal (supE_ne_top _ _ hP)]
  exact le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)) p

theorem one_le_LaAt (D : D7) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) : 1 ≤ LaAt D j ka CR Tt cc :=
  le_max_left _ _

theorem archimedeanTerm_nonneg (E : Type) [Field E] [NumberField E] {r : ℕ} (hr : 1 ≤ r) {La : ℝ} (hLa : 1 ≤ La) (c₁ : ℝ) :
    0 ≤ archP E r La c₁ := by
  unfold archP
  have h1 : 0 ≤ Real.log (max 1 c₁) := Real.log_nonneg (le_max_left _ _)
  have h2 : 0 ≤ Real.log La := Real.log_nonneg hLa
  have h3 : 0 ≤ Real.log (rdE E) := by
    refine Real.log_nonneg (Real.one_le_rpow ?_ (by positivity))
    unfold dE
    exact_mod_cast Int.one_le_abs (discr_ne_zero E)
  have h4 : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
  linarith

theorem arch_good (hK : Known) {D : D7} {T : Core D} (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ)
    (hG : GlobalTheory.RunIn.GamAt T) (hj : InR D j) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁]
    (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁) (hd : Std d)
    (s : CMIn d.a d.e d.th d.jj (nAt D j ka CR Tt cc) (LaAt D j ka CR Tt cc) (WeightFamilies.c1 D CR Tt cc j))
    (em : K₁ →+* ℂ) (hem : GoodEmb T.Q.c (em.comp (algebraMap T.Q.c.F K₁))) (F : (recB h).Cusp j ka) :
    ‖em (cfOf d.yF d.μ d.jj F.1)‖ * (s.valLine d.μ ka.n).n em ≤
      (recB h).supN j ka (em.comp (algebraMap T.Q.c.F K₁)) F * Real.exp (CarchAt D j ka CR Tt cc) := by
  obtain ⟨-, -, -, -, -, hf, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨-, hr, -⟩ := hnum j hj
  have hFc : F.1 ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA ka) ka.n := cutR_le T.C j ka F.2
  have hS : (recB h).supN j ka (em.comp (algebraMap T.Q.c.F K₁)) F =
      supC (T.Q.Xo j) T.Q.c (T.U j) (xiR D) (em.comp (algebraMap T.Q.c.F K₁)) (wtA ka) ka.n F.1 := by
    change cutN T.C T.Ns j ka _ F = _
    unfold cutN Core.Ns
    rw [if_pos hj, goodOf, if_pos hem]
  have h0 := (recB h).supN_nonneg j ka (em.comp (algebraMap T.Q.c.F K₁)) F
  have hb := GlobalTheory.T.norm_cmArcCoefficientFunctional_le hK _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d _ _ _ s em D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j _)) (xiR D) ((recB h).supN j ka (em.comp (algebraMap T.Q.c.F K₁)) F)
    (wtA ka) ka.n hd (one_le_LaAt D j ka CR Tt cc) hem (h.unf j hj _ hem) (h.xiAbs j hj _ hem) (dom_wtA ka)
    (GlobalTheory.TransvPrinc.transvIn_of_hasPrinc _ _ _ _ _ _ _ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j _)) _ _ (hG j hj _ hem)
      (h.chiTriv j hj _ hem _ _ (dom_wtA ka)))
    F.1 (cusp_le_sec _ _ _ _ _ hFc) h0 (by
      intro k y hy
      rw [hS]
      exact mul_le_mul_of_nonneg_left
        (pnorm_le_sup _ _ (((mem_cusp _ _ _ _ _ _).1 hFc).2 _ hem) ⟨k, ⟨y, hy⟩⟩) (lieFac_pos _ _ _).le)
  refine hb.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) h0)
  unfold CarchAt
  have h1 := absA_add_le_size T h.pins j hj ka
  have h2 : (fdeg D.host.E : ℝ) = D.R.f := by
    unfold fdeg
    rw [hf, Nat.mul_div_cancel_left _ two_pos]
  have h3 : (D.R.f : ℝ) * ka.n ≤ (D.R.f : ℝ) * D.R.r * ka.n := by
    have : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr
    have h4 : (0 : ℝ) ≤ (D.R.f : ℝ) * ka.n := by positivity
    nlinarith
  rw [h2]
  have h5 := archimedeanTerm_nonneg D.host.E hr (one_le_LaAt D j ka CR Tt cc) (WeightFamilies.c1 D CR Tt cc j)
  exact add_le_add_right (mul_le_mul_of_nonneg_left (by linarith) h5) _

theorem arch_all (hK : Known) {D : D7} {T : Core D} (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ)
    (hG : GlobalTheory.RunIn.GamAt T) (hj : InR D j) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁]
    (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁) (hd : Std d)
    (s : CMIn d.a d.e d.th d.jj (nAt D j ka CR Tt cc) (LaAt D j ka CR Tt cc) (WeightFamilies.c1 D CR Tt cc j))
    (em : K₁ →+* ℂ) (F : (recB h).Cusp j ka) :
    ‖em (cfOf d.yF d.μ d.jj F.1)‖ * (s.valLine d.μ ka.n).n em ≤
      (recB h).supN j ka (em.comp (algebraMap T.Q.c.F K₁)) F * Real.exp (CarchAt D j ka CR Tt cc) := by
  by_cases hem : GoodEmb T.Q.c (em.comp (algebraMap T.Q.c.F K₁))
  · exact arch_good hK h j ka CR Tt cc hG hj K₁ d hd s em hem F
  · have hg := goodEmb_goodOf T.Q.c (em.comp (algebraMap T.Q.c.F K₁))
    rw [goodOf, if_neg hem] at hg
    have h1 := arch_good hK h j ka CR Tt cc hG hj K₁ d hd s ((starRingEnd ℂ).comp em) hg F
    rw [GlobalTheory.T.cmValueLine_length_conj_eq hK _ _ _ _ _ K₁ _ _ _ _ _ _ _ s d.μ ka.n em, RingHom.comp_assoc, recB_supN_conj] at h1
    simpa using h1

end GlobalTheory.ArcCM.RunNum

namespace GlobalTheory.ArcCM

open RunNum

theorem numGood_of_famQ : Known → ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (large₂ : SizeData₂ D), GlobalTheory.RunIn.GamAt T → InR D j → j < D.R.m → ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra T.Q.c.F K₁] (d : GlobalTheory.ArcQ.ArcDatum (T.Q.Xo j) T.Q.c K₁), FamQ T j ka CR Tt cc K₁ d → ∃ φ : (recB h).Cusp j ka →ₗ[T.Q.c.F] K₁, (∀ F, φ F = cfOf d.yF d.μ d.jj F.1) ∧ @NumGood T.Q.c.F ((recB h).Cusp j ka) _ _ ((recB h).acgC j ka) ((recB h).modC j ka) {F | F ∈ (recB h).Mlat j ka} (fun σ F => (recB h).supN j ka σ F) (beOf D.host.E (nAt D j ka CR Tt cc) (absA (T.Q.Dw j) (wtA ka))) (CarchAt D j ka CR Tt cc) (BdegAt large₂ j ka CR Tt cc) K₁ _ _ _ φ := by
  intro hK D T h j ka CR Tt cc large₂ hG hj _ K₁ _ _ _ d ⟨hd, ⟨s⟩⟩
  obtain ⟨hgood, -, -, -, -, hf, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨hpq, hr, -⟩ := hnum j hj
  have hle : cutR T.C j ka ≤ sec (T.Q.Xo j) T.Q.c (wtA ka) ka.n :=
    (cutR_le T.C j ka).trans (cusp_le_sec _ _ _ _ _)
  obtain ⟨⟨ψ, hψ⟩, hdeg⟩ := cfOf_linear_and_degree hK _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d (wtA ka) ka.n
  have hLa := one_le_LaAt D j ka CR Tt cc
  have hc : 0 ≤ pDeg large₂.logOm + (1 / 2) * Real.log (LaAt D j ka CR Tt cc) := by
    have := Real.log_nonneg hLa
    unfold pDeg
    positivity
  have hφ : ∀ F : (recB h).Cusp j ka, (ψ.comp (Submodule.inclusion hle)) F = cfOf d.yF d.μ d.jj F.1 :=
    fun F => hψ _
  refine ⟨ψ.comp (Submodule.inclusion hle), hφ, ?_⟩
  by_cases hμ : ∑ v, d.μ v = absA (T.Q.Dw j) (wtA ka)
  · obtain ⟨hN, hNd⟩ := valLine_ndeg_le hK _ _ _ _ _ K₁ _ _ _ _ _ _ _ s large₂.logOm d.μ ka.n hLa
      (lamDegSt_logOm₂ hK D T large₂ h.pins)
    refine ⟨s.valLine d.μ ka.n, hN, hNd.trans ?_, GlobalTheory.T.cmValueLine_length_conj_eq hK _ _ _ _ _ K₁ _ _ _ _ _ _ _ s _ _, ?_, ?_⟩
    · unfold BdegAt
      refine mul_le_mul_of_nonneg_left ?_ hc
      rw [hμ, hf, hpq, Nat.mul_div_cancel_left _ two_pos]
      push_cast
      exact absA_add_le_size T h.pins j hj ka
    · intro la w hw F hF hne
      rw [hφ] at hne ⊢
      exact GlobalTheory.T.cmArcDatum_functional_finite_integrality_bound hK _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d _ _ _ s
        (modelsAt_of_good_level hK _ _ _ _ _ _ (hpq ▸ hr) hgood) hd hLa la w hw (wtA ka) ka.n F.1
        ⟨hle F.2, fun v hv => hF la v hv⟩ hne
    · intro em F _ hne
      have hpos : 0 < (recB h).supN j ka (em.comp (algebraMap T.Q.c.F K₁)) F := by
        refine lt_of_le_of_ne ((recB h).supN_nonneg j ka _ F) fun h0 => hne ?_
        rw [((recB h).supN_eq_zero j ka _ F).1 h0.symm]
        exact map_zero _
      have h1 := arch_all hK h j ka CR Tt cc hG hj K₁ d hd s em F
      rw [hφ] at hne ⊢
      have h2 : 0 < ‖em (cfOf d.yF d.μ d.jj F.1)‖ := norm_pos_iff.2 ((map_ne_zero em).2 hne)
      have h3 := Real.log_le_log (mul_pos h2 (hN.2 em)) h1
      rwa [Real.log_mul h2.ne' (hN.2 em).ne', Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp] at h3
  · have hz : ∀ F : (recB h).Cusp j ka, ¬ (ψ.comp (Submodule.inclusion hle)) F ≠ 0 := fun F hne =>
      hμ (hdeg F.1 (hle F.2) (hφ F ▸ hne))
    refine ⟨MLine.one, ⟨one_ne_zero, fun _ => one_pos⟩, ?_, fun _ => rfl, fun _ _ _ F _ hne => (hz F hne).elim,
      fun _ F _ hne => (hz F hne).elim⟩
    have : (MLine.one : MLine K₁).ndeg = 0 := by simp [MLine.ndeg, MLine.deg, MLine.one]
    rw [this]
    exact mul_nonneg hc (zero_le_one.trans ka.one_le_size)

end GlobalTheory.ArcCM
