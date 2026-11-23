import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsQuotientIntegrableFoldUnimodular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingBasePointFourierJacobiGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelBaseValueEquivariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselUnfoldingEvaluationIntegrandContinuousInva
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedBesselJacobiIntegralAbsLe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalUnitarySubgroupCountableDiscreteFundDoma
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemidirectHaarMeasureFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMixedCoordinatesContinuousBoundedSupNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContAutRapidDecBoundedIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBesselGroupsClosedHaarProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.EvalAbs

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem sFinite_of_haar {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [LocallyCompactSpace G]
    [SecondCountableTopology G] (μ : Measure G) [μ.IsHaarMeasure] : SFinite μ := inferInstance

theorem lintegral_three_lt_top {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {ν : Measure β} {κ : Measure γ} [SFinite μ] [SFinite ν] [SFinite κ] {φ : α → ℂ} {G : β → ℂ}
    {E : α → β → γ → ℂ} (hφ : Measurable φ) (hG : Measurable G) (hE : Measurable fun p : α × β × γ => E p.1 p.2.1 p.2.2)
    (hi : Integrable φ μ) {M : ℝ} (hM : ∀ a, ∫⁻ b, ‖G b‖ₑ * ∫⁻ c, ‖E a b c‖ₑ ∂κ ∂ν ≤ ENNReal.ofReal M) :
    ∫⁻ b, ∫⁻ c, ‖G b‖ₑ * ∫⁻ a, ‖φ a‖ₑ * ‖E a b c‖ₑ ∂μ ∂κ ∂ν < ∞ := by
  have hm : Measurable fun p : (β × γ) × α => ‖φ p.2‖ₑ * (‖G p.1.1‖ₑ * ‖E p.2 p.1.1 p.1.2‖ₑ) :=
    (hφ.comp measurable_snd).enorm.mul ((hG.comp (measurable_fst.comp measurable_fst)).enorm.mul
      (hE.comp (measurable_snd.prodMk measurable_fst)).enorm)
  calc ∫⁻ b, ∫⁻ c, ‖G b‖ₑ * ∫⁻ a, ‖φ a‖ₑ * ‖E a b c‖ₑ ∂μ ∂κ ∂ν
      = ∫⁻ b, ∫⁻ c, ∫⁻ a, ‖φ a‖ₑ * (‖G b‖ₑ * ‖E a b c‖ₑ) ∂μ ∂κ ∂ν := by
        refine lintegral_congr fun b => lintegral_congr fun c => ?_
        rw [← lintegral_const_mul' _ _ enorm_ne_top]
        exact lintegral_congr fun a => mul_left_comm _ _ _
    _ = ∫⁻ p : β × γ, ∫⁻ a, ‖φ a‖ₑ * (‖G p.1‖ₑ * ‖E a p.1 p.2‖ₑ) ∂μ ∂ν.prod κ :=
        (lintegral_prod _ hm.lintegral_prod_right'.aemeasurable).symm
    _ = ∫⁻ a, ∫⁻ p : β × γ, ‖φ a‖ₑ * (‖G p.1‖ₑ * ‖E a p.1 p.2‖ₑ) ∂ν.prod κ ∂μ := lintegral_lintegral_swap hm.aemeasurable
    _ ≤ ∫⁻ a, ‖φ a‖ₑ * ENNReal.ofReal M ∂μ := by
        refine lintegral_mono fun a => ?_
        have h1 : Measurable fun p : β × γ => ‖G p.1‖ₑ * ‖E a p.1 p.2‖ₑ :=
          (hG.comp measurable_fst).enorm.mul (hE.comp measurable_prodMk_left).enorm
        rw [lintegral_const_mul' _ _ enorm_ne_top, lintegral_prod _ h1.aemeasurable]
        simp only [lintegral_const_mul' _ _ enorm_ne_top]
        exact mul_le_mul_right (hM a) _
    _ < ∞ := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_lt_top hi.2 ENNReal.ofReal_lt_top

theorem norm_theta_add (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : WO S T}
    (hγ : γ ∈ ratMx D T.rank S.rank) (w : WO S T) : ‖f (γ + w)‖ = ‖f w‖ := by
  obtain ⟨δ, rfl⟩ := hγ
  have h := hf.quasi δ w
  rw [show f ((incA D).toAddMonoidHom.mapMatrix δ + w) = _ from h, norm_mul, hψ.1.2.1, one_mul]

theorem yZero_mem (S : HSp D) (ρ : ℕ) (z : Fin S.rank → D.host.E) : yZero S ρ z ∈ ratMx D S.rank ρ := by
  refine neg_mem (mem_ratMx.2 ⟨vecMulVec z fun i => if i.1 + 1 = ρ then 1 else 0, ?_⟩)
  funext i j
  change incA D (z i * if j.1 + 1 = ρ then 1 else 0) = incA D (z i) * ell D ρ j
  unfold ell
  split_ifs
  · rw [mul_one, mul_one]
  · rw [mul_zero, mul_zero, map_zero]

theorem incAdj_mem {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) {y : Mx D S.rank ρ} (hy : y ∈ ratMx D S.rank ρ) :
    d.incAdj S y ∈ ratMx D T.rank S.rank :=
  ratMx_mul (rat_mem _) (ratMx_smul _ (ratMx_mul (ratMx_adj hy) (rat_mem _)))

variable {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J)

def val (Ψ : WO B.V J.W → ℂ) (x : Mx D J.W.rank ρ) : WO B.V₀ J.W₀ → ℂ :=
  evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ x (yZero B.V₀ ρ (vecB B.o B.ζ))

theorem val_theta {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) (x : Mx D J.W.rank ρ) :
    IsThetaFunO ψ B.V₀ J.W₀ (val s Ψ x) :=
  (GlobalTheory.MixValues.mixed_values D ψ s.weil.std).2 _ _ _ _ J.d _ _ s.vT.covol _
    ((GlobalTheory.MixValues.mixed_values D ψ s.weil.std).1 _ _ _ _ B.d _ _ s.vS.covol Ψ hΨ x) _

theorem enorm_val_le {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) (x : Mx D J.W.rank ρ) :
    ‖val s Ψ x 0‖ₑ ≤ ∫⁻ b in s.vT.𝓕, ‖B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ x (xZero J.d ⬝ b)‖ₑ ∂s.vT.μ := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun b => ?_))
  have hf := (GlobalTheory.MixValues.mixed_values D ψ s.weil.std).1 _ _ _ _ B.d _ _ s.vS.covol Ψ hΨ x
  rw [J.d.integrandT_eq, map_zero, add_zero, add_comm, ← ofReal_norm, ← ofReal_norm, norm_mul, s.weil.std.1.2.1, one_mul,
    norm_theta_add s.weil.std hf (incAdj_mem J.d _ (yZero_mem _ _ _))]
  rfl

variable {om' : Om B.V₀ J.W} (hom : IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om')
include hom

theorem val_flag {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) (h₀ : GA D B.A) {n : GA D J.W} (hn : n ∈ flagN J.d)
    (h' : GA D J.W₀) (u : UX D ρ) :
    val s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (mt J.W (n * J.d.emb0 h') ⬝ (xZero J.d ⬝ u.1.1)) =
      s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (val s Ψ (xZero J.d ⬝ u.1.1))) := by
  obtain ⟨v, hv, b, c, rfl⟩ := Decomp.flag_decomp J.d hn
  have hr : J.d.nB b * J.d.nC c ∈ radX J.d := (Decomp.mem_radX_iff J.d).2 ⟨b, c, rfl⟩
  have e1 : s.om (embA B.d B.o h₀, J.d.levi v * (J.d.nB b * J.d.nC c) * J.d.emb0 h') Ψ =
      s.om (1, J.d.levi v) (s.om (embA B.d B.o h₀, J.d.nB b * J.d.nC c * J.d.emb0 h') Ψ) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_assoc (J.d.levi v)]
  have e2 : mt J.W (J.d.levi v * (J.d.nB b * J.d.nC c) * J.d.emb0 h') ⬝ (xZero J.d ⬝ u.1.1) =
      xZero J.d ⬝ ((⟨v, hv⟩ : UX D ρ) * u).1.1 := by
    rw [xZero, ← Matrix.mul_assoc, mt_mul, Matrix.mul_assoc (mt J.W _), J.d.wittDecomp_anisotropicEmbedding_inclX, Decomp.mt_flag_jX, Matrix.mul_assoc]
    rfl
  have e3 := (GlobalTheory.Unf.evalAt_xZero_yZero D ψ ρ B J s om' hom _ (s.weil.om_pres (embA B.d B.o h₀, J.d.nB b * J.d.nC c * J.d.emb0 h') Ψ hΨ)).2
    (⟨v, hv⟩ * u) ⟨v, hv⟩
  rw [inv_mul_cancel_left] at e3
  rw [e1, e2, val, e3, (GlobalTheory.Unf.evalAt_xZero_yZero D ψ ρ B J s om' hom Ψ hΨ).1 u h₀ _ hr h', opA, opA,
    jacT_levi_mul ψ J.d B.V₀ _ (yZero_mul B.V₀ _ hv)]
  rfl

theorem val_ratA {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) {γ : GA D B.A} (hγ : γ ∈ GQ B.A) (u : UX D ρ) :
    val s (s.om (embA B.d B.o γ, 1) Ψ) (xZero J.d ⬝ u.1.1) 0 = val s Ψ (xZero J.d ⬝ u.1.1) 0 := by
  have h := val_flag s hom hΨ γ (one_mem _) 1 u
  rw [map_one, mul_one, mt_one, Matrix.one_mul, opA, jacT_one, id, Prod.mk_one_one, map_one, Module.End.one_apply] at h
  rw [h]
  exact s.weil₀.om_aut _ (B.o.emb_mem_GQ hγ (one_mem _)) 1 (one_mem _) _ (val_theta s hΨ _)

theorem val_ratR {Ψ : WO B.V J.W → ℂ} (hΨ : IsThetaFunO ψ B.V J.W Ψ) {γ : GA D J.W} (hγ : γ ∈ GQ J.W ⊓ jacGrp J.d)
    (u : UX D ρ) :
    ‖val s (s.om (1, γ) Ψ) (mt J.W γ ⬝ (xZero J.d ⬝ u.1.1)) 0‖ = ‖val s Ψ (xZero J.d ⬝ u.1.1) 0‖ := by
  obtain ⟨hq, hj⟩ := Subgroup.mem_inf.1 hγ
  obtain ⟨n, hn, h', rfl⟩ := (Decomp.mem_jacGrp_iff J.d).1 hj
  obtain ⟨hnq, hh⟩ := ((GlobalTheory.Unf.base_point D J.W J.W₀ ρ J.d).2.2.2.2.2 n hn h').1 hq
  have h := val_flag s hom hΨ 1 hn h' u
  rw [map_one, Prod.mk_one_one, map_one, Prod.mk_one_one, map_one, Module.End.one_apply] at h
  have ht := val_theta s hΨ (xZero J.d ⬝ u.1.1)
  have hp : ptT J.d B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ)) n ∈ ratMx D J.W₀.rank B.V₀.rank :=
    ratMx_mul (rat_mem _) (ratMx_mul ((mem_GQ_iff _ _).1 (inv_mem hnq)) (incAdj_mem J.d _ (yZero_mem _ _ _)))
  rw [h, opA, jacT, Pi.smul_apply, smul_eq_mul, heisO, norm_mul, norm_mul, s.weil.std.1.2.1, s.weil.std.1.2.1, one_mul,
    one_mul, add_comm, norm_theta_add s.weil.std (s.weil₀.om_pres _ _ ht) hp,
    s.weil₀.om_aut 1 (one_mem _) h' hh _ ht]

variable (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ)

omit hom in

def evalMaj (g r : GA D J.W) : ℝ≥0∞ :=
  ‖G g‖ₑ * ∫⁻ h₀ in B.vA.𝓕, ‖φ h₀‖ₑ * ‖val s (s.om (embA B.d B.o h₀, g) Φ) (mt J.W r ⬝ xZero J.d) 0‖ₑ ∂B.vA.μ

variable {φ G Φ}

omit hom in
theorem continuous_val (hΦ : IsThetaFunO ψ B.V J.W Φ) {X : Type} [TopologicalSpace X] {a : X → GA D B.A} {g : X → GA D J.W}
    {x : X → Mx D J.W.rank ρ} (ha : Continuous a) (hg : Continuous g) (hx : Continuous x) :
    Continuous fun p => val s (s.om (embA B.d B.o (a p), g p) Φ) (x p) 0 := by
  have hA : Continuous (embA B.d B.o) :=
    B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))
  have hc : Continuous fun p : X => ((embA B.d B.o (a p), g p), x p, yZero B.V₀ ρ (vecB B.o B.ζ), (0 : WO B.V₀ J.W₀)) :=
    ((hA.comp ha).prodMk hg).prodMk (hx.prodMk continuous_const)
  have h := (GlobalTheory.MixCont.mixed_coords_continuous D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil Φ hΦ).2.comp hc
  simpa only [Function.comp_def, val] using h

omit hom in
theorem measurable_maj (hφ : IsContAut B.A φ) (hG : RapidDec J.W G) (hΦ : IsThetaFunO ψ B.V J.W Φ) :
    Measurable (Function.uncurry (evalMaj s φ G Φ)) := by
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D J.W
  obtain ⟨j1, j2, j3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D B.A
  have : BorelSpace (GA D J.W) := ⟨rfl⟩
  have : BorelSpace (GA D B.A) := ⟨rfl⟩
  have := B.vA.haar
  have := sFinite_of_haar B.vA.μ
  refine (hG.continuous.measurable.comp measurable_fst).enorm.mul ?_
  have hc : Continuous fun p : GA D B.A × GA D J.W × GA D J.W =>
      val s (s.om (embA B.d B.o p.1, p.2.1) Φ) (mt J.W p.2.2 ⬝ xZero J.d) 0 :=
    continuous_val s hΦ continuous_fst (continuous_fst.comp continuous_snd)
      (((continuous_mt J.W).comp (continuous_snd.comp continuous_snd)).matrix_mul continuous_const)
  exact ((hφ.2.measurable.comp measurable_fst).enorm.mul hc.measurable.enorm).lintegral_prod_left'

omit hom in
theorem exists_mt_xZero {r : GA D J.W} (hr : r ∈ jacGrp J.d) : ∃ v : UX D ρ, mt J.W r ⬝ xZero J.d = xZero J.d ⬝ v.1.1 := by
  rw [← (GlobalTheory.Unf.base_point D J.W J.W₀ ρ J.d).2.2.2.1] at hr
  obtain ⟨v, hv, e⟩ := hr
  exact ⟨⟨v, hv⟩, e⟩

omit hom in

theorem exists_levi_conj {r : GA D J.W} (hr : r ∈ jacGrp J.d) : ∃ v : UX D ρ, ∀ u : UX D ρ,
    ∃ t ∈ radX J.d ⊔ J.d.emb0.range, J.d.levi u.1 * r = t * J.d.levi (u * v).1 := by
  obtain ⟨v, hv⟩ := exists_mt_xZero hr
  refine ⟨v, fun u => ⟨J.d.levi u.1 * r * (J.d.levi (u * v).1)⁻¹, ?_, (inv_mul_cancel_right _ _).symm⟩⟩
  have hs : J.d.levi u.1 * r * (J.d.levi (u * v).1)⁻¹ ∈ stabX J.d := by
    have h1 : mt J.W (J.d.levi u.1 * r) ⬝ xZero J.d = mt J.W (J.d.levi (u * v).1) ⬝ xZero J.d := by
      rw [mt_mul, Matrix.mul_assoc, hv, ← Matrix.mul_assoc, levi_xZero, levi_xZero, Matrix.mul_assoc]
      rfl
    change mt J.W _ ⬝ xZero J.d = xZero J.d
    rw [← map_inv, mt_mul, Matrix.mul_assoc, levi_xZero, ← Matrix.mul_assoc, h1, levi_xZero, Matrix.mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  obtain ⟨n, hn, h', e⟩ := (Decomp.mem_stabX_iff J.d).1 hs
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h', rfl⟩)

theorem maj_left (hG : RapidDec J.W G) (hΦ : IsThetaFunO ψ B.V J.W Φ) {γ : GA D J.W} (hγ : γ ∈ GQ J.W ⊓ jacGrp J.d)
    (g : GA D J.W) {r : GA D J.W} (hr : r ∈ jacGrp J.d) : evalMaj s φ G Φ (γ * g) (γ * r) = evalMaj s φ G Φ g r := by
  obtain ⟨v, hv⟩ := exists_mt_xZero hr
  rw [evalMaj, evalMaj, hG.left (Subgroup.mem_inf.1 hγ).1]
  refine congrArg (‖G g‖ₑ * ·) (lintegral_congr fun h₀ => ?_)
  have h := val_ratR s hom (s.weil.om_pres (embA B.d B.o h₀, g) Φ hΦ) hγ v
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul] at h
  rw [mt_mul, Matrix.mul_assoc, hv, ← ofReal_norm (val s _ _ 0), h, ofReal_norm]

omit hom in
theorem maj_levi {r : GA D J.W} (hr : r ∈ jacGrp J.d) :
    ∃ v : UX D ρ, ∀ g (u : UX D ρ), evalMaj s φ G Φ g (r * J.d.levi u.1) = evalMaj s φ G Φ g (J.d.levi (v * u).1) := by
  obtain ⟨v, hv⟩ := exists_mt_xZero hr
  refine ⟨v, fun g u => ?_⟩
  have e : mt J.W (r * J.d.levi u.1) ⬝ xZero J.d = mt J.W (J.d.levi (v * u).1) ⬝ xZero J.d := by
    rw [mt_mul, Matrix.mul_assoc, levi_xZero, levi_xZero, ← Matrix.mul_assoc, hv, Matrix.mul_assoc]
    rfl
  rw [evalMaj, evalMaj, e]

theorem enorm_fjAllFun_le (hΦ : IsThetaFunO ψ B.V J.W Φ) (h : GA D J.W) (h' : GA D J.W₀) (n : flagN J.d) :
    ‖fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ (rTrans h G) (evalBF s (s.om (1, h) Φ)) h' n‖ₑ ≤
      evalMaj s φ G Φ (n.1 * J.d.emb0 h' * h) (n.1 * J.d.emb0 h') := by
  have e : ‖star (psiFlag ψ J.d n.1)‖ₑ = 1 := by
    rw [← ofReal_norm, norm_star, psiFlag, psiE, s.weil.std.1.2.1, ENNReal.ofReal_one]
  rw [fjAllFun, enorm_mul, enorm_mul, e, mul_one, evalMaj]
  refine mul_le_mul_right ((enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun h₀ => ?_))) _
  have h1 := val_flag s hom (s.weil.om_pres (1, h) Φ hΦ) h₀ n.2 h' 1
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, OneMemClass.coe_one, Units.val_one, Matrix.mul_one] at h1
  rw [enorm_mul, h1]
  rfl

theorem exists_bound (hG : RapidDec J.W G) (hΦ : IsThetaFunO ψ B.V J.W Φ)
    {𝓑 : Set (GA D J.W)} (h𝓑 : IsFundamentalDomain (GQ J.W ⊓ jacGrp J.d : Subgroup (GA D J.W)) 𝓑 s.vW.μ) :
    ∃ M : ℝ, ∀ h₀, ∫⁻ g in 𝓑, ‖G g‖ₑ * ∫⁻ u : UX D ρ,
      ‖val s (s.om (embA B.d B.o h₀, g) Φ) (xZero J.d ⬝ u.1.1) 0‖ₑ ∂s.vU.ν ∂s.vW.μ ≤ ENNReal.ofReal M := by
  obtain ⟨hb, -, -, hR, -⟩ := GlobalTheory.Unf.base_point D J.W J.W₀ ρ J.d
  obtain ⟨C, A, hC⟩ := GlobalTheory.Unf.UnfoldBound.unfolded_integral_le D ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom s.vS s.vT s.vU s.vW J.d.e hb G Φ
    hG hΦ 𝓑 (by rw [hR]; exact h𝓑)
  have hA : Continuous (embA B.d B.o) :=
    B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))
  obtain ⟨K, hK, hcov⟩ := B.cpt
  have hc : Continuous fun h₀ => C * height B.V (embA B.d B.o h₀) ^ A :=
    continuous_const.mul (((continuous_height B.V).comp hA).pow A)
  obtain ⟨M, hM⟩ := hK.bddAbove_image hc.continuousOn
  refine ⟨M, fun h₀ => ?_⟩
  obtain ⟨γ, hγ, hk⟩ := hcov h₀
  refine le_trans (lintegral_mono fun g => ?_)
    ((hC (embA B.d B.o (γ * h₀))).trans (ENNReal.ofReal_le_ofReal (hM ⟨_, hk, rfl⟩)))
  refine mul_le_mul_right (lintegral_mono fun u => ?_) _
  have h1 := val_ratA s hom (s.weil.om_pres (embA B.d B.o h₀, g) Φ hΦ) hγ u
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, ← map_mul] at h1
  exact (congrArg enorm h1).symm.le.trans (enorm_val_le s (s.weil.om_pres _ Φ hΦ) _)

theorem lintegral_maj_lt_top (hφ : IsContAut B.A φ) (hG : RapidDec J.W G) (hΦ : IsThetaFunO ψ B.V J.W Φ)
    {𝓑 : Set (GA D J.W)} (h𝓑 : IsFundamentalDomain (GQ J.W ⊓ jacGrp J.d : Subgroup (GA D J.W)) 𝓑 s.vW.μ) :
    ∫⁻ g in 𝓑, ∫⁻ u : UX D ρ, evalMaj s φ G Φ g (J.d.levi u.1) ∂s.vU.ν ∂s.vW.μ < ∞ := by
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D J.W
  obtain ⟨j1, j2, j3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D B.A
  obtain ⟨k1, k2, k3⟩ := GlobalTheory.UnitU.topology D ρ
  have : BorelSpace (GA D J.W) := ⟨rfl⟩
  have : BorelSpace (GA D B.A) := ⟨rfl⟩
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  have := B.vA.haar
  have := sFinite_of_haar B.vA.μ
  have := s.vW.haar
  have := sFinite_of_haar s.vW.μ
  have := s.vU.unit.1
  have := sFinite_of_haar s.vU.ν
  obtain ⟨M, hM⟩ := exists_bound s hom hG hΦ h𝓑
  have hc : Continuous fun p : GA D B.A × GA D J.W × UX D ρ =>
      val s (s.om (embA B.d B.o p.1, p.2.1) Φ) (xZero J.d ⬝ p.2.2.1.1) 0 :=
    continuous_val s hΦ continuous_fst (continuous_fst.comp continuous_snd) (continuous_const.matrix_mul
      ((GlobalTheory.UnitU.isClosedEmbedding_val D ρ).continuous.comp (continuous_snd.comp continuous_snd)))
  simp only [evalMaj, levi_xZero]
  exact lintegral_three_lt_top (E := fun h₀ g (u : UX D ρ) => val s (s.om (embA B.d B.o h₀, g) Φ) (xZero J.d ⬝ u.1.1) 0)
    hφ.2.measurable hG.continuous.measurable hc.measurable
    ((contAut_rapidDec_bounded_integrable D B.A B.cpt φ hφ).2.2 B.vA) hM

omit hom in

theorem exists_domain (J : JacLev D ρ) : IsClosed (jacGrp J.d : Set (GA D J.W)) ∧ J.μR.IsHaarMeasure ∧ J.μR.IsInvInvariant ∧
    ∃ 𝓡 : Set (jacGrp J.d), IsFundamentalDomain ((GQ J.W ⊓ jacGrp J.d).subgroupOf (jacGrp J.d)) 𝓡 J.μR ∧
      ∀ F : GA D J.W → ℝ≥0∞, Measurable F →
        ∫⁻ r in 𝓡, F r ∂J.μR = ∫⁻ h in J.v0.𝓕, ∫⁻ n in J.vN.𝓝, F (n.1 * J.d.emb0 h) ∂J.vN.ν ∂J.v0.μ := by
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D J.W
  obtain ⟨j1, j2, j3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D J.W₀
  have : BorelSpace (GA D J.W) := ⟨rfl⟩
  have : BorelSpace (GA D J.W₀) := ⟨rfl⟩
  have := J.v0.haar
  have := J.vN.unit.1
  have o : OrthDec J.W₀ J.W₀ (diagSp D 0 ![] 0 0) :=
    { iA := 1
      iB := 0
      isoA := by simp
      isoB := funext fun i => Fin.elim0 i
      orth := funext fun i => Fin.elim0 i
      rank_add := rfl }
  obtain ⟨⟨hc, hH⟩, -⟩ := GlobalTheory.MixPer.jacGrp_besGrp_haar D J.W J.W₀ J.W₀ (diagSp D 0 ![] 0 0) ρ J.d o J.vN.ν J.vN.𝓝 J.vN.unit
  have hN : IsClosed (flagN J.d : Set (GA D J.W)) := GlobalTheory.Mem.TrueRecord.isClosed_NFlag J.W (isIsoSub_e J.d)
  have : LocallyCompactSpace (flagN J.d) := hN.locallyCompactSpace
  have : SecondCountableTopology (flagN J.d) := TopologicalSpace.Subtype.secondCountableTopology (flagN J.d : Set (GA D J.W))
  have : LocallyCompactSpace (jacGrp J.d) := hc.locallyCompactSpace
  have : SecondCountableTopology (jacGrp J.d) := TopologicalSpace.Subtype.secondCountableTopology (jacGrp J.d : Set (GA D J.W))
  have := sFinite_of_haar J.v0.μ
  have := sFinite_of_haar J.vN.ν
  have hHaar : J.μR.IsHaarMeasure := hH _ J.v0.haar
  obtain ⟨𝓡, h𝓡', hint⟩ : ∃ 𝓡 : Set (jacGrp J.d),
      IsFundamentalDomain ((GQ J.W ⊓ jacGrp J.d).subgroupOf (jacGrp J.d)) 𝓡 J.μR ∧ ∀ f : GA D J.W → ℂ, Measurable f →
        (IntegrableOn (fun r : jacGrp J.d => f r) 𝓡 J.μR ↔
          AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 fun h n => f (n.1 * J.d.emb0 h)) ∧
        (AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 (fun h n => f (n.1 * J.d.emb0 h)) → ∫ r in 𝓡, f (r : GA D J.W) ∂J.μR =
          ∫ h in J.v0.𝓕, ∫ n in J.vN.𝓝, f (n.1 * J.d.emb0 h) ∂J.vN.ν ∂J.v0.μ) := GlobalTheory.Unf.semiFd_iterated D J.W J.W₀ (flagN J.d) J.d.emb0 J.d.continuous_embed hN
    (fun n hn h => Decomp.conj_mem J.d hn h) (fun n hn n' hn' h h' e => Decomp.flag_unipotent_mul_embedded_anisotropic_unique J.d hn hn' e)
    (GlobalTheory.Unf.base_point D J.W J.W₀ ρ J.d).2.2.2.2.2 J.v0 J.vN.ν J.vN.𝓝 J.vN.unit.1 J.vN.unit.2.1 hHaar
  have hb : Measurable fun p : GA D J.W₀ × flagN J.d => p.2.1 * J.d.emb0 p.1 :=
    (measurable_subtype_coe.comp measurable_snd).mul (J.d.continuous_embed.measurable.comp measurable_fst)
  have hF : ∀ F : GA D J.W → ℝ≥0∞, Measurable F →
      ∫⁻ r in 𝓡, F r ∂J.μR = ∫⁻ h in J.v0.𝓕, ∫⁻ n in J.vN.𝓝, F (n.1 * J.d.emb0 h) ∂J.vN.ν ∂J.v0.μ := fun F hF => by
    refine (lintegral_eq_of_integral (a := fun r : jacGrp J.d => r.1) measurable_subtype_coe hb (fun f hf => ?_) F hF).trans
      (lintegral_prod _ (hF.comp hb).aemeasurable)
    exact ⟨(hint f hf).1, fun hi => ((hint f hf).2 hi).trans (integral_prod _ hi).symm⟩
  have : Countable (GQ J.W ⊓ jacGrp J.d : Subgroup (GA D J.W)) := (GlobalTheory.RationalSubgroupFund.countable_discrete_exists_fundamentalDomain D J.W _ inf_le_left).1
  have : Countable ((GQ J.W ⊓ jacGrp J.d).subgroupOf (jacGrp J.d)) :=
    (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv.countable_iff.2 inferInstance
  have hfin : J.μR 𝓡 ≠ ∞ := by
    have h1 := hF (fun _ => 1) measurable_const
    have h2 := (contAut_rapidDec_bounded_integrable D J.W₀ J.cpt (fun _ => 1) ⟨fun _ _ _ => rfl, continuous_const⟩).2.2 J.v0
    rw [integrableOn_const_iff] at h2
    simp only [enorm_eq_zero, one_ne_zero, false_or] at h2
    simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, one_mul, J.vN.unit.2.2] at h1
    rw [h1]; exact h2.ne
  have := GlobalTheory.UnitU.isMulRightInvariant_of_fundamentalDomain _ J.μR h𝓡' (h𝓡'.measure_ne_zero (NeZero.ne _)) hfin
  exact ⟨hc, hHaar, GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant _, 𝓡, h𝓡', hF⟩

end GlobalTheory.EvalAbs

namespace GlobalTheory.Unf

set_option maxHeartbeats 800000 in
open GlobalTheory.EvalAbs in

theorem evalBF_abs : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ → ∃ z', IsQuotIntL1 J.μR s.vW.μ (fun h => ((∫ u : UX D ρ, ‖J.perAll ψ B s.om₀ φ (rTrans (J.d.levi u.1 * h) G) (evalBF s (s.om (1, (J.d.levi u.1 * h)) Φ))‖ ∂s.vU.ν : ℝ) : ℂ)) z' := by
  intro D ψ ρ B J s om' hom φ G Φ hφ hG hΦ
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D J.W
  obtain ⟨k1, k2, k3⟩ := GlobalTheory.UnitU.topology D ρ
  have : BorelSpace (GA D J.W) := ⟨rfl⟩
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  have := s.vW.haar
  have := sFinite_of_haar s.vW.μ
  have := s.vU.unit.1
  have := sFinite_of_haar s.vU.ν
  have := (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).2.2 _ s.vU.unit
  have := GlobalTheory.QuotDiscrete.isInvInvariant_of_isMulRightInvariant s.vU.ν
  obtain ⟨hc, hH, hI, 𝓡, h𝓡, hF⟩ := exists_domain J
  obtain ⟨c1, c2, hex⟩ := GlobalTheory.RationalSubgroupFund.countable_discrete_exists_fundamentalDomain D J.W (GQ J.W ⊓ jacGrp J.d) inf_le_left
  obtain ⟨𝓑, h𝓑⟩ := hex _ s.vW.haar
  obtain ⟨hcont, hinv⟩ := GlobalTheory.Unf.evalIntegrand_continuous_invariant D ψ ρ B J s om' hom φ G Φ hφ hG hΦ
  have hq := measurable_maj s hφ hG hΦ
  refine exists_quotientIntegrable_fold_unimodular inf_le_right hc h𝓡 h𝓑 (J.d.levi.comp (UX D ρ).subtype)
    (J.d.continuous_levi.comp continuous_subtype_val).measurable
    (fun u => Subgroup.mem_sup_left (J.d.levi_mem_NFlag u.2)) hq (fun γ hγ g r hr => maj_left s hom hG hΦ hγ g hr)
    (fun r hr => maj_levi s hr) (lintegral_maj_lt_top s hom hφ hG hΦ h𝓑)
    (P := fun h => J.perAll ψ B s.om₀ φ (rTrans h G) (evalBF s (s.om (1, h) Φ))) hcont.measurable
    (fun r hr => ?_) fun h => ?_
  · obtain ⟨v, hv⟩ := exists_levi_conj hr
    refine ⟨v, fun g u => ?_⟩
    obtain ⟨t, ht, e⟩ := hv u
    have h2 := hinv t ht (J.d.levi (u * v).1 * g)
    rw [← mul_assoc, ← e, mul_assoc] at h2
    exact h2
  · have hp : Measurable fun r : GA D J.W => (r * h, r) := (measurable_id.mul_const h).prodMk measurable_id
    have hm := hq.comp hp
    simp only [Function.comp_def, Function.uncurry_apply_pair] at hm
    refine le_trans ?_ (hF (fun r => evalMaj s φ G Φ (r * h) r) hm).ge
    exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun h' =>
      (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun n => enorm_fjAllFun_le s hom hΦ h h' n))

end GlobalTheory.Unf

end
