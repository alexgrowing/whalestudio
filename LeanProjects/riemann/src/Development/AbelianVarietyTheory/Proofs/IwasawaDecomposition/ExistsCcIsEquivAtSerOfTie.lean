import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsSpanOfOnto
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCuspIsThClsDOfPre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidualCharacterDetValuesMemCoeffField
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ActLevAndActBC

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealGeo.PhaseOne

open GlobalTheory.PhaseRationalDegenerate GlobalTheory.AdTh GlobalTheory.PtId GlobalTheory.OneMapTuples

theorem lieFac_eq_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) {x : ℝ}
    (hx : 0 < x) (a : (E →+* ℂ) × ℕ → ℕ) : lieFac Dw x a = (Real.sqrt (2 * Real.pi * x))⁻¹ ^ GlobalTheory.PtId.degW Dw a := by
  have h : 0 < 2 * Real.pi * x := by positivity
  have e : (Real.sqrt (2 * Real.pi * x))⁻¹ = Real.exp (-(1 / 2) * Real.log (2 * Real.pi * x)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos h, ← Real.exp_neg]
    congr 1
    ring
  rw [e, ← Real.exp_nat_mul, lieFac, GlobalTheory.PtId.degW]
  congr 1
  push_cast
  ring

theorem shape {c s l k m r : ℂ} (hc : c ≠ 0) : s * l * k * (m * r) = c * (c⁻¹ * s * k * l * m * r) := by
  field_simp

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Rat

variable {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : (R.MW i (sg0 D A)).Vec)
  (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ)

end Rat

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

theorem wt_n (hT : TieIn T R κ v₀) (i : Fin D.R.m) : (κ i).n = (Vc D i).rank :=
  (hT.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm

theorem fieldRange_le (O : OMDat T.toCore R i Tp tup)
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) :
    D.what₂.embLL.toRatAlgHom.fieldRange ≤ O.c'.F := by
  rintro _ ⟨a, rfl⟩
  have h : ((O.jL a : O.c'.F) : ℂ) = D.what₂.embLL a := RingHom.congr_fun hP.lift.field a
  show D.what₂.embLL a ∈ O.c'.F
  exact h ▸ (O.jL a).2

set_option maxHeartbeats 1000000 in

theorem tieC_of_serOf (hR : PreChar R) (hT : TieIn T R κ v₀) (O : OMDat T.toCore R i Tp tup)
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) {cc : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ}
    (hs : SerOf O (κ i) (v₀ i (sg0 D A)) cc 1) :
    OneMapTieC O.hle D.what₂.embLL.toRatAlgHom.fieldRange (T.U ((i : ℕ) + 1)) (inC O.c') (Wc D i) O.dict O.mu (xiR D) (wtA (κ i))
      (actLev T.Q.c O.lev2) (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io O.thAd O.Plc cc 1 :=
  ⟨fieldRange_le O hP, (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).2 _ _,
    (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hP.act.1).2,
    oneMapRow_of_serOf_ofPre D G Pl0 T0 A T R κ v₀ hR hT i Tp tup O hP cc hs
      (GlobalTheory.ClassSumRule.exists_cusp_isThClsD_ofPre GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T R κ v₀ hR hT i Tp tup O hP)⟩

end GlobalTheory.RealGeo.PhaseOne

namespace GlobalTheory.RealGeo

open GlobalTheory.AdTh GlobalTheory.PtId GlobalTheory.OneMapTuples PhaseOne

set_option maxHeartbeats 2000000 in

theorem exists_scalar_serOf {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (hC : PreChar R) (hT : TieIn T R κ v₀) (hio : IoExt R)
    (i : Fin D.R.m) (c0L : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) :
    ∃ s : ℂ, ‖s‖ = 1 ∧ ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup),
      O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → CoefficientBaseChange R i O.jL (inC O.c') c0L O.c0' →
      ∀ c0 : ℂ, ‖c0‖ = 1 → XiConst O (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) c0 →
      ∀ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0)
        (R.ωP i A.μ0) (R.vacP i) cc → SerOf O (κ i) (v₀ i (sg0 D A)) ((c0⁻¹ * s) • cc) 1 := by
  by_cases hex : ∃ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup),
    O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)
  swap
  · exact ⟨1, norm_one, fun Tp tup O hP => absurd ⟨Tp, tup, O, hP⟩ hex⟩
  obtain ⟨Tp₀, tup₀, O₀, hP₀⟩ := hex
  obtain ⟨ka, hka1, hka⟩ := OneScalar.exists_scalar_ofPre D G Pl0 T0 A T R κ v₀ hC hT hio i c0L
  have hs₀ : O₀.s0 = T.toCore.σ₀ := sOv_eq _ _ _
  obtain ⟨hemb, hiso, -⟩ := dict_cast T hT.laws _ (inR i) O₀.s0 (hs₀ ▸ T.toCore.good_σ₀) (Wc D i) O₀.hV (rank_Wc i)
  obtain ⟨δ, hδ⟩ := ShortSeries.thetaKO_eq_short_series_ofPre D G Pl0 T0 A _ R hC i hP₀.lift.std _ _ (iotaW T i) hemb hiso
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = ka * (((δ : ℤ) : ℂ) ^ GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) *
    (-1) ^ GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) := ⟨_, rfl⟩
  have hs1 : ‖s‖ = 1 := by
    rcases Int.units_eq_one_or δ with h | h <;> simp [hs, h, hka1]
  have hx : 0 < xiR D := norm_pos_iff.2 ((_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have hcm : cmpConst D ka δ (GlobalTheory.PtId.degW (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i))) =
      s * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) := by
    rw [lieFac_eq_pow _ hx, hs, cmpConst]
    simp only [Complex.ofReal_pow, Complex.ofReal_inv]
    ring
  refine ⟨s, hs1, fun Tp tup O hP hbc c0 h0 hxi cc hcc => ?_⟩
  have hne : c0 ≠ 0 := norm_ne_zero_iff.1 (h0 ▸ one_ne_zero)
  refine ⟨fun k => ?_, norm_one, fun t h J' hR y x hx f _ hf g => ?_⟩
  · show ‖c0⁻¹ * s * cc k‖ = 1
    rw [norm_mul, norm_mul, norm_inv, h0, hs1, hcc.1 k]
    norm_num
  · have h2 := exact_identity_ofPre hC hT O hP (hka Tp tup O hP hbc) hδ
      (covAt_of_xiConst_ofPre D G Pl0 T0 A T R κ v₀ hC hT i Tp tup O hP c0 hxi) hcc t h J' hR y x hx f hf g
    rw [hcm] at h2
    refine mul_left_cancel₀ hne ((congrArg _ (one_mul _)).trans (h2.trans ?_))
    exact shape hne

set_option maxHeartbeats 1000000 in

theorem exists_serOf_of_ccIs : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), PreChar R → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc → ∃ u : ℂ, ‖u‖ = 1 ∧ SerOf O (κ i) (v₀ i (sg0 D A)) (u • cc) 1 := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hC hT hio i Tp tup O hP cc hcc
  obtain ⟨_, _, c0L, -, hbc⟩ := hP.lift.c0
  obtain ⟨c0, ⟨m, hm, hr⟩, hxi⟩ := hP.cxi
  have h0 : ‖c0‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hr hm.ne'
  obtain ⟨s, hs1, hs⟩ := exists_scalar_serOf hC hT hio i (c0L i)
  refine ⟨c0⁻¹ * s, ?_, hs Tp tup O hP hbc c0 h0 hxi cc hcc⟩
  rw [norm_mul, norm_inv, h0, hs1]
  norm_num

set_option maxHeartbeats 1000000 in

theorem exists_ccIs_equivAt_serOf_tie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), PreChar R → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ cc, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) O.s0) O.dict O.mu (T.x₀ ((i : ℕ) + 1) O.s0) (R.ωP i A.μ0) (R.vacP i) cc ∧ ∃ u : ℂ, ‖u‖ = 1 ∧ O.EquivAt (κ i) (u • cc) ∧ SerOf O (κ i) (v₀ i (sg0 D A)) (u • cc) 1 ∧ OneMapTieC O.hle D.what₂.embLL.toRatAlgHom.fieldRange (T.U ((i : ℕ) + 1)) (inC O.c') (Wc D i) O.dict O.mu (xiR D) (wtA (κ i)) (actLev T.Q.c O.lev2) (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io O.thAd O.Plc (u • cc) 1 := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hC hT hio i Tp tup O hP
  obtain ⟨cc, hcc⟩ := CcEx.exists_ccIs_ofPre GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T R κ v₀ hC hT i Tp tup O hP
  obtain ⟨u, hu, hS⟩ := exists_serOf_of_ccIs D G Pl0 T0 A T R κ v₀ hC hT hio i Tp tup O hP cc hcc
  exact ⟨cc, hcc, u, hu,
    GlobalTheory.FrameConstMove.equivAt_of_ccIs_ofPre GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T R κ v₀ hC hT i Tp tup O hP cc hcc u, hS,
    tieC_of_serOf hC hT O hP hS⟩

end GlobalTheory.RealGeo
