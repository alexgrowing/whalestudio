import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGermLinearMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFramesEL
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GermBoxProductEqProdGerms
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowEqOneOfMultilinear
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsBoxFamilyMultilinearMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProdPullZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsBoxQkToA
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxSec
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.FinOrdExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ClosedPointWeilPower
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaFrameFamiliesDifferByValuationZeroUnitStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DvdOfPullEqZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FiniteOrderThetaOperatorsRatioRootOfUnityStatement

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.ColumnSplit

theorem val_eq_zero_of_pow_eq_one {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) {u : F} {m : ℕ} (hm : 0 < m)
    (h : u ^ m = 1) : v u = 0 := by
  have h1 : m • v u = 0 := by rw [← AddValuation.map_pow, h, AddValuation.map_one]
  induction hv : v u using WithTop.recTopCoe with
  | top =>
    rw [hv] at h1
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    simp [succ_nsmul] at h1
  | coe a =>
    rw [hv, ← WithTop.coe_nsmul, WithTop.coe_eq_zero] at h1
    simpa [hm.ne'] using h1

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U) [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)), (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) → (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → ∀ τ : Frames P.U.LG.L (κ := Fin 1 × Fin (chD C.ch)) C.xT, τ.Gen → IsEL P C.xT C.actT C.eT C.wPT τ → ∀ (α : 𝓞 E) (N : ℕ), 1 ≤ N → α * star α = (N : 𝓞 E) → ∀ (θ₁ : Fam P.D.toPre F 1) (θα₁ : Fam P.D.toPre F (1 * N)), ThFrame P.D ϖ F θ₁ → PullAl P.D F P.oD α 1 N θ₁ θα₁ → ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), ThFrame D' ϖ F θ → PullAl D' F oD' α 1 N θ θα → ∀ (p : QkPt D'.toPre F (1 * N)) (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (1 * N)))) (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (1 * N)) (q : ℕ) (e : 1 * N = q) (σ' : U'.toUnifPre.SecGF F q) (h : PS F n (chD C.ch)), w.IsGen → ζ ≠ 0 → FinOrd D' F (1 * N) p w ζ → QkToAkU U'.toUnifPre F (1 * N) p x → PhiRel D'.toPre F (1 * N) p w θα t₀ → Fam.IsSmul D'.toPre F ζ t₀ t → U'.toUnifPre.ExpandsG F q σ' (PowGerm.famCast (Dp := D'.toPre) (F := F) e t) → IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F q σ' h → ∃ (u : F) (p₁ : Fin n → QkPt P.D.toPre F (1 * N)) (w₁ : ∀ i, LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p₁ i).g.b) (DegPre.lineε (1 * N)))) (ζ₁ : Fin n → F) (r₀ r : Fin n → Fam P.D.toPre F (1 * N)) (σ₁ : Fin n → P.U.toUnifPre.SecGF F q) (f : Fin n → PS F 1 (chD C.ch)), v u = 0 ∧ h = u • boxSer f ∧ ∀ i, (w₁ i).IsGen ∧ FinOrd P.D F (1 * N) (p₁ i) (w₁ i) (ζ₁ i) ∧ P.ToA F (1 * N) (p₁ i) (x ≫ pA.pr i) ∧ PhiRel P.D.toPre F (1 * N) (p₁ i) (w₁ i) θα₁ (r₀ i) ∧ Fam.IsSmul P.D.toPre F (ζ₁ i) (r₀ i) (r i) ∧ P.U.toUnifPre.ExpandsG F q (σ₁ i) (PowGerm.famCast (Dp := P.D.toPre) (F := F) e (r i)) ∧ GermA P.U.toUnifPre (κ := Fin 1 × Fin (chD C.ch)) C.xT τ F q (σ₁ i) (f i) := by
  obtain ⟨hL, hL2, -, hL4, -⟩ := GlobalTheory.firstFiveLaws
  have hT := GlobalTheory.twistBaseChange_and_valuation_statements.1
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y C hTr P hTor _ ϖ hϖ Q _ F _ _ _ _ _ _ v hv n D' A' G' _ _ pD pA pG U' PU _ oD' hx hact τ hτ hEL
    α N hN hα θ₁ θα₁ hθ₁ hθα₁ θ θα hθ hθα p w ζ x t₀ t q e σ' h hw _ hfin hpx hΦt hsm hexp hgerm
  subst e
  have hG := hL.globalFns
  have hk : 1 ≤ 1 * N := by omega
  haveI : CharZero T.V := (algebraMap T.V F).charZero
  obtain ⟨p₁, hp, hp₁⟩ := UnboxQk.exists_isBoxQk_toA hL hL2 hL4 hT T.V E H C.I.G P hTor n D' A' G' pD pA pG U' PU F
    (1 * N) hk p
  have hw₁ : ∀ i, ∃ w₁ : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p₁ i).g.b)
      (DegPre.lineε (1 * N))), w₁.IsGen := fun i =>
    H1.ClosedPointWeilPower.gen_local_linComb P.D.toPre.P.L P.D.toPre.P.isLB _ _
  choose w₁ hw₁ using hw₁
  choose ζ₁ _ hζ₁ using fun i => H1.finOrdExists_of (phiFun_of hL) (H1.phiPow_of hL) T.V P.D F (1 * N) hk (p₁ i) (w₁ i)
    (hw₁ i)
  choose Φ₁ hΦ₁ using fun i => phiFun_of hL T.V _ P.D F (1 * N) hk (p₁ i) (w₁ i) (hw₁ i)
  obtain ⟨τ₀, hτ₀, hEL₀, hT₀⟩ := frame1St_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT
    C.wPT C.chartT C.frameT C.primT
  have hLB : P.U.LG.L.IsLB := (congrArg RigLB.L P.bundle).symm ▸ C.I.G.PP.isLB
  obtain rfl : τ = τ₀ := funext fun m => TorusExt.gen_ext_val hLB (hτ m) (hτ₀ m) fun y J hJ =>
    (hEL m y J hJ).trans (hEL₀ m y J hJ).symm
  have hz₁ := GlobalTheory.T.universal_statement E H Dw l Xo c T io y C
  obtain ⟨gm₁, -, hgm₁⟩ := PairingLinear.exists_germ_linearMap hL hL2 hL4 hT T.V P.D P.A C.I.G.G P.U _ _ hz₁ τ hτ
    (hT₀ hTr) F (1 * N) hk
  choose σ₁ hσ₁ hf using fun i => hgm₁ (ζ₁ i • Φ₁ i θα₁)
  obtain ⟨bx₁, hbx₁⟩ := exists_boxFam_multilinear hG T.V n P.D.toPre D'.toPre pD F 1
  obtain ⟨bx, hbx⟩ := exists_boxFam_multilinear hG T.V n P.D.toPre D'.toPre pD F (1 * N)
  obtain ⟨u₀, hu₀, hθu⟩ := GlobalTheory.T.thetaFrameFamilies_differ_by_valuationZero_unit T.V ϖ hϖ D' F v hv _ θ
    (BoxFrame.main T.V ϖ hϖ n P.D D' pD F θ₁ _ hθ₁ ((hbx₁ _ _).2 rfl)) hθ
  have hw0 : TraceFormTwistIso D'.toPre oD' H.w0 := GlobalTheory.PsiWZeroProd.main T.V n P.D.toPre D'.toPre pD (𝓞 E)
    (fun a x => funext fun i => hx a x i) P.oD oD' hact H.w0 P.w0
  obtain ⟨pl, -, hpl⟩ := PullLin.exists_pull_linearMap hL T.V D' F (𝓞 E) oD' H.w0 hw0 α N 1 hN le_rfl hα
  have hpull := BoxPull.main hL hL2 hL4 hT T.V n P.D D' pD F (𝓞 E) hx P.oD oD' hact α N 1 hN le_rfl hα
    (fun _ => θ₁) (fun _ => θα₁) _ _ (fun _ => hθα₁) ((hbx₁ _ _).2 rfl) ((hbx _ _).2 rfl)
  have hθα' : θα = u₀ • bx fun _ => θα₁ := by
    rw [(hpl _ _).1 hθα, (hpl _ _).1 hpull, (isSmul_iff _ _ _).1 hθu, map_smul]
  obtain ⟨w', hw', hΦ⟩ := BoxPhi.phiRel_box hG T.V n P.D.toPre D'.toPre pD F (1 * N) p p₁ hp w₁ hw₁
  have hfin' := finOrd_box hL hL2 hL4 hT T.V n P.D D' pD F (1 * N) hk p p₁ hp w₁ w' hw₁ hw' hΦ ζ₁ hζ₁
  obtain ⟨u₁, ⟨m, hm, hum⟩, hu₁⟩ := GlobalTheory.T.finiteOrder_thetaOperators_ratio_rootOfUnity T.V ϖ hϖ D' F (1 * N) hk p w' w (∏ i, ζ₁ i) ζ hw' hw hfin' hfin
  obtain ⟨Φ', hΦ'⟩ := phiFun_of hL T.V _ D' F (1 * N) hk p w' hw'
  have hbΦ : bx (fun i => Φ₁ i θα₁) = Φ' (bx fun _ => θα₁) :=
    (hΦ' _ _).1 (hΦ _ _ _ _ (fun i => (hΦ₁ i _ _).2 rfl) ((hbx _ _).2 rfl) ((hbx _ _).2 rfl))
  have ht : t = (u₁ * u₀) • bx fun i => ζ₁ i • Φ₁ i θα₁ := by
    rw [(isSmul_iff _ _ _).1 (hu₁ θα _ _ t₀ t ((hΦ' _ _).2 rfl) ((isSmul_iff _ _ _).2 rfl) hΦt hsm), hθα', map_smul,
      MultilinearMap.map_smul_univ, hbΦ, smul_comm (∏ i, ζ₁ i) u₀, smul_smul]
  obtain ⟨τn, hτn, hτT, hiff⟩ := frameNSt_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT
    C.wPT C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  have hz := GlobalTheory.T.universalJets_power_product T.V C.I.G.G G' n _ pG C.xT hz₁
  obtain ⟨gm, hgm, hgmex⟩ := PairingLinear.exists_germ_linearMap hL hL2 hL4 hT T.V D' A' G' U' _ _ hz τn hτn (hτT hTr)
    F (1 * N) hk
  obtain ⟨σb, hσb, -⟩ := hgmex (bx fun i => ζ₁ i • Φ₁ i θα₁)
  have hbox := boxGermSt_holds hL hL2 hL4 hT E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT
    C.eT C.wPT C.chartT C.frameT C.primT τ hτ hEL n D' A' G' pD pA pG U' PU F (1 * N) hk σ₁ _ _ σb _
    (fun i => ⟨hσ₁ i, hf i⟩) ((hbx _ _).2 rfl) hσb
  refine ⟨u₁ * u₀, p₁, w₁, ζ₁, fun i => Φ₁ i θα₁, fun i => ζ₁ i • Φ₁ i θα₁, σ₁, fun i => gm₁ (ζ₁ i • Φ₁ i θα₁), ?_, ?_,
    fun i => ⟨hw₁ i, hζ₁ i, hp₁ x hpx i, (hΦ₁ i _ _).2 rfl, (isSmul_iff _ _ _).2 rfl, hσ₁ i, hf i⟩⟩
  · rw [AddValuation.map_mul, hu₀, val_eq_zero_of_pow_eq_one v hm hum, add_zero]
  · rw [hgm t σ' h hexp ((hiff F _ σ' h).1 hgerm), hgm _ σb _ hσb ((hiff F _ σb _).1 hbox), ht, map_smul]

end GlobalTheory.ColumnSplit
