import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMulEquivUniformisedPointsUniversalStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowPullbackSecModelUniversalBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaFrameExpansionFramedPointGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalisedPullbackSectionExpandsFamilyStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricLiftActsRootOfUnityOnExpansionsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTranslatedNormalisedPullbackSectionStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GroupExpansionBijectiveOfCompleteDVR
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExpandsGSum
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.OneColTranslate

theorem pow_eq_one_of_act {S : Scheme.{0}} {O : Type} [CommRing O] {G T : Over S} [GrpObj G]
    (a : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O G) (b : T ⟶ G) (α β : O) (N : ℕ) (h : α * β = (N : O))
    (hb : b ≫ a.act β = 1) : b ^ N = 1 := by
  have h0 : a.act 0 = 1 := by
    have h1 := a.add 0 0
    rw [add_zero] at h1
    exact (mul_eq_left.mp h1.symm)
  have hn : ∀ n : ℕ, b ≫ a.act (n : O) = b ^ n := by
    intro n
    induction n with
    | zero => rw [Nat.cast_zero, h0, pow_zero, MonObj.comp_one]
    | succ n ih => rw [Nat.cast_succ, a.add, MonObj.comp_mul, ih, a.one, Category.comp_id, pow_succ]
  haveI := a.hom α
  rw [← hn, ← h, mul_comm, a.mul, ← Category.assoc, hb, MonObj.one_comp]

theorem oneColumn_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (ϖ : T.V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F], letI := io.toAlgebra; letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra; ∀ (φ : T.Fr →ₐ[c.F] F), φ.toRingHom = algebraMap T.Fr F → ∀ (yF : FrPt Xo c F), FrMap φ y yF → ∀ (α : 𝓞 E) (N : ℕ), Odd N → α * star α = (N : 𝓞 E) → ∃ (θ₁ : Fam P.D.toPre F 1) (θα₁ : Fam P.D.toPre F (1 * N)), ThFrame P.D ϖ F θ₁ ∧ PullAl P.D F P.oD α 1 N θ₁ θα₁ ∧ ∀ (p : QkPt P.D.toPre F (1 * N)) (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε (1 * N)))) (ζ : F) (x : TFK (R := T.V) F ⟶ P.A.A) (r₀ r : Fam P.D.toPre F (1 * N)) (σ : P.U.toUnifPre.SecGF F N), w.IsGen → FinOrd P.D F (1 * N) p w ζ → P.ToA F (1 * N) p x → x ≫ P.oA.act (star α) = 1 → PhiRel P.D.toPre F (1 * N) p w θα₁ r₀ → Fam.IsSmul P.D.toPre F ζ r₀ r → P.U.toUnifPre.ExpandsG F N σ (PowGerm.famCast (Dp := P.D.toPre) (F := F) (one_mul N) r) → ∃ (u : F) (b : ptO Xo yF.x ⟶ Xo.univ.t.G) (hh : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (N : ℤ) (ptO Xo yF.x))) (σ₀ : P.U.toUnifPre.SecGF F N), (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧ b ≫ Xo.univ.t.act.act (star α) = 1 ∧ IsTransPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) N yF.s b hh ∧ SecTieF I P F yF.x N σ₀ hh ∧ ∀ jj, σ.f jj = resTop ((LB.LinComb P.U.LG.L (K := Fin 1) (fun _ => UnifPre.gFK (R := T.V) (G := I.G.G) F) (fun _ => (N : ℤ))).U jj) (scal (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left u) * σ₀.f jj := by
  intro E _ _ _ H Dw l Xo c T io y I P ϖ hϖ F _ _ _ φ hφ yF hyF α N hN hα
  letI := H.starRing
  letI := io.toAlgebra
  letI : Algebra c.F F := ((algebraMap T.Fr F).comp io).toAlgebra
  have hLL := GlobalTheory.firstFiveLaws
  have hL : Laws := hLL.1
  have hN1 : 1 ≤ N := hN.pos
  have hx : yF.x = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) := by
    have h1 := hyF.1
    rw [hφ] at h1
    exact h1
  have hbij := GlobalTheory.expandsG_bijective_of_dvr hL hLL.2.1 hLL.2.2.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.1 T.V P.D P.A I.G.G P.U F
  have hsec := GlobalTheory.T.powPullbackSec_modelUniversal_bijective E H Dw l Xo c T io y I P F yF.x hx
  obtain ⟨σs, hσs, -⟩ := (hsec 1).2.1 yF.s
  obtain ⟨θ₁, hθ₁, -⟩ := (hbij 1 le_rfl).1 σs
  obtain ⟨π, -, hπ⟩ := GlobalTheory.PullLin.exists_pull_linearMap hL T.V P.D F (𝓞 E) P.oD H.w0 P.w0 α N 1 hN1 le_rfl hα
  have hpull : PullAl P.D F P.oD α 1 N θ₁ (π θ₁) := (hπ _ _).2 rfl
  refine ⟨θ₁, π θ₁, GlobalTheory.T.thetaFrame_expansion_framedPoint_generator E H Dw l Xo c T io y I P ϖ hϖ F φ hφ yF hyF σs θ₁ hσs hθ₁, hpull, ?_⟩
  intro p w ζ x r₀ r σ hw hfin hto hxk hphi hsm hσ
  obtain ⟨e, he, hea⟩ := GlobalTheory.T.exists_mulEquiv_uniformisedPoints_universal E H Dw l Xo c T io y I P F yF.x hx
  have hb : e x ≫ Xo.univ.t.act.act (star α) = 1 := by rw [← hea, hxk, map_one]
  have hbN : e x ^ N = 1 := pow_eq_one_of_act _ _ α (star α) N hα hb
  obtain ⟨hh, hhh⟩ := GlobalTheory.T.exists_translated_normalisedPullback_section E H Dw l Xo c F yF.x α N hN hα yF.s (e x) hbN
  obtain ⟨h₁, hnp, hsym⟩ := id hhh
  obtain ⟨σ₁, hσ₁, -⟩ := (hsec N).2.1 h₁
  obtain ⟨σ₀, hσ₀, -⟩ := (hsec N).2.1 hh
  have hex₁ := GlobalTheory.T.normalisedPullback_section_expands_family E H Dw l Xo c T io y I P F yF.x hx α N 1 N (_root_.one_mul N) hα hN1 (Or.inl rfl)
    σs yF.s θ₁ σ₁ h₁ (π θ₁) hσs hθ₁ hnp hσ₁ hpull
  have key : ∀ (q : ℕ) (eq : q = N) (θ : Fam P.D.toPre F q) (p : QkPt P.D.toPre F q)
      (w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε q)))
      (r₀ r : Fam P.D.toPre F q),
      P.U.toUnifPre.ExpandsG F N σ₁ (PowGerm.famCast (Dp := P.D.toPre) (F := F) eq θ) →
      w.IsGen → FinOrd P.D F q p w ζ → P.ToA F q p x → PhiRel P.D.toPre F q p w θ r₀ →
      Fam.IsSmul P.D.toPre F ζ r₀ r →
      ∃ (u : F) (t' : Fam P.D.toPre F N), (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧
        Fam.IsSmul P.D.toPre F u (PowGerm.famCast (Dp := P.D.toPre) (F := F) eq r) t' ∧
        P.U.toUnifPre.ExpandsG F N σ₀ t' := by
    intro q eq
    obtain rfl : N = q := eq.symm
    intro θ p w r₀ r hθ hw hfin hto hphi hsm
    exact GlobalTheory.T.symmetric_lift_acts_root_of_unity_on_expansions E H Dw l Xo c T io y I P F yF.x hx N hN1 σ₁ σ₀ h₁ hh θ r₀ r x (e x) p w ζ hσ₁ hσ₀ hθ hsym
      ((he _ _).2 rfl) hto hw hfin hphi hsm
  obtain ⟨u, t', ⟨m, hm, hum⟩, hut, hex₀⟩ := key (1 * N) (one_mul N) (π θ₁) p w r₀ r hex₁ hw hfin hto hphi hsm
  have hu : u ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at hum
    exact zero_ne_one hum
  rw [isSmul_iff] at hut
  let σ' : P.U.toUnifPre.SecGF F N := SecOps.secScale
    (Out.scal (fst (TFK (R := T.V) F) ((Over.pullback (jK T.V)).obj I.G.G)).left u⁻¹) σ₀
  have hex' := GlobalTheory.GroupExpansionLinear.expandsG_sum T.V P.D P.A I.G.G P.U F N 1 (fun _ => u⁻¹) (fun _ => σ₀)
    (fun _ => t') σ' (fun _ => hex₀) (fun jj => by rw [Fin.sum_univ_one]; rfl)
  rw [Fin.sum_univ_one, hut, smul_smul, inv_mul_cancel₀ hu, one_smul] at hex'
  have hσσ : σ = σ' := ((hbij N hN1).2 _).unique hσ hex'
  refine ⟨u⁻¹, e x, hh, σ₀, ⟨m, hm, by rw [inv_pow, hum, inv_one]⟩, hb, hhh, hσ₀, fun jj => ?_⟩
  rw [hσσ]
  rfl

end GlobalTheory.OneColTranslate
