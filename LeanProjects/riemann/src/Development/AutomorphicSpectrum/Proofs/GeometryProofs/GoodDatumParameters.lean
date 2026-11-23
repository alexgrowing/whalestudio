import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.GenFrExAndGenFromTest
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsBijectiveKappa
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntAll
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntFrExtOfGoodLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NumberFieldFinitePlaceCompletionEmbedding
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ModuliExistsNumberFieldPointStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspOnRestrict
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CardLower
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug

namespace VsLaws

section Laws

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem idem_val (h : GenFrEx Xo c) (Z : Comp Xo c) :
    evC h Z (GlobalTheory.FlatLine.idem Z) = 1 ∧ ∀ Z', Z' ≠ Z → evC h Z' (GlobalTheory.FlatLine.idem Z) = 0 := by
  obtain ⟨hL, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  exact ⟨GlobalTheory.FlatLine.evR_idem (GlobalTheory.AllWt.liesOn_genFr h Z) (hL.test _ _),
    fun Z' hZ => GlobalTheory.AllWt.evC_eq_zero h hZ (GlobalTheory.FlatLine.idem_mem_suppOn Z)⟩

theorem compLaws_of (hN : N1ab) (hN' : N1c) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (hpq : 1 ≤ Dw.p + Dw.q) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (hF : FnAlgClosed Xo c)
    (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (hT : ∀ σ, GoodEmb c σ → ∀ k x,
      FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((U σ).un k x))
    (hC : ∀ σ, GoodEmb c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (laU (U σ) a n k) γ = 1) :
    ∃ h e', CompLaws U h e' := by
  obtain ⟨h, hgt⟩ := GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c
  have hB := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hTw := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  obtain ⟨κ, hb, -⟩ := GlobalTheory.CompBij.exists_bijection (U c.F.val.toRingHom) rfl (hU _ rfl) hF h
  refine ⟨h, GlobalTheory.FlatLine.idem, ?_⟩
  exact
    { comps := by
        rw [Nat.card_congr (Equiv.ofBijective κ hb), Nat.card_eq_fintype_card]
      ne := (GlobalTheory.Exist.comp_nonempty_finite_genFr_trdeg E H Dw l Xo c hpq).1
      genT := hgt h
      evalWD := GlobalTheory.TransferCompare.evalWD_framed _ _
      unf := hU
      unTest := hT
      chiTriv := hC
      ptNe := intFrNe_of' (GlobalTheory.T.xoNumPt_of_p_add_q_pos hN' E H Dw l Xo c hpq) GlobalTheory.locFld
        (GlobalTheory.Exist.intFrExt_of_good GlobalTheory.partI_closed hN hB hTw E H Dw l Xo c hpq hg)
      intAll := GlobalTheory.IntegralFrames.intAll GlobalTheory.partI_closed hN hB hTw E H Dw l Xo c hpq hg
      e_sec := GlobalTheory.CompRestr.idem_mem_sec
      e_val := idem_val h }

end Laws

theorem lval_congr {n m : ℕ} (h : n = m) (hn : Fact n.Prime) (hm : Fact m.Prime) (zn : NeZero n) (zm : NeZero m) :
    (deriv (DirichletCharacter.LFunction
        (((quadraticChar (ZMod n)).ringHomComp (Int.castRingHom ℂ)) : DirichletCharacter ℂ n)) 1 /
      DirichletCharacter.LFunction
        (((quadraticChar (ZMod n)).ringHomComp (Int.castRingHom ℂ)) : DirichletCharacter ℂ n) 1).re =
    (deriv (DirichletCharacter.LFunction
        (((quadraticChar (ZMod m)).ringHomComp (Int.castRingHom ℂ)) : DirichletCharacter ℂ m)) 1 /
      DirichletCharacter.LFunction
        (((quadraticChar (ZMod m)).ringHomComp (Int.castRingHom ℂ)) : DirichletCharacter ℂ m) 1).re := by
  subst h
  rfl

theorem hostLval_eq (D : D7) (Q : Par D) (h : Q.H.d = D.host.d) : hostLval Q.H = dlogL D 1 :=
  lval_congr h ⟨Q.H.d_prime⟩ ⟨D.host.hyp.2.1⟩ ⟨Q.H.d_prime.ne_zero⟩ ⟨D.host.hyp.2.1.ne_zero⟩

end VsLaws

theorem vs_laws : Top.Given → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ j → j < D.R.m → ∀ (Y : GlobalTheory.CovTop.Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → (∃ h e', CompLaws Y.U h e') ∧ (∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p) ∧ (T.Q.Dw j).q = D.R.m - j ∧ (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r ∧ Fintype.card (CMType T.Q.H) = D.R.f ∧ hostRd D.host.E = D.host.rdE ∧ hostLval T.Q.H = dlogL D 1 := by
  intro hG D T hT j hj1 hjm Y e o hY
  obtain ⟨⟨-, hN, hN', -⟩, -⟩ := hG
  have hI : InR D j := ⟨hj1, hjm.le⟩
  obtain ⟨hH, hLv, -, hD⟩ := hT.pins
  obtain ⟨hp, hq, -⟩ := hD j hI
  have hpq : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [hp, hq]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have hg0 : ∀ p : ℕ, p.Prime → T.Q.l.GoodAt p :=
    goodAt_of_two_primes hLv.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  have hg : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p := GlobalTheory.LawsDeep.goodAt_of_mul _ _ _ hY.lev.1.2.1 hg0
  have hr1 : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    rw [hpq]
    simp only [Ranks.r]
    omega
  refine ⟨VsLaws.compLaws_of hN hN' Y.U hr1 hg hY.geo hY.unf hY.unTest hY.chiTriv, hg, hq, hpq, ?_, rfl,
    VsLaws.hostLval_eq D T.Q hH.1⟩
  convert SharpLaws.card_psi D T.Q

end GlobalTheory.CompanionTheory.Ar.Plug
