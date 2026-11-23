import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReadPk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeRepresentativesPartsOtherLaterStagesStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinTypRepCast
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

set_option maxHeartbeats 4000000 in

theorem chT_tr : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → ∀ (bb : Bool) (Φ : Type) (rep : Φ → _) (Top : C.Tup → Hs) (c : ChD C.Tup Φ B.R.m Top) jA (t : ChT y F bb rep (Top := Top) jA c) jA', HEq jA' jA → ∃ t' : @ChT b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) bb Φ ((rep)) Top jA' c, letI := alg b iK; HEq t'.jE t.jE ∧ HEq t'.jM t.jM ∧ HEq t'.jX t.jX := by
  intro B C a b G _ _ Pl0 T Ks _ _ iK A R F y y' hS bb Φ rep Top c jA t jA' hjA
  have hP := (GlobalTheory.T.typeRepresentativesParts_otherLaterStages B C a b G Pl0 T Ks A R F y y' hS).2.1
  obtain ⟨htup, htupT, hPY, hPW⟩ := hS
  rcases y' with ⟨tup', tupT', tupT_tup', tup0', hm', hTop', hinj', PY', PW', ιW', isomFin', frameMatch', hF', stdPsi'⟩
  have e1 : tup' = (y.tup) := eq_of_heq ((htup))
  have e2 : tupT' = (y.tupT) := eq_of_heq ((htupT))
  subst e1 e2
  have e3 : jA' = (jA) := eq_of_heq ((hjA))
  subst e3
  have hCC := chain_CC b F y.tupT y.hm y.hTop
  have hCCX := chain_CCX b F y.tupT y.hm y.hTop
  have hCCP := chain_CCP b F y.tupT y.hm y.hTop
  have hCCXP := chain_CCXP b F y.tupT y.hm y.hTop
  have hEEc := chain_EEc b F y.tupT y.hm y.hTop
  letI := alg b iK
  refine ⟨{
    jE := (t.jE)
    jM := (t.jM)
    jX := (t.jX)
    jE_inj := (t.jE_inj)
    jE_range := by
      have e : LinearMap.range t.jE = _ := t.jE_range.trans (congrFun hEEc bb)
      exact (e)
    jE_ip := (t.jE_ip)
    jM_inj := (t.jM_inj)
    jM_range := fun μ hU j h1 h2 => by
      let μa : a.D.what₂.Tup := (μ)
      have hUa : y.Us μa := (hU)
      have h2a : j ≤ a.D.R.m - 1 := (h2)
      have e : LinearMap.range (t.jM μa j) = _ := (t.jM_range μa hUa j h1 h2a).trans (congrFun (congrFun (congrFun hCCP bb) μa) j)
      exact (e)
    jM_ip := (t.jM_ip)
    jX_inj := (t.jX_inj)
    jX_range := fun μ hU => by
      let μa : a.D.what₂.Tup := (μ)
      have hUa : y.Us μa := (hU)
      have e : LinearMap.range (t.jX μa) = _ := (t.jX_range μa hUa).trans (congrFun (congrFun hCCXP bb) μa)
      exact (e)
    jX_ip := (t.jX_ip)
    io0 := fun μ hU x v h => by
      let μa : a.D.what₂.Tup := (μ)
      have hUa : y.Us μa := (hU)
      let va : (c.Mult μa 1).T := (v)
      have e := congrFun (congrFun (congrFun hCC bb) μa) 1
      have h0 : t.jM μa 1 va ∈ (y.C F).CC bb μa 1 := cast (congrArg (t.jM μa 1 va ∈ ·) e.symm) ((h))
      have hv := chain_ioC b (R := R) (y.tupT μa) 0 (t.jM μa 1 va) ((h)) h0
      have e' := (t.io0 μa hUa x va h0).trans (congrArg (fun z => (y.C F).ipE bb (t.jE x) z) hv.symm)
      kexactB e'
    io := fun μ hU j h1 h2 x v h => by
      let μa : a.D.what₂.Tup := (μ)
      have hUa : y.Us μa := (hU)
      have h2a : j + 1 ≤ a.D.R.m - 1 := (h2)
      let va : (c.Mult μa (j + 1)).T := (v)
      have e := congrFun (congrFun (congrFun hCC bb) μa) (j + 1)
      have h0 : t.jM μa (j + 1) va ∈ (y.C F).CC bb μa (j + 1) := cast (congrArg (t.jM μa (j + 1) va ∈ ·) e.symm) ((h))
      have hv := chain_ioC b (R := R) (y.tupT μa) j (t.jM μa (j + 1) va) ((h)) h0
      have e' := (t.io μa hUa j h1 h2a x va h0).trans (congrArg (fun z => (y.C F).ipP bb μa j (t.jM μa j x) z) hv.symm)
      kexactB e'
    ioTop := fun μ hU x v v' hvv h => by
      let μa : a.D.what₂.Tup := (μ)
      have hUa : y.Us μa := (hU)
      let va : (c.Mult μa a.D.R.m).T := (v)
      let va' : (c.Mult μa (a.D.R.m - 1 + 1)).T := (v')
      have hvva : HEq va' va := (hvv)
      have e := congrFun (congrFun hCCX bb) μa
      have h0 : t.jX μa (c.multTop μa va) ∈ (y.C F).CCX bb μa := cast (congrArg (t.jX μa (c.multTop μa va) ∈ ·) e.symm) ((h))
      have hv := chain_ioX b (R := R) y.hm y.hTop (y.tupT μa) (t.jX μa (c.multTop μa va)) ((topMult_tr b y.hTop)) ((h)) h0
      have e' := (t.ioTop μa hUa x va va' hvva h0).trans
        (congrArg (fun z => (y.C F).ipP bb μa (a.D.R.m - 1) (t.jM μa (a.D.R.m - 1) x) z) hv.symm)
      exact (e')
    junk := (t.junk)
    ft := fun π => by
      rw [eq_of_heq (hP bb (rep π))]
      exact (t.ft π)
    disj := fun π π' hne => by
      rw [eq_of_heq (hP bb (rep π)), eq_of_heq (hP bb (rep π'))]
      exact (t.disj π π' hne)
    top := (t.top) }, (HEq.refl t.jE), (HEq.refl t.jM), (HEq.refl t.jX)⟩

end GlobalTheory.Mem.R3.Rw
