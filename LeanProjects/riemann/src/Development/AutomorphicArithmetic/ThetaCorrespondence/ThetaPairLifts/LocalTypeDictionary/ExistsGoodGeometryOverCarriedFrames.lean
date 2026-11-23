import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramesForTriangleStage
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.exists_good_geometry_over_carried_frames : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW) (lam : T → ℂ) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), GlobalTheory.SqTower.IsStageC W i j p q X →
      Factor X W.ψ W.θ lam → GlobalTheory.SqStepBig.Fit G W i j t μ₀ Bs A.rank A'.rank →
      ∃ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank A'.rank),
        GlobalTheory.SqStepBig.Over X Γ ∧ Γ.p = p ∧ Γ.q = q ∧ Γ.IsGood Bs ∧
        ∀ s, (s = t ∨ s = μ₀) → GlobalTheory.SqStepBig.Carried G W i j X Bs FA FA' FW Γ s := by
  intro _
  refine GlobalTheory.SqStepBig.gbig_two GlobalTheory.T.towerStage_seesawDictionary_framesSignatures GlobalTheory.T.towerStage_seesawDictionary_framesSignatures ?_
  intro D T Lc sc G μ₀ C x b q1 _ W _ i j p q A A' WW X lam t Bs hX _ hB
  obtain ⟨FA, FA', FW, a, b, -, -, -, hd⟩ := q1 W i j p q A A' WW X hX
  obtain ⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXi⟩ := hX
  obtain ⟨⟨hψ, -⟩, hBs, hemb, -, -, hκ⟩ := hB
  have hsz := GlobalTheory.StageDict.stage_sizes i j hp hq hrA hrA'
  obtain ⟨Γ, hp', hq', hg, hS⟩ := UpperTheory.exists_geo_of_signature_rank_bounds D W.ψ T A A' WW X FA FA' FW hXi.rank Bs p q hBs hψ hemb hXi.rigA hXi.rigA' hXi.rigW
    hXi.meas hXi.meas' hnA hnA' hnW hsz.1 hsz.2.1 hsz.2.2.1 hκ
  refine ⟨FA, FA', FW, Γ, ⟨⟨rfl, hS.JA, hS.latA.1⟩, ⟨rfl, hS.JB, hS.latB.1⟩, ⟨hXi.rank.symm, hS.pairA.JW, hS.latA.2⟩⟩,
    hp', hq', hg, fun s _ => ?_⟩
  obtain ⟨-, -, f1, f2, k1, k2⟩ := hd s
  refine ⟨f1, f2, k1, k2, fun om om' hT => ?_⟩
  obtain ⟨cA, cB, hO, -⟩ := UpperTheory.exists_seesaw_intertwiners_of_triple D W.ψ W.θ hXi.isVac.2.inf T A A' WW X FA FA' FW hXi.rank Bs Γ hS
    (GlobalTheory.SqStep.chs G i j s) om om' hT (X.ω s) (X.ω' s) (hXi.weil s) (hXi.weil' s)
  exact ⟨_, cA, cB, hO⟩
end
