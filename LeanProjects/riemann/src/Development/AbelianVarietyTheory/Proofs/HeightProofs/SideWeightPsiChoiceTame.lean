import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwDatPsiValuesInLL
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WPtFrame
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.PlugPt.sideW_chr : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (𝒮 : Slots) (ν : NRead hL 𝒮) (K : Ctx) (p : WPt 𝒮 K), Formalism.L2.Host.PsiChoiceCompatible (p.w.D p.Z) (sideW ν p).cf p.O.ex.nch (sideW ν p).tp ∧ (∀ v, (p.w.D p.Z).what₂.muAt v ≠ (p.w.D p.Z).what₂.mu0 → ((sideW ν p).tp.psi v).ValuesIn 0 (p.w.D p.Z).what₂.embLL) ∧ GlobalTheory.DimPartsCompare.TameTie (p.w.D p.Z) (sideW ν p).cf.W.om := by
  intro hL 𝒮 ν K p
  refine ⟨p.x.n.chrPsi, ?_, ?_⟩
  · intro v _
    show (p.x.n.tp.psi v).ValuesIn 0 _
    rw [p.x.n.psi]
    exact GlobalTheory.twDat_psi_valuesIn_LL p.B p.T p.x.coh v
  · have h := p.x.what₂.grp
    have hf := (GlobalTheory.Plug.wPt_frame 𝒮 K p).2.1
    show GlobalTheory.DimPartsCompare.TameTie (p.w.D p.Z) (GlobalTheory.Mem.Col2.TC.cf p.w.I p.w.l p.Z).W.om
    rw [hf]
    exact types_of_true (D := p.w.D p.Z) _ h
