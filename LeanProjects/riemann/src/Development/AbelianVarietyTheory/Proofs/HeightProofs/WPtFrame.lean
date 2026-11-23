import Development.AbelianVarietyTheory.Definitions.HeightFunctions.RunsAlong
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Plug
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Plug.wPt_frame : ∀ (𝒮 : Slots) (K : Ctx) (p : WPt 𝒮 K), p.x.what₂.r.z.R.C = Fr.at (p.w.st p.Z) p.f ∧ GlobalTheory.Mem.Col2.TC.cf p.w.I p.w.l p.Z = Fr.at (p.w.st p.Z) p.f ∧ ∃ μ0, p.x.what₂.r.z.R.toRealDat.toLevCh.Is μ0 := by
  intro 𝒮 K p
  have hC : Fr.at (p.w.st p.Z) p.w.I.C = Fr.at (p.w.st p.Z) p.f := congrArg (Fr.at (p.w.st p.Z)) p.w.C_eq
  refine ⟨?_, ?_, ⟨_, p.x.what₂.r.z.lev.is⟩⟩
  · exact p.x.what₂.r.z.lev.C.trans hC
  · exact (rfl : GlobalTheory.Mem.Col2.TC.cf p.w.I p.w.l p.Z = Fr.at (p.w.st p.Z) p.w.I.C).trans hC
