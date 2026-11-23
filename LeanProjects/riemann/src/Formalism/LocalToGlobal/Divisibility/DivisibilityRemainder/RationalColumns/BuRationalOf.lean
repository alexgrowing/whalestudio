import Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.RationalColumns.ColFacts
import Formalism.LocalToGlobal.Divisibility.TupUsed

noncomputable section

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

namespace Formalism.L2.DIV.RatFullPt

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

theorem rrFull_of (P : RowSideFamily ex) (hF : ColFacts P.S1 P.C)
    (hR : DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I) : D.RRFull := by
  have hlat := hF.rr_lattice
  have hlat' : Submodule.IsLattice D.what₂.LL (P.A3.indefDown P.S1).RR := hlat
  have hL : D.div.RR.L = (P.A3.indefDown P.S1).RR.map (P.I.eRR.toLinearMap.restrictScalars (𝓞 D.what₂.LL)) :=
    hR.sharpRR.lat
  refine ⟨by rw [hL]; exact hlat'.fg.map _, ?_⟩
  have hset : (D.div.RR.L : Set D.div.RR.V) = P.I.eRR.toLinearMap '' ((P.A3.indefDown P.S1).RR : Set _) := by
    rw [hL, Submodule.map_coe]; rfl
  rw [hset, Submodule.span_image, hlat'.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact P.I.eRR.surjective

theorem buRational_of (P : RowSideFamily ex) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hF : ColFacts P.S1 P.C)
    (hR : DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I) (hPt : RowsHoldDcPt3 P)
    (hBu : Rows.BuDefQ D.what₂) : D.BuRational := by
  intro u φ x
  obtain ⟨x', rfl⟩ := (P.I.eNu u).surjective φ
  obtain ⟨y, rfl⟩ := P.I.eRR.surjective x
  rw [hBu, hR.colsBk u x' y]
  have hform := P.tied.div.sharp.forms P.A3.A.μ0
  refine PerDescent.per_sec D u (D.jN u (P.I.eNu u x')) (P.I.tup P.A3.A.μ0) P.tied.div.tup.mu0
    (fun F => P.I.jA P.A3.A.μ0 ((rV0 D P.A3.A P.Ps P.ψs P.A3.A.μ0).mulVec F)) P.I.eRR
    (fun F => (P.S1.ι P.A3.A.μ0).mulVec (((P.A3.side3 P.Ps P.ψs P.Zs).Pq P.A3.A.μ0).mulVec F))
    (P.C.B (P.I.wU u) x') ?_ ?_ ?_ ?_ y
  · exact (hF.bij _).2.comp (hF.wf.Pq_surj _)
  · exact range_op_eq_span hform _ (fun z => lvlOp_range _ _ _ _ _ z)
      (fun F => Formalism.L2.G.ServJoint.level_operator_fixes_image hOk.ok2 P.Ps P.ψs (P.A3.fam3.toSub2 P.Zs) P.A3.A.μ0 F)
  · intro F
    have h := P.tied.div.sharp.iota P.A3.A.μ0 F
    rw [Formalism.MainNotions.AbsolutelyIrreducibleSpan.sharp_iota] at h
    exact h
  · intro F
    have h1 : P.Dc.Pt (P.I.wU u) P.A3.A.μ0 x' F = P.C.ζ (P.I.wU u) P.A3.A.μ0 * P.C.B (P.I.wU u) x'
        ((P.S1.ι P.A3.A.μ0).mulVec (((P.A3.side3 P.Ps P.ψs P.Zs).Pq P.A3.A.μ0).mulVec F)) := hF.l1b.1 _ _ _ _
    have h2 : P.C.ζ (P.I.wU u) P.A3.A.μ0 = 1 := hF.l1b.2.1 _
    rw [h2, one_mul] at h1
    exact (hPt u P.A3.A.μ0 x' F).symm.trans (congrArg D.what₂.embLL h1)

end Formalism.L2.DIV.RatFullPt

end
