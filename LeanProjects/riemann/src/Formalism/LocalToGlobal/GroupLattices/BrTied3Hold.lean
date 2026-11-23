import Formalism.LocalToGlobal.GroupLattices.ServJointF
import Formalism.LocalToGlobal.HilbertRowConditions.ColumnsFunctionAtSubspaces

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.L2.DIV Formalism.L2.Indef

noncomputable section

namespace Formalism.L2.G.ServJointF

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

def brOf3 (P : Formalism.L2.Rows.RowSideFamily ex) : ColBrF D where
  Bs := P.A3.fam3.base3
  Df1 := P.A3.side3 P.Ps P.ψs P.Zs
  Dc := P.Dc
  wU := P.I.wU
  eNu := fun u x => P.I.eNu u x
  tup := P.I.tup
  eV := fun t F => P.I.jA t ((rV0 D P.A3.A P.Ps P.ψs t).mulVec F)
  tz := (P.A3.indefDown P.S0).μ

section Gen

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ} {A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m}
  {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G} {ψs : Ps →* D.what₂.LLˣ} {X0 : Formalism.BasicNotions.BaseLevelRowSide D}

theorem brTied_of {Zs : DefSub A3.fam3.amb3} {S0 : IndefData (A3.side3 P0 ψ0 Zs)} {S1 : IndefData (A3.side3 Ps ψs Zs)}
    {Dc : DefCols (A3.side3 Ps ψs Zs)} {Sp : SPer Dc} {C : ColData Dc Sp S1}
    {NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)} {I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc}
    (hT : DivTied3 D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I) (hok : ∃ s : ℕ, A3.A.fam.Ok s)
    (hdc : ∀ (u : D.what₂.Word) (t : A3.fam3.base3.Tup) (x : Fin (Dc.a (I.wU u)) → D.what₂.LL) (F : Fin ((A3.side3 Ps ψs Zs).nV t) → D.what₂.LL),
      D.what₂.embLL (Dc.Pt (I.wU u) t x F) = D.what₂.perCol u (I.tup t) (D.jN u (I.eNu u x)) (I.jA t ((rV0 D A3.A Ps ψs t).mulVec F))) :
    (ColBrF.mk A3.fam3.base3 (A3.side3 Ps ψs Zs) Dc I.wU (fun u x => I.eNu u x) I.tup
      (fun t F => I.jA t ((rV0 D A3.A Ps ψs t).mulVec F)) S1.μ).Tied where
  mu := fun w => by rw [hT.mu1]; exact hT.tup.muAt w
  v0 := fun t F _ => by
    obtain ⟨s0, hOk⟩ := hok
    refine ⟨I.jA t ((rV0 D A3.A Ps ψs t).mulVec F), ?_⟩
    have h1 := (hT.sharp.forms t).op_eq ((rV0 D A3.A Ps ψs t).mulVec F)
    rw [ServJoint.level_operator_fixes_image hOk Ps ψs (A3.fam3.toSub2 Zs) t F] at h1
    exact h1
  gen := fun t F hF => by
    obtain ⟨s0, hOk⟩ := hok
    exact ((hT.sharp.Mtilde t).2 _).1 ((ServJoint.image_mem_nabla_iff hOk Ps ψs (A3.fam3.toSub2 Zs) t F).2 hF)
  dcPt := hdc

end Gen

end Formalism.L2.G.ServJointF

end
