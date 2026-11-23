import Formalism.LocalToGlobal.IndefiniteReal.RealRec
import Formalism.LocalRingCardinality.Lemmas
import Formalism.LocalToGlobal.Divisibility.TupUsed

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Module
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx

namespace Formalism.IndefR.LevelRealisationRankEquality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

variable {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem base_rank_eq_of_tied_level (P : RowSideFamily ex) : D.what₂.D0 = P.S0.D := by
  have h1 : finrank D.what₂.LL (Fin P.S0.D → D.what₂.LL) = finrank D.what₂.LL ex.p0.s.RR.V := P.I.eRR0.finrank_eq
  have h2 : finrank D.what₂.LL ex.p0.s.RR.V = Fintype.card ex.p0.s.RR.ι := finrank_eq_card_basis ex.p0.s.RR.b
  have h3 : finrank ℂ D.what₂.EE0 = Fintype.card ex.p0.s.RR.ι :=
    finrank_eq_card_basis (Basis.mk ex.p0.s.jEE_basis.1 (le_of_eq ex.p0.s.jEE_basis.2.symm))
  have h4 : finrank ℂ D.what₂.EE0 = D.what₂.D0 := by
    simpa using finrank_eq_card_basis D.what₂.onb0.toBasis
  rw [finrank_fin_fun] at h1
  omega

theorem D_of_heq {Bs : DefBase D.what₂.LL} {Df Df' : DefSide Bs} (h : Df = Df') {S0 : IndefData Df} {S1 : IndefData Df'}
    (hS : HEq S0 S1) : S0.D = S1.D := by
  subst h
  cases hS
  rfl

theorem base_rank_eq_of_realisation (Q : RealT Rc P Dcf Spf Zscf S Ks) :
    D.what₂.D0 = (P.A3.A.fam.R P.A3.A.fam.μ0).dZ (P.A3.A.fam.lvl P.P0 P.ψ0) (P.Zs.Z P.A3.A.fam.μ0) := by
  have hD := D_of_heq (congrArg (fun Z => P.A3.side3 P.P0 P.ψ0 Z) Q.zs) Q.s0
  have hz : (P.A3.side3 P.P0 P.ψ0 (Q.Rl.toCx3 (faceT P Dcf Spf Zscf)).zs).dQ P.A3.fam3.base3.μ0 =
      (P.A3.side3 P.P0 P.ψ0 P.Zs).dQ P.A3.fam3.base3.μ0 := by rw [Q.zs]
  rw [base_rank_eq_of_tied_level P, ← hD]
  exact hz

theorem mu_of_heq {Bs : DefBase D.what₂.LL} {Df Df' : DefSide Bs} (h : Df = Df') {S0 : IndefData Df} {S1 : IndefData Df'}
    (hS : HEq S0 S1) : S0.μ = S1.μ := by
  subst h
  cases hS
  rfl

theorem mu_eq (Q : RealT Rc P Dcf Spf Zscf S Ks) : Q.Rl.mu = P.S0.μ :=
  mu_of_heq (congrArg (fun Z => P.A3.side3 P.P0 P.ψ0 Z) Q.zs) Q.s0

theorem tupAllUsed_of_real (Q : RealT Rc P Dcf Spf Zscf S Ks) : TupAllUsed P := by
  apply tupAllUsed_of_cover
  intro t
  rcases Q.charW.tup.mu_used t with h | ⟨w, h⟩
  · exact Or.inl h
  · refine Or.inr ⟨D.plEq.symm w, ?_⟩
    show t = P.S0.μ (D.plEq (D.plEq.symm w))
    rw [← mu_eq Q, Equiv.apply_symm_apply]
    exact h.symm

end Formalism.IndefR.LevelRealisationRankEquality

end
