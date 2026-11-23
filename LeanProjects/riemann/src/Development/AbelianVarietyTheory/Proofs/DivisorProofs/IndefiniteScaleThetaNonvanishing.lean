import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.IndefiniteReal.RealPins
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRowPlacementFiniteElementMatchesLevelsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StarCoeffOfEqReverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarCoeffEisensteinSeriesReversePolyStatement
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowPlacementReal

theorem placement_of_realisation : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : Formalism.L2.RecT ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : RealT Rc P Dcf Spf Zscf S Ks), RealPins Q → (∀ x : S.X.B.I.E, HEq (S.X.ιE x) x) → SeeEx Q := by
  intro hDS D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S Ks _ _ _ Q hP hE
  have hE0 : Formalism.L2.SG.RowDict.IdempotentRealFixed D := by
    have key : ∀ {g : ℕ} [Fact g.Prime] {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod g)} (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) C), Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O → ∀ (r : ℕ) (f : Polynomial (ZMod g)), f.Monic → f.coeff 0 ≠ 0 → ∀ x, star ((Formalism.L2.NT.eSerO O r f).coeff x) = (Formalism.L2.NT.eSerO O r (Polynomial.C (f.coeff 0)⁻¹ * f.reverse)).coeff x := GlobalTheory.T.star_coeff_eisenstein_series_reverse_poly
    exact GlobalTheory.GoodIdemReal.star_coeff_of_reverse D (fun k f hm h0 x => by
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      rw [Rc.T.n.types.eSer_def, Rc.T.n.types.eSer_def]
      exact key _ (Rc.T.n.types.O_equiv k) D.R.r f hm h0 x)
  exact GlobalTheory.T.exists_rowPlacement_finiteElement_matches_levels hDS Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 S.X S.G Q.instEq Q.ιS Q.tS Q.cG
    Q.charW.base.lev Q.charW.base.grp Q.charW.base.models Q.host hE0 Q.ιS_eq hE hP.grpRecPin hP.tSfin hP.tSpin

end GlobalTheory.RowPlacementReal
