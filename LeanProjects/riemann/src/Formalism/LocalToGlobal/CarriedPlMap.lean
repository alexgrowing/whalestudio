import Formalism.LocalToGlobal.SelSide
import Formalism.LocalToGlobal.IndefiniteReal.TrISepWith
import Formalism.LocalToGlobal.IndefiniteReal.RealRec
import Formalism.LocalToGlobal.UnitaryNorms.DatumS

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace Formalism.L2

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

open Classical in

structure SelSideRT (R : RecT ex) (P : Rows.RowSideFamily ex)
    {Dcf : ∀ Zs : Indef.DefSub P.A3.fam3.amb3, Indef.DefCols (P.A3.side3 P.Ps P.ψs Zs)}
    {Spf : ∀ Zs : Indef.DefSub P.A3.fam3.amb3, Indef.SPer (Dcf Zs)}
    {Zscf : Indef.DefSub P.A3.fam3.amb3 → Indef.IndefScale P.A3.fam3.base3}
    {S : SG.SpectralTiesReal.STiesR R} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (RT : IndefR.RealT R P Dcf Spf Zscf S Ks) (Qr : IndefR.RealRec RT) (hd : HostDatumC R.T.toTiedDataS)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → HeightOneSpectrum (𝓞 D.host.E)) : Prop where

  sel : SelSidePq R Pq

  twQ : ∀ μ : D.what₂.Tup, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) →
    (Col.QE R.T.ker.sel (R.T.ker.tup μ : DIV.Chr R.T.ker.X.F R.T.ker.X.E R.T.ker.X.K)).image
      (Host.CT.plMap R.T.ker.seam.iE) = RT.Rl.Q (Qr.tupT μ)

  de : ∀ v, ((D.host.pde : ℕ) : 𝓞 D.host.E) ∈ (Pq v).asIdeal → (Pq v).under (𝓞 D.host.K) = hd.d3b.pK

  de' : ∀ v, ((D.host.pde' : ℕ) : 𝓞 D.host.E) ∈ (Pq v).asIdeal → (Pq v).under (𝓞 D.host.K) = hd.d3b.pK'

theorem SelJ.carried_plMap {D : D7} {X : Col.Fields} (s : Ker.Seam D X) (P : HeightOneSpectrum (𝓞 X.E)) :
    SelJ.Carried s P (Host.CT.plMap s.iE P) := by
  unfold SelJ.Carried SelJ.oEq Host.CT.plMap
  show Ideal.comap ((RingOfIntegers.mapRingEquiv s.iE).symm : 𝓞 D.host.E →+* 𝓞 X.E) P.asIdeal = _
  exact Ideal.comap_symm _

end

end Formalism.L2
