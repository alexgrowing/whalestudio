import Formalism.LocalToGlobal.CarriedPlMap
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostDatumS
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SelSidePq

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
namespace Formalism.L2
section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
open Classical in
structure SelectedSideOfRealRecord (R : _root_.Formalism.L2.RecTAlt ex) (P : Rows.RowSideFamily ex)
    {Dcf : ∀ Zs : Indef.DefSub P.A3.fam3.amb3, Indef.DefCols (P.A3.side3 P.Ps P.ψs Zs)}
    {Spf : ∀ Zs : Indef.DefSub P.A3.fam3.amb3, Indef.SPer (Dcf Zs)}
    {Zscf : Indef.DefSub P.A3.fam3.amb3 → Indef.IndefScale P.A3.fam3.base3}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (RT : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks) (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion RT) (hd : _root_.Formalism.L2.HostDatumWithTies R.T.toTiedDataS)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → HeightOneSpectrum (𝓞 D.host.E)) : Prop where
  sel : _root_.Formalism.L2.SelectedSideOfPrimeAbove R Pq
  twQ : ∀ μ : D.what₂.Tup, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) →
    (Col.QE R.T.ker.sel (R.T.ker.tup μ : DIV.Chr R.T.ker.X.F R.T.ker.X.E R.T.ker.X.K)).image
      (Host.CT.plMap R.T.ker.seam.iE) = RT.Rl.Q (Qr.tupT μ)
  de : ∀ v, ((D.host.pde : ℕ) : 𝓞 D.host.E) ∈ (Pq v).asIdeal → (Pq v).under (𝓞 D.host.K) = hd.d3b.pK
  de' : ∀ v, ((D.host.pde' : ℕ) : 𝓞 D.host.E) ∈ (Pq v).asIdeal → (Pq v).under (𝓞 D.host.K) = hd.d3b.pK'
end
end Formalism.L2
end
end
