import Formalism.AdmissibleDesigns.BKaClause
import Formalism.AdmissibleDesigns.IsDROfWpIso
import Formalism.AdmissibleDesigns.FiniteClassesRowEqGeneric

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.StD

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Red

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)

variable (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem rowTie_S
    (hSub : haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
      KRow.RowSub (ρ₁ := rho1 i Dd) i dc r)
    (hOrb : haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
      KRow.RowOrb (ρ₁ := rho1 i Dd) i dc)
    (hMat : KRow.RowMat i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R))
      (DatS i r π dc g0 eB e₁ s Dd hD hc) ρ π)
    (hTop : haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
      KRow.RowTop i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (T₁ := FirstSummandSubmodule (D.nd.O i) Dd.e₁))
    (hFin : KRow.RowFin i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R))
      (DatS i r π dc g0 eB e₁ s Dd hD hc) (T₁ := FirstSummandSubmodule (D.nd.O i) Dd.e₁))
    (hcob : ∀ n ∈ rowsN i dc, KHf.OrbC i dc (n := n) (DatS i r π dc g0 eB e₁ s Dd hD hc n).ρT') :
    Sel.RowTie i dc r ρ π (rowLenS i r π dc g0 eB e₁ s Dd hD hc hT hrk) := by
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  letI := modS' i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  have hπ : Function.Surjective (piS i Dd hT hrk) :=
    (tensor_lattice_facts Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT hrk (epsU D.nd i)).2.2.2.2.2.2.2.2.2.2
  exact KRow.rowTie_disp i dc _ _ (DatS i r π dc g0 eB e₁ s Dd hD hc) (rho1 i Dd) (piS i Dd hT hrk)
    (vDS i r π dc g0 eB e₁ s Dd hD hc) (hpDS i r π dc g0 eB e₁ s Dd hD hc hT hrk)
    (heDS i r π dc g0 eB e₁ s Dd hD hc hT hrk) r ρ π hπ hSub hOrb hMat hTop hFin hcob

end Red

end Formalism.MainNotions.N.K.StD

end
