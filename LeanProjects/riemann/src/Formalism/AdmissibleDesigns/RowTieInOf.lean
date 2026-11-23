import Formalism.AdmissibleDesigns.RowLatticeFiniteFree
import Formalism.AdmissibleDesigns.UnramifiedInputOfAdmitted

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.KRowA

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.RepresentationBoundsCohomology.BR Formalism.NG
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

attribute [local instance 2000] K.Topo.fracTopology K.Topo.rTopology

open Formalism.MainNotions.N.K Formalism.MainNotions.N.K.St

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem rowTieIn_of
    (hMat : KRow.RowMat i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R))
      (DatS i r π dc g0 eB e₁ s Dd hD hc) ρ π)
    (hcob : ∀ n ∈ rowsN i dc, KHf.OrbC i dc (n := n) (DatS i r π dc g0 eB e₁ s Dd hD hc n).ρT') :
    StD.RowTieIn i r ρ π dc g0 eB e₁ s Dd hD hc := by
  refine ⟨?_, ?_, hMat, ?_, ?_, hcob⟩
  · first
    | exact rowSub_S (hc := hc) ..
    | exact rowSub_S ..
    | (have hD' := hD
       obtain ⟨-, -, -, -, -, -, hr', -, hsm, -, -, hχ, -⟩ := hD'
       have hFF := idempotent_part_finite_and_free (hD := hD) ..
       haveI := hFF.1
       haveI := hFF.2
       intro n _ hn
       exact rowSub_at (hr' := hr') (hsm := hsm) (hχ := hχ) (hn := hn) ..)
  · first
    | exact rowOrb_S (hc := hc) ..
    | exact rowOrb_S i r π dc g0 eB e₁ s Dd hD hc
  · first
    | exact rowTop1_S i dc r π g0 eB e₁ s Dd hD
    | exact rowTop1_S (dc := dc) (hD := hD)
    | exact fun n hn hn' c hcont => rowTop1_S (hD := hD) .. n hn hn' c hcont
  · first
    | exact rowFin_S ..
    | exact rowFin_S i r π dc g0 eB e₁ s Dd hD hc

end Formalism.MainNotions.N.KRowA

end
