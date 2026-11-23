import Formalism.AdmissibleDesigns.TheoremFromNormalizedOpenThree
import Formalism.AdmissibleDesigns.EKSymmCont
import Formalism.AdmissibleDesigns.HomeoKOf
import Formalism.AdmissibleDesigns.LengthSemilinear

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

section Clauses

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)

def RowDR : Prop :=
  ∀ w ∈ rowsN i dc, ∀ hn : plOf i dc w ∈ placesOver D.host.E (D.nd.l i),
    IsDR (Br.PD D.loc D.nbr i _ hn)
      (KHf.repL (KHf.eK (D.nbr i _ hn)) (DatS i r π dc g0 eB e₁ s Dd hD hc w).ρT (Br.iota D.nbr i _ hn))

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem bKa_clause (hBK : LargeLevelLemmas.BlochKatoAnnihilators i) (hG : K.SelfGood i) (hdR : RowDR i r π dc g0 eB e₁ s Dd hD hc) :
    ∀ w ∈ rowsN i dc, ∀ a, a ∈ HfWS i r π dc g0 eB e₁ s Dd hD hc w ↔
      ∀ b ∈ Hf₂S i r π dc g0 eB e₁ s Dd hD hc w, cupFG (DatS i r π dc g0 eB e₁ s Dd hD hc w) a b = 0 := by
  intro w hw
  letI := modS i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  letI := modS' i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  have hreal := (KLat.rowLat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
    (hM0 i r π g0 eB e₁ s Dd hD hc) (D.nd.l i) (Topo.padicCoeff_O i) (Topo.fracTop_O i) w).2.1
  have hin : KBKa.RowIn i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R))
      (DatS i r π dc g0 eB e₁ s Dd hD hc) w :=
    KBKa.rowIn_of i dc _ _ (DatS i r π dc g0 eB e₁ s Dd hD hc) (fun _ => rfl)
      (fun hn => ⟨KOrb.homeoK i hn, KOrb.topMatch_pi i hn _, KOrb.topMatch_pi i hn _⟩) (hdR w hw)
  exact KBKa.bk_a_of_admitted_bk_a i dc _ _ (DatS i r π dc g0 eB e₁ s Dd hD hc) hBK hG hw hreal hin

variable (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)
  (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ)

theorem tie_clause (hG : K.SelfGood i) (hR : TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow)
    (hRT : Sel.RowTie i dc r ρ π (rowLenS i r π dc g0 eB e₁ s Dd hD hc hT hrk)) :
    TieRow i dc (rowLenS i r π dc g0 eB e₁ s Dd hD hc hT hrk) lenRow := by
  intro n hn
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hn
  have hpl : w ∈ plSet i dc := by
    unfold plSet
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hw)))
  have hwo : plOf i dc (idx i dc w) ∈ placesOver D.host.E (D.nd.l i) := by
    rw [plOf_idx i dc hpl]
    exact (dc.cover w).mp (Or.inl hw)
  have hrw : plOf i dc (idx i dc w) ∈ dc.row := by
    rw [plOf_idx i dc hpl]
    exact hw
  have hrow := hR (plOf i dc (idx i dc w)) hwo hrw (TruncatedSeriesCountingIdentities.CoefExt.self i _ hwo) (hG _ hwo)
  obtain ⟨h1, h2⟩ := hRT _ hn hwo _ hrow
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  rw [mul_comm, Sel.lenOlSelf i _ hwo]

end Clauses

end Formalism.MainNotions.N.K.StD

end
