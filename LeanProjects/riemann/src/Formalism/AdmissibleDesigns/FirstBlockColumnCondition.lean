import Formalism.AdmissibleDesigns.TheoremFromNormalizedOpenThree
import Formalism.AdmissibleDesigns.MemImageOfTensorSum
import Formalism.AdmissibleDesigns.EKSymmCont
import Formalism.AdmissibleDesigns.CharacterTrivialWhereLattice
import Formalism.AdmissibleDesigns.HigherColumnInvariantsBound

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.StB

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Rho

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)
  (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)

set_option synthInstance.maxHeartbeats 400000 in

theorem first_block_column_condition (l : Col i dc) :
    FS i r π dc g0 eB e₁ s Dd hD hc 0 (colIdx i dc l) =
      KHf.F0col i dc (colIdx i dc l)
        (resRep (uRep (D.nd.O i) (M := Vr i Dd) Dd.r Dd.χ) (decs D.host.E (Aw i dc) (colIdx i dc l)))
        (QS.resU i dc Dd 0 (colIdx i dc l)) (qVM (D.nd.O i) _ (Dd.ρk 0).toRingHom) := by
  have hnot : colIdx i dc l ∉ rowsN i dc := by
    intro h
    obtain ⟨w, hw, hwe⟩ := Finset.mem_image.mp h
    have h1 : l.1 ∈ plSet i dc := by
      unfold plSet
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr l.2)))
    have h2 : w ∈ plSet i dc := by
      unfold plSet
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hw)))
    have heq : w = l.1 := idx_inj i dc h2 h1 hwe
    have hwc : w ∈ dc.col := by
      rw [heq]
      exact l.2
    exact Finset.disjoint_left.mp dc.disj hw hwc
  simp only [FS, QS.Fall, Fin.cases_zero]
  unfold FirstBlockLocalConditions
  simp only [KHf.Fρ, if_neg hnot]

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem hRho_of
    (hG4 : TruncatedSeriesCountingIdentities.admG4 i r) (hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hFf : ∀ l, KFin.FinFf i dc Dd l) (hRk : ∀ l, KFin.RankFf i dc Dd ρ π l)
    (hSel : TieSel1 i ρ π (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc))
      (rowsN i dc) (FS i r π dc g0 eB e₁ s Dd hD hc 0) (QS.Io i)) :
    InRhoFixReal2 (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ Dd.e₁ (colIdx i dc) (decs D.host.E (Aw i dc))
      (jN i ρ π dc) (rowsN i dc) (sN i ρ π) (tensM (D.nd.O i) _ (Dd.ρk 0).toRingHom) (v1S i Dd hT hrk)
      (KFin.κ i dc Dd ρ π)
      (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) (qVM (D.nd.O i) _ (Dd.ρk 0).toRingHom)
      (fun l => KHf.Ff i dc Dd.r Dd.χ (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) l) (KFin.κz i dc Dd ρ π)
      (FS i r π dc g0 eB e₁ s Dd hD hc 0)
      (QS.Io i) (epsU D.nd i) (rho1 i Dd) (rho2 i Dd) (FirstSummandSubmodule (D.nd.O i) Dd.e₁).subtype (piS i Dd hT hrk)
      (gamM (Dd.ρk 0)) (lamS i Dd hT hrk) := by
  have hA := tensor_lattice_facts Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT hrk (epsU D.nd i)
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩, -, -, -, -, -, -, hinc, -, hgam, -⟩ := hA
  have hOrb : ∀ l : Col i dc, KHf.OrbC i dc (KFin.ρV i dc Dd l) := fun l =>
    KOrb.orbC_uRep i dc r π g0 eB e₁ s Dd hD hc (fun c v => KOrb.latM_alg i Dd (Dd.ρk 0) c v) (colIdx i dc l)
  refine ⟨h1, h2, ?_, ⟨h3, h4, h5, h6, h7, h8, h9, fun l =>
      KFin.finRhoAt_of i dc Dd ρ π l (hOrb l) (hFf l) (hRk l)⟩,
    QS.inertia_triviality_clause i r ρ π Dd (QS.ev_of hD) hG4 hdec, hinc,
    fun g b => pi_equiv2 Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) Dd.e₁ _ g b, hgam,
    selRho_le_sN i ρ π _ Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc) _ (QS.Io i) hSel⟩
  intro l z x hz
  rw [first_block_column_condition]
  exact KFin.clause3 i dc Dd ρ π l z x hz

end Rho

end Formalism.MainNotions.N.K.StB

end
