import Formalism.AdmissibleDesigns.RowDROfWpIso
import Formalism.AdmissibleDesigns.RhoContOf
import Formalism.AdmissibleDesigns.RowTopOf
import Formalism.AdmissibleDesigns.LocRepTriv

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.StD

section Unr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (δO : D.nd.O i)

def UnrIn : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.col →
    Z1ur (1 : Representation ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 (Br.G D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1)
        (Br.inert D.nbr i w hw) ≤
      finiteCocycles (Br.PD D.loc D.nbr i w hw)
        (1 : Representation ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 (Br.G D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1)

theorem unramified_input_of_admitted (h : EmbeddingTypes.UnramifiedTrivialH1f i dc) : UnrIn i dc := by
  intro w hw hc
  have h2 := h w hw hc (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)
  unfold UnrTriv at h2
  first
  | exact h2.ge
  | exact h2.symm.le
  | exact le_of_eq h2.symm
  | (rw [h2])

theorem unrFinIn_of (hA : UnrIn i dc) (l : K.Col i dc) : KFin.UnrFinIn i dc δO l := by
  intro f hf
  have hn := KUnr.col_over i dc l
  refine Submodule.mem_map_of_mem ?_
  show (fun g => KHf.mkK (((KFin.uzOf i dc δO l f hf.1 : _ → _) g))) ∈
    ((KHf.fZ i dc (K.colIdx i dc l) (KHf.locRep (Representation.trivial (D.nd.O i) ↥(KFin.Γc i dc l)
      ↥(Ideal.span {δO})))).restrictScalars (D.nd.O i))
  rw [Submodule.restrictScalars_mem, KHf.fZ_pos i dc _ hn]
  have hU := hA (K.plOf i dc (K.colIdx i dc l)) hn (KUnr.col_mem i dc l)
  let Bw := D.nbr i (K.plOf i dc (K.colIdx i dc l)) hn
  let V := KHf.MK (O := D.nd.O i) ↥(Ideal.span {δO})
  let c' : Br.G D.nbr i _ hn → Br.LLw Bw := fun g =>
    KHf.eK Bw (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (f (Br.iota D.nbr i _ hn g)))
  have hc' : c' ∈ Z1ur (1 : Representation (Br.LLw Bw) (Br.G D.nbr i _ hn) (Br.LLw Bw)) (Br.inert D.nbr i _ hn) := by
    refine ⟨⟨hf.2.2 hn, fun g h => ?_⟩, 0, fun g hg => ?_⟩
    · show c' (g * h) = c' g + c' h
      have h1 : f (Br.iota D.nbr i _ hn g * Br.iota D.nbr i _ hn h) =
          f (Br.iota D.nbr i _ hn g) + f (Br.iota D.nbr i _ hn h) := hf.1 _ _
      simp only [c', map_mul]
      rw [h1, map_add, map_add]
    · show c' g = 0 - 0
      rw [sub_zero]
      show KHf.eK Bw (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (f (Br.iota D.nbr i _ hn g))) = 0
      rw [hf.2.1 _ hg, map_zero, map_zero]
  have hcf : c' ∈ finiteCocycles (Br.PD D.loc D.nbr i _ hn) (1 : Representation (Br.LLw Bw) (Br.G D.nbr i _ hn) (Br.LLw Bw)) := by
    exact hU hc'
  let v0 : KHf.TrV (KHf.eK Bw) V := KHf.mkK (⟨δO, Ideal.mem_span_singleton_self δO⟩ : ↥(Ideal.span {δO}))
  let f0 : Br.LLw Bw →ₗ[Br.LLw Bw] KHf.TrV (KHf.eK Bw) V := LinearMap.toSpanSingleton _ _ v0
  have hf0 : Continuous f0 := continuous_id.smul continuous_const
  let ρ' := KHf.repL (KHf.eK Bw) (KHf.locRep (Representation.trivial (D.nd.O i) ↥(KFin.Γc i dc l) ↥(Ideal.span {δO})))
    (Br.iota D.nbr i _ hn)
  have heq : ∀ g x, f0 ((1 : Representation (Br.LLw Bw) (Br.G D.nbr i _ hn) (Br.LLw Bw)) g x) = ρ' g (f0 x) :=
    fun g x => (KUnr.locRep_triv (Br.iota D.nbr i _ hn g) (f0 x : V)).symm
  have key := (cocyclesFunctorial_holds _ _ _ _ _ _ (Br.PD D.loc D.nbr i _ hn) (Br.LLw Bw) (Br.LLw Bw) (KHf.TrV (KHf.eK Bw) V)
    1 ρ' f0 hf0 heq c').2 hcf
  let lhs : Br.G D.nbr i _ hn → KHf.TrV (KHf.eK Bw) V := fun g =>
    ((KHf.mkK ((KFin.uzOf i dc δO l f hf.1 : ↥(KFin.Γc i dc l) → ↥(Ideal.span {δO})) (Br.iota D.nbr i _ hn g)) : V) :
      KHf.TrV (KHf.eK Bw) V)
  show lhs ∈ finiteCocycles (Br.PD D.loc D.nbr i _ hn) ρ'
  suffices hfun : lhs = ⇑f0 ∘ c' by
    rw [hfun]
    exact key
  funext g
  show _ = f0 (c' g)
  rw [LinearMap.toSpanSingleton_apply]
  show _ = ((KHf.eK Bw).symm (c' g) • (show V from v0) : V)
  simp only [c', RingEquiv.symm_apply_apply]
  rw [algebraMap_smul]
  rw [← map_smul]
  show KHf.mkK ((KFin.uzOf i dc δO l f hf.1 : ↥(KFin.Γc i dc l) → ↥(Ideal.span {δO})) (Br.iota D.nbr i _ hn g)) =
    KHf.mkK _
  congr 1
  apply Subtype.ext
  show δO * f (Br.iota D.nbr i _ hn g) = f (Br.iota D.nbr i _ hn g) * δO
  ring

theorem unrFin_of (hA : UnrIn i dc) : KHf.UnrFin i dc δO (KFin.uz i dc δO) := by
  intro l
  refine unrFinIn_of i dc δO hA l _ ?_

  by_cases hU : KFin.UnrHom i dc l
  · unfold KFin.uCol; rw [dif_pos hU]; exact hU.choose_spec.1
  · have h0 : KFin.uCol i dc l = 0 := by unfold KFin.uCol; exact dif_neg hU
    rw [h0]; unfold KFin.UnrAdm
    refine ⟨fun g h => by simp, fun g _ => rfl, fun hn => ?_⟩
    first
    | (simp only [Pi.zero_apply, map_zero]; exact continuous_const)
    | exact Continuous.congr (f := fun _ => KHf.eK (D.nbr i (plOf i dc (colIdx i dc l)) hn)
        ((algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) 0)) continuous_const (fun _ => rfl)

end Unr

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.JS Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Red3

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem rowDR_of_fontaine (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) : RowDR i r π dc g0 eB e₁ s Dd hD hc := fun w _ hn =>
  Font.isDR_dat i dc r ρ π g0 eB e₁ s Dd (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc) hF hG2 hDec hc hD hN w hn

variable (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

def RowTieIn : Prop :=
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  KRow.RowSub (ρ₁ := rho1 i Dd) i dc r ∧ KRow.RowOrb (ρ₁ := rho1 i Dd) i dc ∧
  KRow.RowMat i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R))
    (DatS i r π dc g0 eB e₁ s Dd hD hc) ρ π ∧
  KRow.RowTop1 i dc (T₁ := FirstSummandSubmodule (D.nd.O i) Dd.e₁) ∧
  KRow.RowFin i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R))
    (DatS i r π dc g0 eB e₁ s Dd hD hc) (T₁ := FirstSummandSubmodule (D.nd.O i) Dd.e₁) ∧
  ∀ n ∈ rowsN i dc, KHf.OrbC i dc (n := n) (DatS i r π dc g0 eB e₁ s Dd hD hc n).ρT'

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem row_match_from_comparison (h : RowTieIn i r ρ π dc g0 eB e₁ s Dd hD hc) :
    Sel.RowTie i dc r ρ π (rowLenS i r π dc g0 eB e₁ s Dd hD hc hT hrk) := by
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  obtain ⟨hSub, hOrb, hMat, hTop1, hFin, hcob⟩ := h
  exact rowTie_S i r ρ π dc g0 eB e₁ s Dd hD hc hT hrk hSub hOrb hMat
    (KRow.rowTop_of i dc _ (fun _ _ hw => KOrb.topMatch_pi i hw _) hTop1) hFin hcob

end Red3

end Formalism.MainNotions.N.K.StD

end
