import Formalism.AdmissibleDesigns.IsDROfWpIso
import Formalism.AdmissibleDesigns.KernelLengthHigherColumns
import Formalism.AdmissibleDesigns.FgTopContinuousLinearMap

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

set_option synthInstance.maxHeartbeats 400000

open Classical

namespace Formalism.MainNotions.N.K.Font

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.KHf Formalism.MainNotions.N.KDim NumberField IsDedekindDomain Formalism.NG Formalism.BasicNotions

section RhoC

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem rhoCont_of (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) :
    Continuous fun g => rhoO D.nd i ρ π g := by
  have h : (fun g => rhoO D.nd i ρ π g) = fun g => (fun a b => rO D.nd i r π g (Fin.castAdd D.R.t a) (Fin.castAdd D.R.t b) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) := by
    funext g
    exact Matrix.ext fun a b => (hN.2.2 g a b).symm
  rw [h]
  exact continuous_pi fun a => continuous_pi fun b => (hc π).matrix_elem _ _

end RhoC

section Lat

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (g0 : GE D.nd)
  (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))]
  (hK : ContinuousMul (FractionRing (D.nd.O i)))
  (hε : Continuous fun g => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i))
  (hM : ∀ a b, Continuous fun g => KLat.M0 Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk g a b)

def phiW (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    TrV (eK (D.nbr i _ hn)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R) n) ≃ₗ[Br.LL D.nbr i _ hn]
      (Fin D.R.r → Br.LL D.nbr i _ hn) where
  toFun v a := eK (D.nbr i _ hn) ((v : {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)) (H0.e0 a))
  invFun w := (show {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i) from
    fun b => (eK (D.nbr i _ hn)).symm (w ((H0.e0 (D := D)).symm b)))
  map_add' u v := funext fun a => map_add (eK (D.nbr i _ hn)) _ _
  map_smul' c v := funext fun a => by
    show eK (D.nbr i _ hn) ((eK (D.nbr i _ hn)).symm c * _) = c * _
    rw [map_mul, RingEquiv.apply_symm_apply]
  left_inv v := by
    funext b
    show (eK (D.nbr i _ hn)).symm (eK (D.nbr i _ hn) (_ : FractionRing (D.nd.O i))) = _
    rw [RingEquiv.symm_apply_apply, Equiv.apply_symm_apply]
  right_inv w := by
    funext a
    show eK (D.nbr i _ hn) ((eK (D.nbr i _ hn)).symm (w ((H0.e0 (D := D)).symm (H0.e0 a)))) = w a
    rw [RingEquiv.apply_symm_apply, Equiv.symm_apply_apply]

theorem wpIso_dat (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0
      eB e₁ s Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    WpIso i dc ρ π n hn (KLat.Dat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (K.Aw i dc) hK hε hM n).ρT := by
  refine ⟨phiW i dc n hn, fun g x => funext fun a => ?_⟩
  show eK (D.nbr i _ hn) ((KLat.matK (Dd.ρk 0 (uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hn g : _) : GE D.nd)))).mulVec
      (x : {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)) (H0.e0 a)) =
    ∑ b, Br.loc D.nbr i _ hn (WpO D.nd i ρ π) g a b * eK (D.nbr i _ hn) ((x : {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)) (H0.e0 b))
  refine (congrArg (eK (D.nbr i _ hn)) (KLat.matK_mulVec (Dd.ρk 0 (uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hn g : _) : GE D.nd)))
    (show {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i) from x) (H0.e0 a))).trans ?_
  rw [map_sum]
  refine (Equiv.sum_comp (H0.e0 (D := D)) _).symm.trans (Finset.sum_congr rfl fun b _ => ?_)
  rw [Algebra.smul_def, map_mul, loc_apply, H0.unipotent_block_zero_entry hD hN]

end Lat

section RowDR2

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (g0 : GE D.nd)
  (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))]
  (hK : ContinuousMul (FractionRing (D.nd.O i)))
  (hε : Continuous fun g => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i))
  (hM : ∀ a b, Continuous fun g => KLat.M0 Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk g a b)

theorem isDR_dat (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hCont : TruncatedSeriesCountingIdentities.FamilyContinuous i r)
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0
      eB e₁ s Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    IsDR (Br.PD D.loc D.nbr i _ hn) (repL (eK (D.nbr i _ hn))
      (KLat.Dat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (K.Aw i dc) hK hε hM n).ρT (Br.iota D.nbr i _ hn)) :=
  isDR_of_wpIso i dc r ρ π hF hG2 hDec hCont (rhoCont_of i r ρ π hCont hN) n hn _ (wpIso_dat i dc r ρ π g0 eB e₁ s Dd hK hε hM hD hN n hn)

end RowDR2

end Formalism.MainNotions.N.K.Font

end
