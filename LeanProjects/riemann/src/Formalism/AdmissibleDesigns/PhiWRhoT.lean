import Formalism.AdmissibleDesigns.RowDROfWpIso
import Formalism.AdmissibleDesigns.RhoContOf

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

set_option synthInstance.maxHeartbeats 400000

open Classical Matrix

namespace Formalism.MainNotions.N.K.RowB

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.KHf Formalism.MainNotions.N.KRow NumberField IsDedekindDomain Formalism.NG Formalism.BasicNotions

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

theorem phiW_rhoT' (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i))
    (g : Br.G D.nbr i _ hn) (v : TrV (eK (D.nbr i _ hn)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R) n)) (a : Fin D.R.r) :
    Font.phiW i dc n hn (repL (eK (D.nbr i _ hn))
      (KLat.Dat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (K.Aw i dc) hK hε hM n).ρT' (Br.iota D.nbr i _ hn) g v) a =
    ∑ b, eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
      (((epsU D.nd i ((Br.iota D.nbr i _ hn g : _) : GE D.nd) : (D.nd.O i)ˣ) : D.nd.O i) *
        Dd.ρk 0 (uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hn g : _) : GE D.nd)⁻¹) (H0.e0 b) (H0.e0 a))) *
      Font.phiW i dc n hn v b := by
  show eK (D.nbr i _ hn) ((((epsU D.nd i ((Br.iota D.nbr i _ hn g : _) : GE D.nd) : (D.nd.O i)ˣ) : D.nd.O i) •
      ((KLat.matK (Dd.ρk 0 (uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hn g : _) : GE D.nd)⁻¹)))ᵀ *ᵥ
        (v : {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)))) (H0.e0 a)) = _
  simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, Finset.smul_sum, map_sum]
  refine (Equiv.sum_comp (H0.e0 (D := D)) _).symm.trans (Finset.sum_congr rfl fun b _ => ?_)
  rw [Matrix.transpose_apply, KLat.matK, Matrix.map_apply, Algebra.smul_def, ← mul_assoc, ← map_mul, map_mul]
  rfl

variable {i dc Dd hK hε hM} in

theorem rowMat_at
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0
      eB e₁ s Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    IsMatLat (ρ := repL (eK (D.nbr i _ hn))
        (KLat.Dat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (K.Aw i dc) hK hε hM n).ρT' (Br.iota D.nbr i _ hn))
      (latT (eK (D.nbr i _ hn)) (D.nbr i _ hn).eO
        (KLat.Dat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (K.Aw i dc) hK hε hM n).T'.subtype (heO_br i dc hn))
      (⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (T2O D.nd i ρ π))) := by
  refine ⟨Font.phiW i dc n hn, fun g v => funext fun a => ?_, fun v => ?_⟩
  · rw [phiW_rhoT']
    show _ = ∑ b, Br.loc D.nbr i _ hn (T2O D.nd i ρ π) g a b * Font.phiW i dc n hn v b
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Font.loc_apply]
    show eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
        (((epsU D.nd i ((Br.iota D.nbr i _ hn g : _) : GE D.nd) : (D.nd.O i)ˣ) : D.nd.O i) *
          Dd.ρk 0 (uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hn g : _) : GE D.nd)⁻¹) (H0.e0 b) (H0.e0 a))) * _ =
      eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
        (((epsU D.nd i ((Br.iota D.nbr i _ hn g : _) : GE D.nd) : (D.nd.O i)ˣ) : D.nd.O i) *
          WpO D.nd i ρ π ((Br.iota D.nbr i _ hn g : _) : GE D.nd)⁻¹ b a)) * _
    rw [H0.unipotent_block_zero_entry hD hN]
  · rw [KRow.mem_latT]
    constructor
    · rintro ⟨m, rfl⟩ j
      obtain ⟨y, hy⟩ := Submodule.mem_one.1 (m.2 _ (KLat.unit_mem_latT (H0.e0 (D := D) j)))
      refine ⟨(D.nbr i _ hn).eO y, ?_⟩
      rw [heO_br i dc hn, hy]
      show _ = eK (D.nbr i _ hn) ((m : {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)) (H0.e0 j))
      congr 1
      show (fun k => if H0.e0 (D := D) j = k then (1 : FractionRing (D.nd.O i)) else 0) ⬝ᵥ
        (m : {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)) = _
      simp [dotProduct]
    · intro h
      choose z hz using h
      refine ⟨KLat.vD Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (K.Aw i dc) hK hε hM n
        (fun b => (D.nbr i _ hn).eO.symm (z ((H0.e0 (D := D)).symm b))), ?_⟩
      funext b
      apply (eK (D.nbr i _ hn)).injective
      show eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
        ((D.nbr i _ hn).eO.symm (z ((H0.e0 (D := D)).symm b)))) = eK (D.nbr i _ hn) (v b)
      rw [← heO_br i dc hn, RingEquiv.apply_symm_apply, hz]
      show eK (D.nbr i _ hn) (v (H0.e0 ((H0.e0 (D := D)).symm b))) = _
      rw [Equiv.apply_symm_apply]

variable {i dc Dd hK hε hM} in

theorem orbC_dat (n : ℕ) :
    KHf.OrbC i dc (n := n)
      (KLat.Dat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (K.Aw i dc) hK hε hM n).ρT' := by
  intro hn v
  have hι : Continuous fun g : Br.G D.nbr i _ hn => ((Br.iota D.nbr i _ hn g : _) : GE D.nd) :=
    continuous_subtype_val.comp (Br.iota_cont D.nbr i _ hn)
  have hf : (fun g => repL (eK (D.nbr i _ hn))
      (KLat.Dat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (K.Aw i dc) hK hε hM n).ρT' (Br.iota D.nbr i _ hn) g v) =
      fun g => (Font.phiW i dc n hn).symm (fun a => ∑ b, eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
        (((epsU D.nd i ((Br.iota D.nbr i _ hn g : _) : GE D.nd) : (D.nd.O i)ˣ) : D.nd.O i) *
          Dd.ρk 0 (uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hn g : _) : GE D.nd)⁻¹) (H0.e0 b) (H0.e0 a))) *
        Font.phiW i dc n hn v b) := by
    funext g
    apply (Font.phiW i dc n hn).injective
    rw [LinearEquiv.apply_symm_apply]
    funext a
    exact phiW_rhoT' i dc Dd hK hε hM n hn g v a
  rw [hf]
  refine (LinearMap.continuous_on_pi (Font.phiW i dc n hn).symm.toLinearMap).comp
    (continuous_pi fun a => continuous_finsetSum _ fun b _ => ((KOrb.eK_alg_cont i hn).comp ?_).mul continuous_const)
  exact (hε.comp hι).mul ((hM (H0.e0 b) (H0.e0 a)).comp (continuous_inv.comp hι))

end Lat

section Rec

attribute [local instance 2000] K.Topo.fracTopology K.Topo.rTopology

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)

theorem rowMat_S (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) :
    KRow.RowMat i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R))
      (St.DatS i r π dc g0 eB e₁ s Dd hD hc) ρ π := by
  intro n _ hn
  exact rowMat_at (hD := hD) (hN := hN) (n := n) (hn := hn) ..

theorem orbC_S : ∀ n ∈ K.rowsN i dc, KHf.OrbC i dc (n := n) (St.DatS i r π dc g0 eB e₁ s Dd hD hc n).ρT' := by
  intro n _
  exact orbC_dat n

variable (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)

end Rec

section RecN

attribute [local instance 2000] K.Topo.fracTopology K.Topo.rTopology

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd (Norm.rN i r ρ π)) π (chiU D.nd i 1) (epsU D.nd i)
    g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i (Norm.rN i r ρ π))
  (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)

theorem rowMat_SN :
    KRow.RowMat i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R))
      (St.DatS i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc) ρ π := by
  exact rowMat_S i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc (Norm.normAt_rN i r ρ π)

end RecN

end Formalism.MainNotions.N.K.RowB

end
