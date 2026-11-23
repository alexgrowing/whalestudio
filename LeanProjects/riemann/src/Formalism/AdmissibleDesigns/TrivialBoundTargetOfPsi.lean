import Formalism.AdmissibleDesigns.URepApply
import Formalism.AdmissibleDesigns.TrivialBoundGeneral
import Formalism.AdmissibleDesigns.CycMatchRec

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.MainNotions.N.K.TB
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.ShaT
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Cyc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem cycW_of : CycW i dc := by
  intro w hw g
  have h1 := Formalism.MainNotions.N.KBKa.cycZ_eq_χQ (D.nbr i w hw) (D.loc (D.nd.l i)) (eW i dc hw g)
  have h2 := (D.loc (D.nd.l i)).PD_χ (D.nbr i w hw).Kw (eW i dc hw g)
  have h3 : ((Br.ι (D.nbr i w hw) (eW i dc hw g) : Dec (F := D.host.E) (D.nd.plOm.1 w)) : GE D.nd) = (g : GE D.nd) := by
    show (((D.nbr i w hw).e.symm ((D.nbr i w hw).e (MulEquiv.subgroupCongr (Dw_idx i dc hw) g)) :
      ↥(Dec (F := D.host.E) (D.nd.plOm.1 w))) : GE D.nd) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  rw [h3] at h1
  show ((((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).χ (eW i dc hw g) : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) = _
  rw [h2, ← h1]
  rfl

theorem eW_inert' {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (h : Br.G D.nbr i w hw) (hh : h ∈ Br.inert D.nbr i w hw) :
    (eW i dc hw).symm h ∈ (Ine (F := D.host.E) (Aw i dc (idx i dc w))).subgroupOf (Dw i dc (idx i dc w)) := by
  rw [Subgroup.mem_subgroupOf]
  have hA : Aw i dc (idx i dc w) = D.nd.plOm.1 w := by
    unfold Aw
    rw [plOf_idx i dc (mem_plSet i dc hw)]
  rw [hA]
  exact hh

end Cyc

section Dict

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem sE_cont (c' : Fin D.R.t) :
    Continuous fun g : GE D.nd => sE i (((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1) g := by
  have := D.nd.trO i
  have hc1 : Continuous fun g : GE D.nd => (((D.nd.chi i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
    have : (fun g : GE D.nd => (((D.nd.chi i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) =
        fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := funext fun g => by rw [map_inv]
    rw [this]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  have h := hc1.mul (D.nd.chi_cont i ((c' : ℕ) + 1))
  have he : (fun g : GE D.nd => sE i (((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1) g) =
      fun g => (((D.nd.chi i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * ((D.nd.chi i ((c' : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) :=
    funext fun g => (chi_ratio (i := i) c' g).symm
  rw [he]
  exact h

theorem epsL_cont {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (c' : Fin D.R.t) :
    Continuous fun h => (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) (epsL i dc hw h)) ^
      (((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1) := by
  have he : (fun h => (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) (epsL i dc hw h)) ^
      (((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1)) = fun h => algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))
        ((D.nbr i w hw).eO (sE i (((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1) (((eW i dc hw).symm h : Dw i dc (idx i dc w)) : GE D.nd))) := by
    funext h
    rw [eO_sE i dc (cycW_of i dc) hw, MulEquiv.apply_symm_apply, map_pow]
  rw [he]
  exact continuous_subtype_val.comp ((D.nbr i w hw).eO_cont.comp
    ((sE_cont i c').comp (continuous_subtype_val.comp (eW_symm_cont i dc hw))))

variable [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

set_option maxHeartbeats 1000000 in

theorem coefDict_of
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (c : Fin (D.R.t + 1)) (hc : 1 ≤ (c : ℕ)) :
    Nonempty (CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)
      (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w)) (eW i dc hw) ((c : ℕ) - 1)) := by
  obtain ⟨φ, hφ⟩ := blkTw_of_def hD hN c hc
  obtain ⟨c', rfl⟩ : ∃ c', Fin.succ c' = c := Fin.exists_succ_eq.mpr (by
    rintro rfl
    simp at hc)
  exact ⟨coefDictOf i dc Dd (cycW_of i dc) hw c'.succ φ hφ (epsL_cont i dc hw c')⟩

end Dict

section Len

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

set_option maxHeartbeats 1000000 in

theorem lenMap_of (cB : ℕ) (hTB : TrivialBoundAtRows i dc r π cB) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (hwrow : w ∈ dc.row) (c : Fin (D.R.t + 1)) (hc : 1 ≤ (c : ℕ))
    (Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)
      (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w)) (eW i dc hw) ((c : ℕ) - 1)) :
    LenMap (Br.PD D.loc D.nbr i w hw) (selfO i hw) (Qcore i dc Dd c (idx i dc w) cB) Cd.Ce cB := by
  have hT := hTB w hw hwrow
  have het : (c : ℕ) - 1 < D.R.t := by
    have := c.2
    omega
  have h2 := trivial_bound_general hT het Cd.Ce
  have hp : (Br.PD D.loc D.nbr i w hw).p = D.nd.l i := Br.PD_p D.loc D.nbr i w hw
  refine lenMap_gen Cd (eW_symm_cont i dc hw) hp ?_ ?_
  · intro z hz hF
    unfold Fc at hF
    split_ifs at hF with h1
    · exact hW_zero Cd (eW_symm_cont i dc hw) (h2.2 (by omega)) (fun h hh => eW_inert' i dc hw h hh) z hz hF
    · exact hW_bot Cd z hz hF
  · intro z hz hH
    unfold Fc
    split_ifs with h1
    · exact hB_zero Cd (eW_symm_cont i dc hw) (h2.2 (by omega)) (eW_inert i dc hw) z hz hH
    · exact hB_bot Cd (eW_symm_cont i dc hw) (h2.1 (by omega)) z hz hH

end Len

section Dict2

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def YtPsi : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.row →
    ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) →
      ∀ Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)
          (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w)) (eW i dc hw) ((c : ℕ) - 1),
        ∃ Y : YtLat (G := Br.G D.nbr i w hw) (Qp := ℚ_[D.nd.l i]) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
            ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL),
          YtCrys (PD := Br.PD D.loc D.nbr i w hw) Y (Jr i r π (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) ∧
          PsiExt (selfO i hw) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w)) (eW i dc hw) Y Cd

set_option maxHeartbeats 4000000 in

theorem tbDict2_of (cB : ℕ)
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (hTB : TrivialBoundAtRows i dc r π cB)
    (hY : YtPsi i dc r π Dd) : TBDict2 i dc r π Dd cB := by
  intro w hw hwrow c hcc
  obtain ⟨Cd⟩ := coefDict_of i dc r ρ π g0 eB e₁ s Dd hD hN hw c hcc
  obtain ⟨Y, hY1, hY2⟩ := hY w hw hwrow c hcc Cd
  refine ⟨Y, Cd, hY1, hY2, ?_, ?_⟩
  · exact yLoc_of i dc r π g0 eB e₁ s Dd hD hc c (idx i dc w)
  · exact lenMap_of i dc r π Dd cB hTB hw hwrow c hcc Cd

theorem trivial_bound_target_of_psi (cB : ℕ)
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (hTB : TrivialBoundAtRows i dc r π cB)
    (hTie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i) (hY : YtPsi i dc r π Dd) : TBTarget i dc Dd cB :=
  trivial_bound_target_of_dict i dc r π Dd cB hTB hTie (tbDict2_of i dc r ρ π g0 eB e₁ s Dd cB hD hN hc hTB hY)

end Dict2

end Formalism.MainNotions.N.K.TBb

end
