import Formalism.AdmissibleDesigns.BkLocCol
import Formalism.AdmissibleDesigns.InvariantsMapEquivariant
import Formalism.AdmissibleDesigns.RankReductionIdempotentOne
import Formalism.AdmissibleDesigns.CoboundaryMemFiniteClasses
import Formalism.AdmissibleDesigns.FgTopContinuousLinearMap

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.Bk

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N
  Formalism.MainNotions.N.K Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N.KHf Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.Sel

section Col

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

abbrev VB : Type :=
  LatM (D.nd.O i) (FractionRing (D.nd.O i)) {a // RepresentationBoundsCohomology.blk D.R a = 0} (Dd.ρk 0).toRingHom

abbrev qB : VB i Dd →ₗ[D.nd.O i] blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0 :=
  qVM (D.nd.O i) {a // RepresentationBoundsCohomology.blk D.R a = 0} (Dd.ρk 0).toRingHom

def psiB {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    TrV (eK (D.nbr i w hw)) (VB i Dd) →ₗ[Br.LLw (D.nbr i w hw)] (Fin D.R.r → Br.LLw (D.nbr i w hw)) where
  toFun v a := eK (D.nbr i w hw) ((show VB i Dd from v) (H0.e0 a))
  map_add' u v := by
    funext a
    exact map_add (eK (D.nbr i w hw)) _ _
  map_smul' c v := by
    funext a
    show eK (D.nbr i w hw) ((eK (D.nbr i w hw)).symm c * (show VB i Dd from v) (H0.e0 a)) =
      c * eK (D.nbr i w hw) ((show VB i Dd from v) (H0.e0 a))
    rw [map_mul, RingEquiv.apply_symm_apply]

theorem psiB_apply {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (v : TrV (eK (D.nbr i w hw)) (VB i Dd)) (a : Fin D.R.r) :
    psiB i Dd hw v a = eK (D.nbr i w hw) ((show VB i Dd from v) (H0.e0 a)) := rfl

theorem psiB_cont {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    Continuous (psiB i Dd hw) :=
  IsModuleTopology.continuous_of_linearMap (psiB i Dd hw)

set_option synthInstance.maxHeartbeats 400000 in

theorem psiB_comp {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (v : VB i Dd) :
    Br.phi (D.nbr i w hw) D.R.r (phi0 i Dd (qB i Dd v)) = Submodule.Quotient.mk (psiB i Dd hw v) := by
  have h1 : phi0 i Dd (qB i Dd v) =
      (Submodule.Quotient.mk (fun a => v (H0.e0 a)) : KOG (D.nd.O i) D.R.r) := by
    show (H0.kogEq D.R.r).symm (fun a => (qB i Dd v) (H0.e0 a)) = _
    apply (H0.kogEq D.R.r).injective
    rw [LinearEquiv.apply_symm_apply, H0.kogEq_apply, H0.kogTo_mk]
    rfl
  rw [h1]
  rfl

end Col

section Eqv

variable {D : D7} {i : D.nd.Loc} (dc : TruncatedSeriesCountingIdentities.Decl D i) {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
  {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i}
  {g0 : GE D.nd} {eB e₁ s : D.nd.X i → MatN D.nd i}
  {Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R)}
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem psiB_equiv
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (n : ℕ) (hw : plOf i dc n ∈ placesOver D.host.E (D.nd.l i))
    (g : ↥(GK (D.nbr i _ hw).Kw)) (v : TrV (eK (D.nbr i _ hw)) (VB i Dd)) :
    psiB i Dd hw (repL (eK (D.nbr i _ hw))
        (resRep (uRep (D.nd.O i) (M := VB i Dd) Dd.r Dd.χ) (decs D.host.E (Aw i dc) n))
        (Br.iota D.nbr i _ hw) g v) =
      matRep (Br.locM (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) g (psiB i Dd hw v) := by
  funext a
  rw [psiB_apply]
  show _ = ∑ b, (Br.locM (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n))) g) a b *
    psiB i Dd hw v b
  show eK (D.nbr i _ hw) (∑ c, (Dd.ρk 0 (uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hw g : decs D.host.E (Aw i dc) n) : GE D.nd)))
      (H0.e0 a) c • (show VB i Dd from v) c) = _
  rw [map_sum, ← Equiv.sum_comp (H0.e0 (D := D))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [H0.unipotent_block_zero_entry hD hN, Algebra.smul_def, map_mul, eK_apply, Br.toLLK_alg]
  rfl

end Eqv

section Row

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))]
  (VT VT' : ℕ → Type)
  [∀ w, AddCommGroup (VT w)] [∀ w, Module (D.nd.O i) (VT w)] [∀ w, TopologicalSpace (VT w)]
  [∀ w, IsTopologicalAddGroup (VT w)] [∀ w, ContinuousSMul (D.nd.O i) (VT w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT w)]
  [∀ w, AddCommGroup (VT' w)] [∀ w, Module (D.nd.O i) (VT' w)] [∀ w, TopologicalSpace (VT' w)]
  [∀ w, IsTopologicalAddGroup (VT' w)] [∀ w, ContinuousSMul (D.nd.O i) (VT' w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT' w)]
  (Dat : ∀ w, Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) (VT w) (VT' w))
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT)]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT)]
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]

theorem hfW_rep (n : ℕ) [ContinuousConstSMul (FractionRing (D.nd.O i)) (VT n)] (h : ReciprocityTheory.Gal.H1 (Dat n).ρT)
    (hh : h ∈ HfW i dc VT VT' Dat n) :
    ∃ c : ReciprocityTheory.Gal.Z1 (Dat n).ρT,
      Submodule.mkQ ((ReciprocityTheory.Gal.B1 (Dat n).ρT).comap (ReciprocityTheory.Gal.Z1 (Dat n).ρT).subtype) c = h ∧
      c.1 ∈ fZ i dc n (Dat n).ρT := by
  let S : Submodule (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat n).ρT) :=
    { carrier := {a | ∃ c : ReciprocityTheory.Gal.Z1 (Dat n).ρT,
        Submodule.mkQ ((ReciprocityTheory.Gal.B1 (Dat n).ρT).comap (ReciprocityTheory.Gal.Z1 (Dat n).ρT).subtype) c = a ∧
        c.1 ∈ fZ i dc n (Dat n).ρT}
      zero_mem' := ⟨0, map_zero _, (fZ i dc n (Dat n).ρT).zero_mem⟩
      add_mem' := by
        rintro a b ⟨c, rfl, hc⟩ ⟨c', rfl, hc'⟩
        exact ⟨c + c', map_add _ _ _, (fZ i dc n (Dat n).ρT).add_mem hc hc'⟩
      smul_mem' := by
        rintro k a ⟨c, rfl, hc⟩
        obtain ⟨kc, hkc, hmk⟩ := KBKa.mk_smul (Dat n).ρT k c
        refine ⟨kc, hmk, ?_⟩
        rw [hkc]
        exact (fZ i dc n (Dat n).ρT).smul_mem k hc }
  have hle : HfW i dc VT VT' Dat n ≤ S := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, rfl, hc⟩
  exact hle hh

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem frow_le_col (n : ℕ) [ContinuousConstSMul (FractionRing (D.nd.O i)) (VT n)]
    {M : Type} [AddCommGroup M] [Module (D.nd.O i) M] (ρM : Representation (D.nd.O i) ↥(Γn i dc n) M)
    (u : M ≃ₗ[D.nd.O i] (VT n ⧸ (Dat n).T)) (hu : ∀ g m, u (ρM g m) = (Dat n).ρA g (u m))
    {V : Type} [AddCommGroup V] [Module (FractionRing (D.nd.O i)) V] [Module (D.nd.O i) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V]
    (ρV : Representation (D.nd.O i) ↥(Γn i dc n) V) (qV : V →ₗ[D.nd.O i] M) (f : VT n →ₗ[D.nd.O i] V)
    (hf : ∀ g v, f ((Dat n).ρT g v) = ρV g (f v))
    (hq : ∀ x, u.symm (Submodule.Quotient.mk x) = qV (f x)) :
    (((HfW i dc VT VT' Dat n).restrictScalars (D.nd.O i)).map (Dat n).q).map (kRow (Dat n) ρM u hu) ≤
      F0col i dc n ρV ρM qV := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
  obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.1 hy
  obtain ⟨c, rfl, hcZ⟩ := hfW_rep i dc VT VT' Dat n h hh
  have hsym : ∀ g v, u.symm (Submodule.Quotient.mk ((Dat n).ρT g v)) =
      ρM g (u.symm (Submodule.Quotient.mk v)) := fun g v =>
    ReciprocityTheory.ChartRestriction.T2.trCompat_symm (MulEquiv.refl _) u ρM (Dat n).ρA hu g (Submodule.Quotient.mk v)
  have hcoc : (fun g => u.symm (Submodule.Quotient.mk (c.1 g))) ∈ coZ1s ρM := by
    intro g g'
    have e := c.2.2 g g'
    simp only at e ⊢
    rw [e, Submodule.Quotient.mk_add, map_add, hsym]
  have hk : kRow (Dat n) ρM u hu ((Dat n).q (Submodule.mkQ _ c)) =
      Submodule.mkQ _ (⟨_, hcoc⟩ : coZ1s ρM) := by
    show ReciprocityTheory.ChartRestriction.T2.traceH1 (MulEquiv.refl _) u ρM (Dat n).ρA hu
      (ReciprocityTheory.ChartRestriction.T2.toH1Cocycles (Dat n).ρA ((Dat n).q (Submodule.mkQ _ c))) = _
    simp only [Formalism.RepresentationBoundsCohomology.LOC.LatData.q, ReciprocityTheory.Gal.mapH1, ReciprocityTheory.ChartRestriction.T2.toH1Cocycles, ReciprocityTheory.ChartRestriction.T2.traceH1,
      Submodule.mkQ_apply, Submodule.mapQ_apply]
    congr 1
  rw [hk]
  refine Submodule.mem_map_of_mem (Submodule.mem_comap.2 (Submodule.mem_sup_left
    ⟨fun g => f (c.1 g), fZ_map i dc (Dat n).ρT ρV f hf _ hcZ, ?_⟩))
  funext g
  exact (hq _).symm

end Row

section LatRec

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {X' d : Type} [Fintype d] [DecidableEq d] {R' : Subalgebra O (X' → Matrix d d (FractionRing O))}
  {Tc : Type} [CommRing Tc] [Algebra Tc R']
  {Ek Ω : Type} [Field Ek] [Field Ω] [Algebra Ek Ω]
  (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) {t : ℕ} (bl : d → Fin (t + 1))
  (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
  (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (Aw : ℕ → ValuationSubring Ω)
  (hK : ContinuousMul (FractionRing O)) (hε : Continuous fun g => ((ε g : Oˣ) : O))
  (hM : ∀ a b, Continuous fun g => KLat.M0 r χ bl ρk g a b)

def idV (w : ℕ) :
    KLat.VT (O := O) bl w →ₗ[O] LatM O (FractionRing O) {a // bl a = 0} (ρk 0).toRingHom where
  toFun v := v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem idV_equiv (w : ℕ) (g : decs Ek Aw w) (v : KLat.VT (O := O) bl w) :
    idV bl ρk w ((KLat.Dat r χ bl ρk ε Aw hK hε hM w).ρT g v) =
      resRep (uRep O (M := LatM O (FractionRing O) {a // bl a = 0} (ρk 0).toRingHom) r χ) (decs Ek Aw w) g
        (idV bl ρk w v) := by
  funext a
  exact KLat.matK_mulVec _ _ a

theorem uD_symm_mk (w : ℕ) (x : KLat.VT (O := O) bl w) :
    (KLat.uD r χ bl ρk ε Aw hK hε hM w).symm (Submodule.Quotient.mk x) =
      qVM O {a // bl a = 0} (ρk 0).toRingHom (idV bl ρk w x) := by
  rfl

end LatRec

section Final

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
  {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i}
  {g0 : GE D.nd} {eB e₁ s : D.nd.X i → MatN D.nd i}
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))]
  (hK : ContinuousMul (FractionRing (D.nd.O i)))
  (hε : Continuous fun g => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i))
  (hM : ∀ a b, Continuous fun g => KLat.M0 Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk g a b)

abbrev rhoM (n : ℕ) : Representation (D.nd.O i) ↥(Γn i dc n) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) :=
  resRep (uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ) (decs D.host.E (Aw i dc) n)

abbrev rhoV (n : ℕ) : Representation (D.nd.O i) ↥(Γn i dc n) (VB i Dd) :=
  resRep (uRep (D.nd.O i) (M := VB i Dd) Dd.r Dd.χ) (decs D.host.E (Aw i dc) n)

abbrev DatK (w : ℕ) := KLat.Dat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) hK hε hM w

abbrev uDK (w : ℕ) := KLat.uD Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) hK hε hM w

variable [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (DatK i dc Dd hK hε hM w).ρT)]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (DatK i dc Dd hK hε hM w).ρT)]
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (DatK i dc Dd hK hε hM w).ρT')]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (DatK i dc Dd hK hε hM w).ρT')]

def FrowK (n : ℕ) : Submodule (D.nd.O i) (H1z (rhoM i dc Dd n)) :=
  (((HfW i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R))
      (DatK i dc Dd hK hε hM) n).restrictScalars (D.nd.O i)).map (DatK i dc Dd hK hε hM n).q).map
    (kRow (DatK i dc Dd hK hε hM n) (rhoM i dc Dd n) (uDK i dc Dd hK hε hM n)
      (KLat.huD Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) hK hε hM n))

def FcolK (n : ℕ) : Submodule (D.nd.O i) (H1z (rhoM i dc Dd n)) :=
  F0col i dc n (rhoV i dc Dd n) (rhoM i dc Dd n) (qB i Dd)

def FK (n : ℕ) : Submodule (D.nd.O i) (H1z (rhoM i dc Dd n)) :=
  Fρ i dc (rowsN i dc) (rhoM i dc Dd) (FrowK i dc Dd hK hε hM) (FcolK i dc Dd) n

set_option synthInstance.maxHeartbeats 400000 in

theorem fK_le (n : ℕ) : FK i dc Dd hK hε hM n ≤ FcolK i dc Dd n := by
  unfold FK Fρ
  split_ifs
  · haveI : ContinuousMul (FractionRing (D.nd.O i)) := hK
    exact frow_le_col i dc _ _ (DatK i dc Dd hK hε hM) n (rhoM i dc Dd n) (uDK i dc Dd hK hε hM n)
      (KLat.huD Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) hK hε hM n)
      (rhoV i dc Dd n) (qB i Dd) (idV (RepresentationBoundsCohomology.blk D.R) Dd.ρk n)
      (idV_equiv Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) hK hε hM n)
      (uD_symm_mk Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) hK hε hM n)
  · exact le_rfl

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem bkLoc_rec
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) :
    BkLoc i dc ρ π (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ (phi0 i Dd) (invariants_map_equivariant hD hN)
      (FK i dc Dd hK hε hM) := by
  intro n _ hw y hy
  exact bkLoc_col i dc ρ π _ Dd.r Dd.χ (phi0 i Dd) (invariants_map_equivariant hD hN) n hw (rhoV i dc Dd n) (qB i Dd)
    (psiB i Dd hw) (psiB_cont i Dd hw) (psiB_equiv dc hD hN n hw) (psiB_comp i Dd hw) y
    (fK_le i dc Dd hK hε hM n hy)

theorem tieSel1_K
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) :
    TieSel1 i ρ π (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc)
      (FK i dc Dd hK hε hM) (K.QS.Io i) :=
  tieSel1_rec_loc dc hD hN _ (bkLoc_rec i dc Dd hK hε hM hD hN)

end Final

end Formalism.MainNotions.N.K.Bk

end
