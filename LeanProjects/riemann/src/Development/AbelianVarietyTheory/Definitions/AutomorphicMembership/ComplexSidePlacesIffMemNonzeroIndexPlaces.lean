import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Divisibility.ColumnFamilyPlaceCharacterComap
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InGeoIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.VolumeLeOfTrivialFirstPair
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InclUInjective
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DefiniteSideNonzeroIndexPlacesAnyColumnsScale
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InGeoGeoScalIff

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Record

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt Wt' : Set X.B.places.Pl} (z : Dat X I hX T Wt)

namespace Dat

set_option maxHeartbeats 2000000 in

def restrict (hH : Holds z.R z.F) (Wt' : Set X.B.places.Pl) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') : Dat X I hX T Wt' where
  Xg := z.Xg
  tr := z.tr
  core := z.core
  alg := z.alg
  alg_eq := z.alg_eq
  R := z.resR h
  cG := z.cG
  geo := z.resGeo h
  pins := z.pins_resR h hc hH.aux.ex hH.prim.thmB
  lev := z.levOf_resR h
  idG := z.idG
  good := z.good
  mu := z.muOf_res h
  fieldValues_mem_fixedField := z.fieldValues_mem_fixedField
  Ks_le := z.Ks_le

theorem restrict_Xg_tr_core (hH : Holds z.R z.F) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') :
    (z.restrict hH Wt' h hc).Xg = z.Xg ∧ (z.restrict hH Wt' h hc).tr = z.tr ∧ (z.restrict hH Wt' h hc).core = z.core := ⟨rfl, rfl, rfl⟩

theorem restrict_R (hH : Holds z.R z.F) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') : (z.restrict hH Wt' h hc).R = z.resR h := rfl

theorem restrictRealData_constant_error (h : Wt' ⊆ Wt) : (z.resR h).kap = z.R.kap ∧ (z.resR h).err0 = z.R.err0 := ⟨rfl, rfl⟩

set_option maxHeartbeats 1000000 in

theorem restrictRealData_lift_scalar (h : Wt' ⊆ Wt) (i : Fin X.toD7.R.m) (t : TupU I (usedOf I T Wt')) :
    (z.resR h).lam3 i t = z.R.lam3 i (inclU I (usedOf_mono I T h) t) := rfl

theorem resR_mu_twPl (h : Wt' ⊆ Wt) : (z.resR h).mu = z.resMu h ∧ (z.resR h).twPl = z.resTw Wt' := ⟨rfl, rfl⟩

theorem restrict_holds (hH : Holds z.R z.F) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') :
    Holds (z.restrict hH Wt' h hc).R (z.restrict hH Wt' h hc).F := z.holds_resR h hH

set_option maxHeartbeats 2000000 in

theorem inGeo_resGeo_iff (h : Wt' ⊆ Wt) : GlobalTheory.RealGeo.InGeo (z.resGeo h) ↔ GlobalTheory.RealGeo.InGeo z.geo :=
  Res.inGeo_iff (A := (famR X I hX (usedOf I T Wt) z.Xg z.tr).A) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R.toRealDat) (z.resMu h) (z.resTw Wt') (g := z.geo)

theorem restrict_inGeo_iff (hH : Holds z.R z.F) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') :
    GlobalTheory.RealGeo.InGeo (z.restrict hH Wt' h hc).geo ↔ GlobalTheory.RealGeo.InGeo z.geo := z.inGeo_resGeo_iff h

variable (F0 : HeightOneSpectrum (𝓞 X.toD7.what₂.LL) → Fin X.toD7.R.m → ℝ)

theorem mem_nonzero_index_places_iff_at_place_or_conjugate (w : X.B.places.Pl) :
    w ∈ z.W1 F0 ↔ ∃ j, NzAt z.R z.F F0 j (plB X w) ∨ NzAt z.R z.F F0 j (Formalism.DivisionValues.conjPl (plB X w)) := by
  refine exists_congr fun j => ⟨?_, ?_⟩
  · rintro ⟨w', rfl | rfl, h⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩

theorem nonzero_index_places_conj_stable : ConjStable X (z.W1 F0) := by
  intro w hw
  rw [mem_nonzero_index_places_iff_at_place_or_conjugate] at hw ⊢
  rw [plB_conj, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
  exact hw.imp fun _ h => h.symm

set_option maxHeartbeats 2000000 in

theorem nzAt_resR (h : Wt' ⊆ Wt) (j : Fin X.toD7.R.m) (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) :
    NzAt (z.resR h) (face0 X I hX (usedOf I T Wt') z.Xg z.tr) F0 j v ↔ NzAt z.R (face0 X I hX (usedOf I T Wt) z.Xg z.tr) F0 j v := by
  rw [columnChoiceReferenceFace_eq_bareFaceTwoLevels, columnChoiceReferenceFace_eq_bareFaceTwoLevels]
  exact nzAt_res (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (Ks := z.core.Q.c.F) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) z.R (z.resMu h) (z.resTw Wt') (lev0 I) (chr0 I) (lev1 I) (chr1 I) F0 j v

theorem restrict_nonzero_places_eq (hH : Holds z.R z.F) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') : (z.restrict hH Wt' h hc).W1 F0 = z.W1 F0 := by
  ext w
  rw [mem_nonzero_index_places_iff_at_place_or_conjugate, mem_nonzero_index_places_iff_at_place_or_conjugate]
  exact exists_congr fun j => or_congr (z.nzAt_resR F0 h j _) (z.nzAt_resR F0 h j _)

theorem complex_side_places_iff_mem_nonzero_index_places (kap lam err) (Dc Sp Zsc) (N : IndefNum (famR X I hX (usedOf I T Wt) z.Xg z.tr).fam3.base3) (hN : N.F0 = F0)
    (w : X.B.places.Pl) :
    (((z.R.updS kap lam).withErr err).toCx3 (reFace z.F Dc Sp Zsc)).W1 (reFace z.F Dc Sp Zsc).cr N (X.toD7.plEq w) ↔ w ∈ z.W1 F0 := by
  subst hN
  exact (complexSide_nonzeroIndexPlaces_iff z.R z.F kap lam err Dc Sp Zsc N (plB X w)).trans (z.mem_nonzero_index_places_iff_at_place_or_conjugate N.F0 w).symm

theorem complex_side_face_numbers_iff_mem_nonzero_index_places (kap lam err) (Dc Sp Zsc) (C CH : ℝ) (hZ : (Zsc (zsOf z.R z.F)).F0 = F0) (w : X.B.places.Pl) :
    (((z.R.updS kap lam).withErr err).toCx3 (reFace z.F Dc Sp Zsc)).W1 (reFace z.F Dc Sp Zsc).cr
      (((z.R.updS kap lam).withErr err).num (reFace z.F Dc Sp Zsc) C CH) (X.toD7.plEq w) ↔ w ∈ z.W1 F0 :=
  z.complex_side_places_iff_mem_nonzero_index_places F0 kap lam err Dc Sp Zsc _ ((complexSide_numberContents_eq_scaleAtSubspaces z.R z.F kap lam err Dc Sp Zsc C CH).trans hZ) w

theorem twisted_places_eq_complex_side_of_eq_nonzero_index (hW : z.W1 F0 = Wt) (kap lam err) (Dc Sp Zsc) (C CH : ℝ) (hZ : (Zsc (zsOf z.R z.F)).F0 = F0)
    (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) :
    v ∈ ((z.R.updS kap lam).withErr err).twPl ↔
      (((z.R.updS kap lam).withErr err).toCx3 (reFace z.F Dc Sp Zsc)).W1 (reFace z.F Dc Sp Zsc).cr
        (((z.R.updS kap lam).withErr err).num (reFace z.F Dc Sp Zsc) C CH) v := by
  obtain ⟨w, rfl⟩ := (plB X).surjective v
  exact (z.plB_mem_twPl w).trans ((Set.ext_iff.1 hW w).symm.trans (z.complex_side_face_numbers_iff_mem_nonzero_index_places F0 kap lam err Dc Sp Zsc C CH hZ w).symm)

def restrictNonzero (hH : Holds z.R z.F) (h : z.W1 F0 ⊆ Wt) : Dat X I hX T (z.W1 F0) := z.restrict hH (z.W1 F0) h (z.nonzero_index_places_conj_stable F0)

theorem restrictNonzero_nonzero_places (hH : Holds z.R z.F) (h : z.W1 F0 ⊆ Wt) : (z.restrictNonzero F0 hH h).W1 F0 = z.W1 F0 :=
  z.restrict_nonzero_places_eq F0 hH h (z.nonzero_index_places_conj_stable F0)

theorem restrictNonzero_mem_twisted_iff (hH : Holds z.R z.F) (h : z.W1 F0 ⊆ Wt) (w : X.B.places.Pl) :
    X.toD7.plEq w ∈ (z.restrictNonzero F0 hH h).R.twPl ↔ w ∈ (z.restrictNonzero F0 hH h).W1 F0 := by
  rw [restrictNonzero_nonzero_places]
  exact (z.restrictNonzero F0 hH h).plB_mem_twPl w

theorem restrictNonzero_holds (hH : Holds z.R z.F) (h : z.W1 F0 ⊆ Wt) : Holds (z.restrictNonzero F0 hH h).R (z.restrictNonzero F0 hH h).F :=
  z.restrict_holds hH h (z.nonzero_index_places_conj_stable F0)

theorem restrictNonzero_geometry_iff (hH : Holds z.R z.F) (h : z.W1 F0 ⊆ Wt) :
    GlobalTheory.RealGeo.InGeo (z.restrictNonzero F0 hH h).geo ↔ GlobalTheory.RealGeo.InGeo z.geo := z.restrict_inGeo_iff hH h (z.nonzero_index_places_conj_stable F0)

theorem restrictNonzero_twisted_iff_complex (hH : Holds z.R z.F) (h : z.W1 F0 ⊆ Wt) (kap lam err) (Dc Sp Zsc) (C CH : ℝ)
    (hZ : (Zsc (zsOf (z.restrictNonzero F0 hH h).R (z.restrictNonzero F0 hH h).F)).F0 = F0) (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) :
    v ∈ (((z.restrictNonzero F0 hH h).R.updS kap lam).withErr err).twPl ↔
      ((((z.restrictNonzero F0 hH h).R.updS kap lam).withErr err).toCx3 (reFace (z.restrictNonzero F0 hH h).F Dc Sp Zsc)).W1
        (reFace (z.restrictNonzero F0 hH h).F Dc Sp Zsc).cr
        ((((z.restrictNonzero F0 hH h).R.updS kap lam).withErr err).num (reFace (z.restrictNonzero F0 hH h).F Dc Sp Zsc) C CH) v :=
  (z.restrictNonzero F0 hH h).twisted_places_eq_complex_side_of_eq_nonzero_index F0 (z.restrictNonzero_nonzero_places F0 hH h) kap lam err Dc Sp Zsc C CH hZ v

set_option maxHeartbeats 4000000 in

def restrictE (e : z.R.toRealDat.ExAt) (Wt' : Set X.B.places.Pl) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') : Dat X I hX T Wt' where
  Xg := z.Xg
  tr := z.tr
  core := z.core
  alg := z.alg
  alg_eq := z.alg_eq
  R := z.resRE h
  cG := z.cG
  geo := z.resGeoE h
  pins := z.pins_resRE h hc e
  lev := z.levOf_resR h
  idG := z.idG
  good := z.good
  mu := z.muOf_res h
  fieldValues_mem_fixedField := z.fieldValues_mem_fixedField
  Ks_le := z.Ks_le

section Ex

variable (e : z.R.toRealDat.ExAt) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt')

theorem restrictE_Xg_tr_core :
    (z.restrictE e Wt' h hc).Xg = z.Xg ∧ (z.restrictE e Wt' h hc).tr = z.tr ∧ (z.restrictE e Wt' h hc).core = z.core := ⟨rfl, rfl, rfl⟩

theorem restrictE_R : (z.restrictE e Wt' h hc).R = (z.resR h).updS (Res.kapNew (z.resR h)) (z.resR h).lam3 := rfl

set_option maxHeartbeats 2000000 in

theorem restrictOfExists_lift_scalar (i : Fin X.toD7.R.m) (t : TupU I (usedOf I T Wt')) :
    (z.restrictE e Wt' h hc).R.lam3 i t = z.R.lam3 i (inclU I (usedOf_mono I T h) t) := z.restrictRealData_lift_scalar h i t

set_option maxHeartbeats 2000000 in

theorem restrictOfExists_error_tuples_twisted : (z.restrictE e Wt' h hc).R.err0 = z.R.err0 ∧ (z.restrictE e Wt' h hc).R.mu = z.resMu h ∧
    (z.restrictE e Wt' h hc).R.twPl = z.resTw Wt' := ⟨rfl, rfl, rfl⟩

theorem restrictE_R_of_thmB (hB : z.R.PThmB) : (z.restrictE e Wt' h hc).R = z.resR h := z.resRE_of_thmB h hB

set_option maxHeartbeats 2000000 in

theorem restrictE_kap (hB : z.R.PThmB) : (z.restrictE e Wt' h hc).R.kap = z.R.kap :=
  (Res.kapNew_of_thmB (z.resR h) (z.thmB_resR h hB)).trans (z.restrictRealData_constant_error h).1

theorem restrictE_R_eq_restrict (hH : Holds z.R z.F) : (z.restrictE e Wt' h hc).R = (z.restrict hH Wt' h hc).R :=
  z.resRE_of_thmB h hH.prim.thmB

theorem restrictE_exAt : (z.restrictE e Wt' h hc).R.toRealDat.ExAt := z.exAt_resRE h e

set_option maxHeartbeats 4000000 in

theorem restrictE_holds (hH : Holds z.R z.F) : Holds (z.restrictE e Wt' h hc).R (z.restrictE e Wt' h hc).F := by
  rw [z.restrictE_R_of_thmB e h hc hH.prim.thmB]
  exact z.holds_resR h hH

set_option maxHeartbeats 4000000 in

theorem restrictE_inGeo_iff : GlobalTheory.RealGeo.InGeo (z.restrictE e Wt' h hc).geo ↔ GlobalTheory.RealGeo.InGeo z.geo :=
  (Res.inGeo_geoScal_iff (z.resGeo h) (Res.kapNew (z.resR h)) (z.resR h).lam (z.resR h).err0).trans (z.inGeo_resGeo_iff h)

set_option maxHeartbeats 4000000 in

theorem restrictOfExists_nonzero_places : (z.restrictE e Wt' h hc).W1 F0 = z.W1 F0 := by
  ext w
  rw [mem_nonzero_index_places_iff_at_place_or_conjugate, mem_nonzero_index_places_iff_at_place_or_conjugate]
  have key : ∀ j v, NzAt ((z.resR h).updS (Res.kapNew (z.resR h)) (z.resR h).lam3) (face0 X I hX (usedOf I T Wt') z.Xg z.tr) F0 j v ↔
      NzAt z.R z.F F0 j v := fun j v => (Res.nzAt_scal _ _ _ _ F0 j v).trans (z.nzAt_resR F0 h j v)
  exact exists_congr fun j => or_congr (key j _) (key j _)

end Ex

theorem restrict_exAt (hH : Holds z.R z.F) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') : (z.restrict hH Wt' h hc).R.toRealDat.ExAt :=
  z.exAt_resR h hH.aux.ex

def restrictNonzeroOfExists (e : z.R.toRealDat.ExAt) (h : z.W1 F0 ⊆ Wt) : Dat X I hX T (z.W1 F0) :=
  z.restrictE e (z.W1 F0) h (z.nonzero_index_places_conj_stable F0)

section ExW

variable (e : z.R.toRealDat.ExAt) (h : z.W1 F0 ⊆ Wt)

theorem restrictNonzeroOfExists_characters_eq :
    (z.restrictNonzeroOfExists F0 e h).Xg = z.Xg ∧ (z.restrictNonzeroOfExists F0 e h).tr = z.tr ∧ (z.restrictNonzeroOfExists F0 e h).core = z.core := ⟨rfl, rfl, rfl⟩

theorem restrictNonzeroOfExists_nonzero_places : (z.restrictNonzeroOfExists F0 e h).W1 F0 = z.W1 F0 := z.restrictOfExists_nonzero_places F0 e h (z.nonzero_index_places_conj_stable F0)

theorem restrictNonzeroOfExists_mem_twisted_iff (w : X.B.places.Pl) :
    X.toD7.plEq w ∈ (z.restrictNonzeroOfExists F0 e h).R.twPl ↔ w ∈ (z.restrictNonzeroOfExists F0 e h).W1 F0 := by
  rw [restrictNonzeroOfExists_nonzero_places]
  exact (z.restrictNonzeroOfExists F0 e h).plB_mem_twPl w

theorem restrictNonzeroOfExists_exists_lifts : (z.restrictNonzeroOfExists F0 e h).R.toRealDat.ExAt := z.restrictE_exAt e h (z.nonzero_index_places_conj_stable F0)

theorem restrictNonzeroOfExists_holds (hH : Holds z.R z.F) : Holds (z.restrictNonzeroOfExists F0 e h).R (z.restrictNonzeroOfExists F0 e h).F :=
  z.restrictE_holds e h (z.nonzero_index_places_conj_stable F0) hH

theorem restrictNonzeroOfExists_geometry_iff : GlobalTheory.RealGeo.InGeo (z.restrictNonzeroOfExists F0 e h).geo ↔ GlobalTheory.RealGeo.InGeo z.geo :=
  z.restrictE_inGeo_iff e h (z.nonzero_index_places_conj_stable F0)

theorem restrictNonzeroOfExists_twisted_iff_complex (kap lam err) (Dc Sp Zsc) (C CH : ℝ)
    (hZ : (Zsc (zsOf (z.restrictNonzeroOfExists F0 e h).R (z.restrictNonzeroOfExists F0 e h).F)).F0 = F0) (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) :
    v ∈ (((z.restrictNonzeroOfExists F0 e h).R.updS kap lam).withErr err).twPl ↔
      ((((z.restrictNonzeroOfExists F0 e h).R.updS kap lam).withErr err).toCx3 (reFace (z.restrictNonzeroOfExists F0 e h).F Dc Sp Zsc)).W1
        (reFace (z.restrictNonzeroOfExists F0 e h).F Dc Sp Zsc).cr
        ((((z.restrictNonzeroOfExists F0 e h).R.updS kap lam).withErr err).num (reFace (z.restrictNonzeroOfExists F0 e h).F Dc Sp Zsc) C CH) v :=
  (z.restrictNonzeroOfExists F0 e h).twisted_places_eq_complex_side_of_eq_nonzero_index F0 (z.restrictNonzeroOfExists_nonzero_places F0 e h) kap lam err Dc Sp Zsc C CH hZ v

end ExW

example (e : z.R.toRealDat.ExAt) : (z.restrictE e ∅ (Set.empty_subset _) fun _ h => h.elim).R.twPl = ∅ :=
  Finset.eq_empty_of_forall_notMem fun v hv => (Dat.mem_twPl _ v).1 hv

example : Res.kapNew z.R = z.R.kap := Res.kapNew_of_scal z.R z.pins.char.scal.kap

example (hH : Holds z.R z.F) : (z.restrict hH ∅ (Set.empty_subset _) fun _ h => h.elim).R.twPl = ∅ :=
  Finset.eq_empty_of_forall_notMem fun v hv => (Dat.mem_twPl _ v).1 hv

example : z.resTw Wt = z.R.twPl := Finset.ext fun v => (z.mem_resTw subset_rfl v).trans (z.mem_twPl v).symm

include z in

theorem conjStable : ConjStable X Wt := by
  intro w hw
  have ht := z.pins.char.tup
  rw [← z.plB_mem_twPl, plB_conj]
  by_contra hn
  exact ht.mu_ne _ ((z.plB_mem_twPl w).2 hw) ((ht.mu_conj _).symm.trans (ht.mu_off _ hn))

example (w : X.B.places.Pl) (j : Fin X.toD7.R.m) (h : F0 (plB X w) j ≠ 0) : w ∈ z.W1 F0 :=
  (z.mem_nonzero_index_places_iff_at_place_or_conjugate F0 w).2 ⟨j, Or.inl (Or.inr (Or.inr h))⟩

end Dat

end Record

end GlobalTheory.Mem.R3

end
