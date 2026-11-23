import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ComplexSidePlacesIffMemNonzeroIndexPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeoHalfUpd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.ResEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

open GlobalTheory.Mem.R3.Res

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 2000000 in

theorem baseWeight_scalar_update_invariant {A : FamIn D.what₂.LL G Pl0 T D.R.m} {R : RealDat D A Ks} {F : Face D A} (h : R.BaseW F) (k l) :
    (R.upd6 k l).BaseW F :=
  ⟨h.lev, ⟨h.grp.red_R, h.grp.red_L, h.grp.levels, h.grp.record, h.grp.chiW⟩,
    ⟨h.fam.tie, h.fam.Sb, h.fam.roots, h.fam.pl_onto, h.fam.degR, h.fam.degL, h.fam.muVal, h.fam.etaVal⟩,
    ⟨h.models.inf, h.models.vpos, h.models.cX, h.models.cV, h.models.prX, h.models.HX, h.models.HV, h.models.HE, h.models.HW,
      h.models.gE, h.models.gW, h.models.jX, h.models.jV, h.models.νY, h.models.νY', h.models.ν0, h.models.νX, h.models.νV,
      h.models.νW, h.models.BV, h.models.order⟩, RealDat.weak_chain_of_scalar_update h.chain k l, RealDat.weak_theta_props_of_scalar_update h.thP k l⟩

set_option maxHeartbeats 2000000 in

theorem intertwinersExist_scalar_update_invariant {A : FamIn D.what₂.LL G Pl0 T D.R.m} {R : RealDat D A Ks} (e : R.ExAt) (k l) : (R.upd6 k l).ExAt :=
  ⟨e.ItY, e.ItX, e.ioY, e.ioX, e.Th, e.ioP, e.thF, e.thG⟩

set_option maxHeartbeats 2000000 in

theorem nz_updS (R : RealDat3 D A3 Ks) (F : Face3 D A3) (k l) (F0 : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ)
    (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (∃ j, NzAt (R.updS k l) F F0 j w ∨ NzAt (R.updS k l) F F0 j (Formalism.DivisionValues.conjPl w)) ↔
      ∃ j, NzAt R F F0 j w ∨ NzAt R F F0 j (Formalism.DivisionValues.conjPl w) :=
  (complexSide_nonzeroIndexPlaces_iff_self (R.updS k l) F { R.num F 0 0 with F0 := F0 } w).symm.trans
    (complexSide_nonzeroIndexPlaces_iff R F k l R.err0 F.Dc F.Sp F.Zsc { R.num F 0 0 with F0 := F0 } w)

open Classical in

def kapOf (S : RealDat3 D A3 Ks) : ℝ :=
  if h : ∃ κ, Lift.IsKap D.R.m (fun t => S.Th t ∘ₗ LinearMap.adjoint (S.Th t)) S.EEp3 S.lamN κ ∧
      ∃ t p, S.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, S.lamN t j p ≠ 0 then h.choose else S.kap

theorem kapOf_eq (S : RealDat3 D A3 Ks) (κ : ℝ)
    (hκ : Lift.IsKap D.R.m (fun t => S.Th t ∘ₗ LinearMap.adjoint (S.Th t)) S.EEp3 S.lamN κ)
    (hn : ∃ t p, S.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, S.lamN t j p ≠ 0) : kapOf S = κ := by
  have h : ∃ κ, Lift.IsKap D.R.m (fun t => S.Th t ∘ₗ LinearMap.adjoint (S.Th t)) S.EEp3 S.lamN κ ∧
      ∃ t p, S.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, S.lamN t j p ≠ 0 := ⟨κ, hκ, hn⟩
  obtain ⟨t, p, hp, hl⟩ := hn
  unfold kapOf
  rw [dif_pos h]
  exact Lift.IsKap.unique h.choose_spec.1 hκ t p hp hl

theorem kapOf_of_thmB (S : RealDat3 D A3 Ks) (hB : S.PThmB) : kapOf S = S.kap := by
  by_cases hn : ∃ t p, S.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, S.lamN t j p ≠ 0
  · exact kapOf_eq S _ hB hn
  · unfold kapOf
    exact dif_neg fun h => hn h.choose_spec.2

set_option maxHeartbeats 2000000 in

theorem isScal_kapOf (S : RealDat3 D A3 Ks) (F : Face3 D A3) (h0 : S.eigenvalue_at_base_of_scalar) (h1 : S.scal_off F) (h2 : S.zero_part_eigenvalue_convention F)
    (h3 : S.scal_abs F) (h4 : S.scal_tup) : (S.updS (kapOf S) S.lam3).IsScal F := by
  refine ⟨h0, fun κ h h' => kapOf_eq S κ h h', fun i p v l hv hp he => ?_, fun i t p hp => ?_, fun i p v hv hp => ?_, h4⟩
  · exact h1 i p v l hv ((RealDat3.partAt_updS _ _ _ _ _).1 hp) ((RealDat3.sim_updS _ _ _ _ _ _).1 he)
  · rw [RealDat3.zs_updS]
    exact h2 i t p hp
  · rw [RealDat3.zs_updS]
    exact h3 i p v hv fun hl => hp ((RealDat3.partAt_updS _ _ _ _ _).2 hl)

variable {f : T' → T} {μ : T'} {R : RealDat3 D (A3.comap id (f μ)) Ks} {mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T'}
  {tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))} {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G} {ψ1 : P1 →* D.what₂.LLˣ}

set_option maxHeartbeats 4000000 in

theorem pins_updS (hf : Function.Injective f) {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (h : Pins R (bare3 _ P0 ψ0 P1 ψ1) cG)
    (e : R.toRealDat.ExAt) (n : NewTup R mu tw) (k l) (hs : ((dat3 f μ R mu tw).updS k l).IsScal (bare3 _ P0 ψ0 P1 ψ1)) :
    Pins ((dat3 f μ R mu tw).updS k l) (bare3 _ P0 ψ0 P1 ψ1) cG := by
  have i := isInert mu tw h.char.inert
  have u := isTup hf h.char.tup n
  have kv := keep mu tw h.keep
  exact ⟨⟨baseWeight_scalar_update_invariant (baseW (A := A3.A) mu tw hf h.char.base e) k _, ⟨i.tie, i.onto, i.hR, i.hL, i.SF⟩,
      fun t => h.char.fullY (f t), fun t => h.char.fullX (f t), fun i t => h.char.fullP i (f t), hs,
      ⟨u.mu_off, u.mu_used, u.mu_ne, u.mu_conj, u.mu_on⟩, h.char.phase, h.char.allPl⟩,
    ⟨kv.std, kv.signs, kv.frames, kv.beta, kv.prX, kv.grp, kv.psi, kv.guard, kv.valKs, kv.frameKs, kv.levKs⟩, h.phs, h.trSem⟩

set_option maxHeartbeats 4000000 in

theorem pins_kapOf (hf : Function.Injective f) {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (h : Pins R (bare3 _ P0 ψ0 P1 ψ1) cG)
    (e : R.toRealDat.ExAt) (n : NewTup R mu tw) :
    Pins ((dat3 f μ R mu tw).updS (kapOf (dat3 f μ R mu tw)) (dat3 f μ R mu tw).lam3) (bare3 _ P0 ψ0 P1 ψ1) cG :=
  pins_updS hf h e n _ _ (isScal_kapOf _ _ (fun i t => h.char.scal.lam0 i (f t)) h.char.scal.off
    (fun i t => h.char.scal.abs0 i (f t)) h.char.scal.abs fun i t => h.char.scal.tup i (f t))

end Generic

section Record

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt Wt' : Set X.B.places.Pl}

set_option maxHeartbeats 4000000 in

theorem pins_res (z : Dat X I hX T Wt) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') (e : z.R.toRealDat.ExAt) (k l)
    (hs : ((z.resR h).updS k l).IsScal (face0 X I hX (usedOf I T Wt') z.Xg z.tr)) :
    Pins ((z.resR h).updS k l) (face0 X I hX (usedOf I T Wt') z.Xg z.tr) z.cG := by
  have hp := z.pins
  rw [columnChoiceReferenceFace_eq_bareFaceTwoLevels] at hp hs ⊢
  exact pins_updS (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (Ks := z.core.Q.c.F) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R) (P0 := lev0 I) (ψ0 := chr0 I) (P1 := lev1 I) (ψ1 := chr1 I)
    (mu := z.resMu h) (tw := z.resTw Wt') (inclU_injective (usedOf_mono I T h)) (cG := z.cG) hp e (z.newTup h hc) k l hs

set_option maxHeartbeats 4000000 in

theorem exAt_res (z : Dat X I hX T Wt) (h : Wt' ⊆ Wt) (e : z.R.toRealDat.ExAt) : (z.resR h).toRealDat.ExAt :=
  Res.exAt (A := (famR X I hX (usedOf I T Wt) z.Xg z.tr).A) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R.toRealDat) (z.resMu h) (z.resTw Wt') e

set_option maxHeartbeats 4000000 in

theorem exists_restrict (z : Dat X I hX T Wt) (e : z.R.toRealDat.ExAt) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') :
    ∃ z' : Dat X I hX T Wt', z'.Xg = z.Xg ∧ z'.tr = z.tr ∧ z'.core = z.core ∧ z'.R.toRealDat.ExAt ∧
      (GlobalTheory.RealGeo.InGeo z.geo → GlobalTheory.RealGeo.InGeo z'.geo) ∧ ∀ F0, z'.W1 F0 = z.W1 F0 := by
  obtain ⟨k, l, hs⟩ := scalars_exist (F := face0 X I hX (usedOf I T Wt') z.Xg z.tr) (z.resR h)
  obtain ⟨g, -, -, hg⟩ := GlobalTheory.RealGeo.geoHalf_upd X.toD7 _ _ _ _ z.core (z.resR h).toRealDat (fun _ => 1) k (z.resR h).lam
    (z.resR h).err0 (z.resGeo h)
  refine ⟨{ Xg := z.Xg, tr := z.tr, core := z.core, alg := z.alg, alg_eq := z.alg_eq, R := (z.resR h).updS k l, cG := z.cG,
            geo := g, pins := pins_res z h hc e k l hs, lev := z.levOf_resR h, idG := z.idG, good := z.good, mu := z.muOf_res h,
            fieldValues_mem_fixedField := z.fieldValues_mem_fixedField, Ks_le := z.Ks_le }, rfl, rfl, rfl, intertwinersExist_scalar_update_invariant (exAt_res z h e) k _,
    fun hi => hg ((z.inGeo_resGeo_iff h).2 hi), fun F0 => ?_⟩
  ext w
  rw [Dat.mem_nonzero_index_places_iff_at_place_or_conjugate, Dat.mem_nonzero_index_places_iff_at_place_or_conjugate]
  exact (nz_updS (z.resR h) _ k l F0 _).trans (exists_congr fun j => or_congr (z.nzAt_resR F0 h j _) (z.nzAt_resR F0 h j _))

theorem exists_exact (z : Dat X I hX T Wt) (hL : Rw.HoldsL z.R z.F) (F0) (h : z.W1 F0 ⊆ Wt) :
    ∃ z' : Dat X I hX T (z.W1 F0), z'.core = z.core ∧ z'.R.toRealDat.ExAt ∧
      (GlobalTheory.RealGeo.InGeo z.geo → GlobalTheory.RealGeo.InGeo z'.geo) ∧ z.W1 F0 = z'.W1 F0 := by
  obtain ⟨z', -, -, h1, h2, h3, h4⟩ := exists_restrict z hL.aux.ex h (z.nonzero_index_places_conj_stable F0)
  exact ⟨z', h1, h2, h3, (h4 F0).symm⟩

set_option maxHeartbeats 4000000 in

theorem pins_resK (z : Dat X I hX T Wt) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') (e : z.R.toRealDat.ExAt) :
    Pins ((z.resR h).updS (kapOf (z.resR h)) (z.resR h).lam3) (face0 X I hX (usedOf I T Wt') z.Xg z.tr) z.cG := by
  have hp := z.pins
  rw [columnChoiceReferenceFace_eq_bareFaceTwoLevels] at hp ⊢
  exact pins_kapOf (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (Ks := z.core.Q.c.F) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R) (P0 := lev0 I) (ψ0 := chr0 I) (P1 := lev1 I) (ψ1 := chr1 I)
    (mu := z.resMu h) (tw := z.resTw Wt') (inclU_injective (usedOf_mono I T h)) (cG := z.cG) hp e (z.newTup h hc)

set_option maxHeartbeats 4000000 in

def restrictEx (z : Dat X I hX T Wt) (e : z.R.toRealDat.ExAt) (Wt' : Set X.B.places.Pl) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') :
    Dat X I hX T Wt' where
  Xg := z.Xg
  tr := z.tr
  core := z.core
  alg := z.alg
  alg_eq := z.alg_eq
  R := (z.resR h).updS (kapOf (z.resR h)) (z.resR h).lam3
  cG := z.cG
  geo := (GlobalTheory.RealGeo.geoHalf_upd X.toD7 _ _ _ _ z.core (z.resR h).toRealDat (fun _ => 1) (kapOf (z.resR h)) (z.resR h).lam
    (z.resR h).err0 (z.resGeo h)).choose
  pins := pins_resK z h hc e
  lev := z.levOf_resR h
  idG := z.idG
  good := z.good
  mu := z.muOf_res h
  fieldValues_mem_fixedField := z.fieldValues_mem_fixedField
  Ks_le := z.Ks_le

variable (z : Dat X I hX T Wt) (e : z.R.toRealDat.ExAt) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt')

theorem restrictEx_core : (restrictEx z e Wt' h hc).core = z.core := rfl

theorem restrictEx_exAt : (restrictEx z e Wt' h hc).R.toRealDat.ExAt := intertwinersExist_scalar_update_invariant (exAt_res z h e) _ _

set_option maxHeartbeats 4000000 in

theorem restrictEx_inGeo (hi : GlobalTheory.RealGeo.InGeo z.geo) : GlobalTheory.RealGeo.InGeo (restrictEx z e Wt' h hc).geo :=
  (GlobalTheory.RealGeo.geoHalf_upd X.toD7 _ _ _ _ z.core (z.resR h).toRealDat (fun _ => 1) (kapOf (z.resR h)) (z.resR h).lam
    (z.resR h).err0 (z.resGeo h)).choose_spec.2.2 ((z.inGeo_resGeo_iff h).2 hi)

set_option maxHeartbeats 4000000 in

theorem restrictExists_nonzero_places (F0) : (restrictEx z e Wt' h hc).W1 F0 = z.W1 F0 := by
  ext w
  rw [Dat.mem_nonzero_index_places_iff_at_place_or_conjugate, Dat.mem_nonzero_index_places_iff_at_place_or_conjugate]
  exact (nz_updS (z.resR h) _ _ _ F0 _).trans (exists_congr fun j => or_congr (z.nzAt_resR F0 h j _) (z.nzAt_resR F0 h j _))

set_option maxHeartbeats 4000000 in

theorem restrictEx_R_of_holds (hH : Holds z.R z.F) : (restrictEx z e Wt' h hc).R = z.resR h :=
  (congrArg (fun k => (z.resR h).updS k (z.resR h).lam3) (kapOf_of_thmB (z.resR h) (z.holds_resR h hH).prim.thmB)).trans rfl

set_option maxHeartbeats 4000000 in

theorem restrictEx_holds (hH : Holds z.R z.F) : Holds (restrictEx z e Wt' h hc).R (restrictEx z e Wt' h hc).F := by
  rw [restrictEx_R_of_holds z e h hc hH]
  exact z.holds_resR h hH

end Record

end GlobalTheory.Mem.R3.ResEx

end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.ResTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt Wt' Wt'' : Set X.B.places.Pl} (z : Dat X I hX T Wt)

theorem resMu_self : z.resMu subset_rfl = z.R.mu := by
  funext v
  by_cases hv : (plB X).symm v ∈ Wt
  · exact inclU_injective (usedOf_mono I T subset_rfl) (z.inclU_resMu subset_rfl hv)
  · exact (z.resMu_off subset_rfl hv).trans (z.pins.char.tup.mu_off v fun h => hv ((z.mem_twPl v).1 h)).symm

theorem resTw_self : z.resTw Wt = z.R.twPl := Finset.ext fun v => (z.mem_resTw subset_rfl v).trans (z.mem_twPl v).symm

theorem tup_empty (z : Dat X I hX T Wt) (t : TupU I (usedOf I T (∅ : Set X.B.places.Pl))) :
    t = mu0F (X := X.B.fields) (tuOf I (usedOf I T ∅)) := by
  rcases z.resMu_used (Set.empty_subset _) t with h | ⟨v, h⟩
  · exact h
  · exact h.symm.trans (z.resMu_off _ fun h => h)

theorem inclU_not_surjective (z : Dat X I hX T Wt) {w} (hw : w ∈ Wt) :
    ¬ Function.Surjective (inclU I (usedOf_mono I T (Set.empty_subset Wt))) := by
  intro h
  obtain ⟨t, ht⟩ := h (z.R.mu (plB X w))
  rw [tup_empty z t] at ht
  exact z.pins.char.tup.mu_ne _ ((z.plB_mem_twPl w).2 hw) ht.symm

theorem conj_needed (h : ¬ ConjStable X Wt') : IsEmpty (Dat X I hX T Wt') := ⟨fun y => h y.conjStable⟩

theorem finite_of_dat (z : Dat X I hX T Wt) : Wt.Finite :=
  (z.R.twPl.finite_toSet.preimage (plB X).injective.injOn).subset fun w hw => (z.plB_mem_twPl w).2 hw

theorem restrictE_twice (e : z.R.toRealDat.ExAt) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') (h' : Wt'' ⊆ Wt') :
    (z.restrictE e Wt' h hc).resTw Wt'' = z.resTw Wt'' ∧ (z.restrictE e Wt' h hc).resMu h' = z.resMu (h'.trans h) := by
  refine ⟨Finset.ext fun v => ((z.restrictE e Wt' h hc).mem_resTw h' v).trans (z.mem_resTw (h'.trans h) v).symm, funext fun v => ?_⟩
  by_cases hv : (plB X).symm v ∈ Wt''
  · apply inclU_injective (usedOf_mono I T (h'.trans h))
    have h1 := (z.restrictE e Wt' h hc).inclU_resMu h' hv
    have h2 := z.inclU_resMu h (h' hv)
    rw [z.inclU_resMu (h'.trans h) hv, ← h2]
    exact congrArg (inclU I (usedOf_mono I T h)) h1
  · exact ((z.restrictE e Wt' h hc).resMu_off h' hv).trans (z.resMu_off (h'.trans h) hv).symm

theorem pair (e : z.R.toRealDat.ExAt) {w} (hw : w ∈ Wt) :
    ∃ y : Dat X I hX T {w, X.B.places.conj w}, plB X w ∈ y.R.twPl ∧ y.R.twPl.card ≤ 2 ∧ y.core = z.core := by
  have cc : X.B.places.conj (X.B.places.conj w) = w :=
    (plB X).injective (by rw [plB_conj, plB_conj, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl])
  have h : ({w, X.B.places.conj w} : Set _) ⊆ Wt := by
    rintro _ (rfl | rfl)
    · exact hw
    · exact z.conjStable _ hw
  have hc : ConjStable X {w, X.B.places.conj w} := by
    rintro _ (rfl | rfl)
    · exact Or.inr rfl
    · exact Or.inl cc
  refine ⟨z.restrictE e _ h hc, (Dat.plB_mem_twPl _ w).2 (Or.inl rfl), ?_, rfl⟩
  classical
  refine le_trans (Finset.card_le_card (t := {plB X w, plB X (X.B.places.conj w)}) fun v hv => ?_) Finset.card_le_two
  rcases (Dat.mem_twPl _ v).1 hv with h1 | h1
  · simp [← h1]
  · have h2 : (plB X).symm v = X.B.places.conj w := h1
    simp [← h2]

open Classical in

theorem subset_nonzero_places_indicator (j : Fin X.toD7.R.m) : Wt ⊆ z.W1 fun v _ => if v ∈ z.R.twPl then 1 else 0 := fun w hw =>
  (z.mem_nonzero_index_places_iff_at_place_or_conjugate _ w).2 ⟨j, Or.inl (Or.inr (Or.inr (by simp [(z.plB_mem_twPl w).2 hw])))⟩

theorem restrictNonzero_idempotent (F0) (e : z.R.toRealDat.ExAt) (h : z.W1 F0 ⊆ Wt) :
    ((z.restrictNonzeroOfExists F0 e h).restrictNonzeroOfExists F0 (z.restrictNonzeroOfExists_exists_lifts F0 e h) (z.restrictNonzeroOfExists_nonzero_places F0 e h).le).W1 F0 = z.W1 F0 :=
  (Dat.restrictNonzeroOfExists_nonzero_places _ F0 _ _).trans (z.restrictNonzeroOfExists_nonzero_places F0 e h)

set_option maxHeartbeats 400000 in

theorem realData_restrict_id {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {μ : T0}
    (R : RealDat3 D (A3.comap id (id μ)) Ks) : Res.dat3 id μ R R.mu R.twPl = R := rfl

set_option maxHeartbeats 400000 in

theorem resR_self : z.resR subset_rfl = z.R := by
  have h0 := realData_restrict_id (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (Ks := z.core.Q.c.F) (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt))) z.R
  have h1 := congrArg₂ (Res.dat3 (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (Ks := z.core.Q.c.F) id (mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt))) z.R) (resMu_self z) (resTw_self z)
  have h2 := h1.trans h0
  exact (h2)

theorem updS_kapNew {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {S R : RealDat3 D A3 Ks} (e : S = R) (h : R.scal_kap) : S.updS (Res.kapNew S) S.lam3 = R := by
  subst e
  rw [Res.kapNew_of_scal S h]
  rfl

set_option maxHeartbeats 400000 in

theorem resRE_self : z.resRE subset_rfl = z.R := updS_kapNew (resR_self z) z.pins.char.scal.kap

end GlobalTheory.Mem.R3.ResTest

end
