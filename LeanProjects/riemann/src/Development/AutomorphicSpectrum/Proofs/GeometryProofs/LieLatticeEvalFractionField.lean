import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapFromSpecStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

section Rings

variable {S : Scheme.{0}} {A B D : Type} [CommRing A] [CommRing B] [CommRing D]

theorem dualMap_comp (f : A →+* B) (g : B →+* D) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMap]

theorem spec_dualMap_comp (f : A →+* B) (g : B →+* D) :
    Spec.map (CommRingCat.ofHom (dualMap (g.comp f))) =
      Spec.map (CommRingCat.ofHom (dualMap g)) ≫ Spec.map (CommRingCat.ofHom (dualMap f)) := by
  rw [dualMap_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem isTanAt_epsHom {G : Over S} [GrpObj G] (φ : A →+* B) (x : Spec (CommRingCat.of A) ⟶ S)
    (x' : Spec (CommRingCat.of B) ⟶ S) (h : Spec.map (CommRingCat.ofHom φ) ≫ x = x') (v : epsAt x ⟶ G)
    (hv : IsTanAt G x v) : IsTanAt G x' (LieCarrier.epsHom φ x x' h ≫ v) := by
  rw [LieEx.isTanAt_iff] at hv ⊢
  have key : (LieEx.zsec x' : _ ⟶ LieEx.ob x' B) ≫ LieCarrier.epsHom φ x x' h =
      (Over.homMk (Spec.map (CommRingCat.ofHom φ)) h : Over.mk x' ⟶ Over.mk x) ≫ LieEx.zsec x := by
    ext1
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun a => ?_
    simp [dualMap]
  rw [← Category.assoc, key, Category.assoc, hv, MonObj.comp_one]

theorem stalk_hom_ext {X : Scheme.{0}} (c : X) (a b : X.presheaf.stalk c →+* B)
    (h : Spec.map (CommRingCat.ofHom a) ≫ X.fromSpecStalk c = Spec.map (CommRingCat.ofHom b) ≫ X.fromSpecStalk c) :
    a = b := by
  have h1 := (cancel_mono (X.fromSpecStalk c)).1 h
  have h2 := Spec.map_injective h1
  exact congrArg CommRingCat.Hom.hom h2

end Rings

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E] {R : Type} [CommRing R] [IsLocalRing R] {C : Type} [Field C] [Algebra R C]

theorem centre_specializes (z : Spec (CommRingCat.of R) ⟶ X) :
    centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) ⤳ centre z := by
  have h : (Spec.map (CommRingCat.ofHom (algebraMap R C))) (IsLocalRing.closedPoint C) ⤳
      IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint _
  exact h.map z.continuous

theorem valAt_base (M : LieModel G ξ E) (z : Spec (CommRingCat.of R) ⟶ X) {e : E} (hc : genPt ξ ⤳ centre z)
    (hc' : genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z))
    (v : epsAt (R := X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z)) ⟶ G)
    (hv : M.Extends ⟨centre z, hc⟩ e v) (t : epsAt (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) ⟶ G)
    (u : epsAt z ⟶ G) (ht : t.left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R C))) ≫ u.left)
    (hu : u.left = Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) ≫ v.left) :
    M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) e t := by
  have hsp := centre_specializes (C := C) z
  have F1 : Spec.map (CommRingCat.ofHom (X.presheaf.stalkSpecializes hsp).hom) ≫ X.fromSpecStalk (centre z) =
      X.fromSpecStalk (centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z)) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have gen_eq : (genMap ξ ⟨_, hc'⟩).comp (X.presheaf.stalkSpecializes hsp).hom = genMap ξ ⟨_, hc⟩ := by
    apply stalk_hom_ext
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, F1]
    exact (LieCarrier.genMap_fromSpecStalk ⟨_, hc'⟩).trans (LieCarrier.genMap_fromSpecStalk ⟨_, hc⟩).symm
  have s_eq : (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z)).hom.comp
      (X.presheaf.stalkSpecializes hsp).hom = (algebraMap R C).comp (Scheme.stalkClosedPointTo z).hom := by
    apply stalk_hom_ext
    have L : Spec.map (X.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo
        (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z)) ≫ X.fromSpecStalk (centre z) =
        Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z :=
      (congrArg (· ≫ X.fromSpecStalk (centre z)) (Spec.map_comp _ _)).trans ((Category.assoc _ _ _).trans
        ((congrArg (Spec.map (Scheme.stalkClosedPointTo _) ≫ ·)
          (Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp)).trans
            (Scheme.Spec_stalkClosedPointTo_fromSpecStalk _)))
    have Rt : Spec.map (Scheme.stalkClosedPointTo z ≫ CommRingCat.ofHom (algebraMap R C)) ≫
        X.fromSpecStalk (centre z) = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z :=
      (congrArg (· ≫ X.fromSpecStalk (centre z)) (Spec.map_comp _ _)).trans ((Category.assoc _ _ _).trans
        (congrArg (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ ·)
          (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z)))
    exact L.trans Rt.symm
  refine ⟨hc', LieCarrier.epsHom (X.presheaf.stalkSpecializes hsp).hom _ _ F1 ≫ v,
    ⟨isTanAt_epsHom _ _ _ _ _ hv.1, ?_⟩, ?_⟩
  · change (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap (genMap ξ ⟨_, hc'⟩))) ≫
      Spec.map (CommRingCat.ofHom (dualMap (X.presheaf.stalkSpecializes hsp).hom)) ≫ v.left
    have e := spec_dualMap_comp (X.presheaf.stalkSpecializes hsp).hom (genMap ξ ⟨_, hc'⟩)
    rw [gen_eq] at e
    exact hv.2.trans ((congrArg (· ≫ v.left) e).trans (Category.assoc _ _ _))
  · change t.left = Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo _).hom)) ≫
      Spec.map (CommRingCat.ofHom (dualMap (X.presheaf.stalkSpecializes hsp).hom)) ≫ v.left
    have e1 := spec_dualMap_comp (Scheme.stalkClosedPointTo z).hom (algebraMap R C)
    have e2 := spec_dualMap_comp (X.presheaf.stalkSpecializes hsp).hom
      (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z)).hom
    have e3 := (congrArg (fun f : X.presheaf.stalk (centre z) →+* C => Spec.map (CommRingCat.ofHom (dualMap f)))
      s_eq).symm.trans e2
    exact ht.trans ((congrArg (_ ≫ ·) hu).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ v.left) (e1.symm.trans e3)).trans (Category.assoc _ _ _))))

end GlobalTheory.CompanionTheory.Ar.LieFib

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem lieLat_fibAt_iff : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (R : Type) [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (C : Type) [Field C] [Algebra R C] (EC : Type) [AddCommGroup EC] [Module C EC] [Module R EC] [IsScalarTower R C EC] (MC : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) EC), IsCptGen ξ → Smooth G.hom → genPt ξ ⤳ centre z → genPt ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) → ∀ w : EC, w ∈ M.fibAt M.lat z MC ↔ ∃ v : epsAt z ⟶ G, IsTanAt G z v ∧ (MC.pt w).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R C))) ≫ v.left := by
  intro X G _ _ Ω _ ξ E _ _ M R _ _ z C _ _ EC _ _ _ _ MC hξ hG h h' w
  obtain ⟨ER, _, _, ⟨MR⟩⟩ := lieModel_exists X G R z
  obtain ⟨ev, hev, -, hspan⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ E M R z h ER MR hξ hG
  obtain ⟨evC, hevC, -, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ E M C _ h' EC MC hξ hG
  have hj : ∀ u : ER, ∃ w, MC.pt w = LieCarrier.epsHom (algebraMap R C) z _ rfl ≫ MR.pt u := fun u =>
    MC.onto _ (LieFib.isTanAt_epsHom _ _ _ _ _ (MR.tan u))
  choose j hj using hj
  have hjl : ∀ u, (MC.pt (j u)).left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap R C))) ≫ (MR.pt u).left := fun u =>
    congrArg CommaMorphism.left (hj u)
  have hadd : ∀ u u', j (u + u') = j u + j u' := fun u u' => MC.inj (by
    rw [hj, MC.add, hj, hj, MR.add, MonObj.comp_mul])
  have hsmul : ∀ (r : R) u, j (r • u) = r • j u := fun r u => MC.inj (Over.OverMorphism.ext (by
    rw [← algebraMap_smul C r (j u), MC.smul, hjl, hjl, MR.smul]
    have e : Spec.map (CommRingCat.ofHom (epsMul (algebraMap R C r))) ≫
        Spec.map (CommRingCat.ofHom (dualMap (algebraMap R C))) =
        Spec.map (CommRingCat.ofHom (dualMap (algebraMap R C))) ≫ Spec.map (CommRingCat.ofHom (epsMul r)) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
        LieCarrier.dualMap_epsMul]
    rw [← Category.assoc, ← e, Category.assoc]))
  let jL : ER →ₗ[R] EC := { toFun := j, map_add' := hadd, map_smul' := hsmul }
  have hgen : ∀ (e : E) (he : e ∈ M.lat ⟨centre z, h⟩),
      M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ z) e (MC.pt (j (ev ⟨e, he⟩))) := by
    intro e he
    obtain ⟨h2, v, hv, hu⟩ := (hev e _).2 ⟨he, rfl⟩
    exact LieFib.valAt_base M z h h' v hv _ _ (hjl _) hu
  constructor
  · intro hw
    have hle : M.fibAt M.lat z MC ≤ LinearMap.range jL := by
      refine Submodule.span_le.2 ?_
      rintro w' ⟨h2, e, he, hval⟩
      obtain ⟨he', hw'⟩ := (hevC e _).1 hval
      obtain ⟨he'', hw''⟩ := (hevC e _).1 (hgen e he)
      exact ⟨ev ⟨e, he⟩, hw''.symm.trans hw'⟩
    obtain ⟨u, rfl⟩ := hle hw
    exact ⟨MR.pt u, MR.tan u, hjl u⟩
  · rintro ⟨v, hv, hw⟩
    obtain ⟨u, rfl⟩ := MR.onto v hv
    have hwu : w = j u := MC.inj (Over.OverMorphism.ext (hw.trans (hjl u).symm))
    subst hwu
    have hu : u ∈ Submodule.span R (Set.range ev) := hspan ▸ Submodule.mem_top
    have hle : (Submodule.span R (Set.range ev)).map jL ≤ M.fibAt M.lat z MC := by
      rw [Submodule.map_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨⟨e, he⟩, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨h, e, he, hgen e he⟩
    exact hle (Submodule.mem_map_of_mem hu)

end GlobalTheory.CompanionTheory.Ar
