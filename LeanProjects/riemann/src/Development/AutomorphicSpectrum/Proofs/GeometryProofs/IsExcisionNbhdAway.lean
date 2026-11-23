import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InjectiveOfIsCptGen
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StdSmoothMvPolynomial

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace LieTangent

section Dual

variable {R R' : Type} [CommRing R] [CommRing R']

@[simp] theorem dualMap_fst (φ : R →+* R') (a : DualNumber R) : (dualMap φ a).fst = φ a.fst := by
  simp [dualMap]

@[simp] theorem dualMap_snd (φ : R →+* R') (a : DualNumber R) : (dualMap φ a).snd = φ a.snd := by
  simp [dualMap]

@[simp] theorem epsMul_fst (c : R) (a : DualNumber R) : (epsMul c a).fst = a.fst := by
  simp [epsMul]

@[simp] theorem epsMul_snd (c : R) (a : DualNumber R) : (epsMul c a).snd = c * a.snd := by
  simp [epsMul]

theorem dualMap_injective {φ : R →+* R'} (h : Function.Injective φ) : Function.Injective (dualMap φ) := by
  intro a b e
  have e1 := congrArg TrivSqZeroExt.fst e
  have e2 := congrArg TrivSqZeroExt.snd e
  simp only [dualMap_fst, dualMap_snd] at e1 e2
  exact TrivSqZeroExt.ext (h e1) (h e2)

theorem isLocalRing_dual [IsLocalRing R] : IsLocalRing (DualNumber R) :=
  haveI : Nontrivial (DualNumber R) := (TrivSqZeroExt.fstHom R R R).toRingHom.domain_nontrivial
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self a.fst

theorem spec_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom (g.comp f)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spec_dual_alg (φ : R →+* R') :
    Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R' (DualNumber R'))) ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [spec_comp, spec_comp]
  congr 2
  ext a <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem spec_fst_dual (φ : R →+* R') :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R' R' R').toRingHom) ≫
        Spec.map (CommRingCat.ofHom (dualMap φ)) =
      Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  rw [spec_comp, spec_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  exact dualMap_fst φ a

theorem spec_eps_alg (c : R) :
    Spec.map (CommRingCat.ofHom (epsMul c)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) := by
  rw [spec_comp]
  congr 2
  ext a <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem spec_fst_eps (c : R) :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ Spec.map (CommRingCat.ofHom (epsMul c)) =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  rw [spec_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  exact epsMul_fst c a

theorem spec_dual_eps (φ : R →+* R') (c : R) :
    Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ Spec.map (CommRingCat.ofHom (epsMul c)) =
      Spec.map (CommRingCat.ofHom (epsMul (φ c))) ≫ Spec.map (CommRingCat.ofHom (dualMap φ)) := by
  rw [spec_comp, spec_comp]
  congr 2
  refine RingHom.ext fun a => ?_
  ext <;> simp

variable {S : Scheme.{0}} {x : Spec (CommRingCat.of R) ⟶ S} {x' : Spec (CommRingCat.of R') ⟶ S}

def epsBase (φ : R →+* R') (h : Spec.map (CommRingCat.ofHom φ) ≫ x = x') : epsAt x' ⟶ epsAt x :=
  Over.homMk (Spec.map (CommRingCat.ofHom (dualMap φ))) (by
    change _ ≫ _ ≫ x = _ ≫ x'
    rw [← Category.assoc, spec_dual_alg, Category.assoc, h])

def epsScale (x : Spec (CommRingCat.of R) ⟶ S) (c : R) : epsAt x ⟶ epsAt x :=
  Over.homMk (Spec.map (CommRingCat.ofHom (epsMul c))) (by
    change _ ≫ _ ≫ x = _ ≫ x
    rw [← Category.assoc, spec_eps_alg])

def epsZero (x : Spec (CommRingCat.of R) ⟶ S) : Over.mk x ⟶ epsAt x :=
  Over.homMk (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom)) (by
    change _ ≫ _ ≫ x = x
    rw [← Category.assoc, spec_comp]
    have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext a; simp
    rw [this, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp])

variable {G : Over S} [GrpObj G]

theorem isTanAt_iff (v : epsAt x ⟶ G) : IsTanAt G x v ↔ epsZero x ≫ v = 1 :=
  ⟨fun h => Over.OverMorphism.ext h, fun h => by exact congrArg (fun q : Over.mk x ⟶ G => q.left) h⟩

omit [GrpObj G] in
theorem left_eq_iff (φ : R →+* R') (h : Spec.map (CommRingCat.ofHom φ) ≫ x = x') (w : epsAt x' ⟶ G)
    (v : epsAt x ⟶ G) :
    w.left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v.left ↔ w = epsBase φ h ≫ v :=
  ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (fun q => q.left) h⟩

theorem isTanAt_one : IsTanAt G x 1 := (isTanAt_iff _).2 (comp_one _)

theorem isTanAt_mul {v v' : epsAt x ⟶ G} (h : IsTanAt G x v) (h' : IsTanAt G x v') : IsTanAt G x (v * v') := by
  rw [isTanAt_iff] at *
  rw [comp_mul, h, h', _root_.mul_one]

theorem isTanAt_scale (c : R) {v : epsAt x ⟶ G} (h : IsTanAt G x v) : IsTanAt G x (epsScale x c ≫ v) := by
  change _ ≫ Spec.map _ ≫ v.left = _
  rw [← Category.assoc, spec_fst_eps]
  exact h

theorem isTanAt_base (φ : R →+* R') (hφ : Spec.map (CommRingCat.ofHom φ) ≫ x = x') {v : epsAt x ⟶ G}
    (h : IsTanAt G x v) : IsTanAt G x' (epsBase φ hφ ≫ v) := by
  change _ ≫ Spec.map _ ≫ v.left = _
  rw [← Category.assoc, spec_fst_dual, Category.assoc, h]
  exact congrArg (·.left)
    (comp_one (M := G) (Over.homMk (Spec.map (CommRingCat.ofHom φ)) hφ : Over.mk x' ⟶ Over.mk x))

theorem base_scale (φ : R →+* R') (hφ : Spec.map (CommRingCat.ofHom φ) ≫ x = x') (c : R) :
    epsBase φ hφ ≫ epsScale x c = epsScale x' (φ c) ≫ epsBase φ hφ :=
  Over.OverMorphism.ext (spec_dual_eps φ c)

theorem ext_of_injective [IsLocalRing R] {φ : R →+* R'} (hφ : Function.Injective φ) {Y : Scheme.{0}}
    {v v' : Spec (CommRingCat.of R) ⟶ Y} (hc : v (IsLocalRing.closedPoint R) = v' (IsLocalRing.closedPoint R))
    (h : Spec.map (CommRingCat.ofHom φ) ≫ v = Spec.map (CommRingCat.ofHom φ) ≫ v') : v = v' := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hq, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (v (IsLocalRing.closedPoint R))) isOpen_univ
  replace hU : IsAffineOpen U := hU
  have key : ∀ u : Spec (CommRingCat.of R) ⟶ Y, u (IsLocalRing.closedPoint R) ∈ U →
      ∃ a : Γ(Y, U) ⟶ CommRingCat.of R, Spec.map a ≫ hU.fromSpec = u := by
    intro u hu
    have hr : Set.range u ⊆ Set.range hU.fromSpec := by
      rw [hU.range_fromSpec]
      rintro _ ⟨t, rfl⟩
      have := Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of R) u hu
      exact (this.ge (Set.mem_univ t) : t ∈ u ⁻¹ᵁ U)
    exact ⟨Spec.preimage (IsOpenImmersion.lift hU.fromSpec u hr), by
      rw [Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
  obtain ⟨a, rfl⟩ := key v hq
  obtain ⟨a', rfl⟩ := key v' (hc ▸ hq)
  rw [← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at h
  have h2 := Spec.map_injective h
  have : a = a' := by
    ext t
    exact hφ (congrArg (fun g => g.hom t) h2)
  rw [this]

theorem tan_ext [IsLocalRing R] {φ : R →+* R'} (hφ : Function.Injective φ)
    {v v' : epsAt x ⟶ G} (h : IsTanAt G x v) (h' : IsTanAt G x v')
    (e : Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v.left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v'.left) :
    v = v' := by
  have := isLocalRing_dual (R := R)
  have : IsLocalHom (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom).hom :=
    ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
  refine Over.OverMorphism.ext (ext_of_injective (R := DualNumber R) (dualMap_injective hφ) ?_ e)
  have hc := Spec_closedPoint (f := CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom)
  have e1 := congrArg (fun g => g (IsLocalRing.closedPoint R)) (h.trans h'.symm)
  simp only [Scheme.Hom.comp_apply] at e1
  exact hc ▸ e1

end Dual

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem spec_genMap (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    Spec.map (CommRingCat.ofHom (genMap ξ p)) ≫ X.fromSpecStalk p.1 = ξ := by
  change Spec.map (X.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo ξ) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) ξ

theorem spec_centre {R : Type} [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) :
    Spec.map (CommRingCat.ofHom (R := X.presheaf.stalk (centre z)) (Scheme.stalkClosedPointTo z).hom) ≫
      X.fromSpecStalk (centre z) = z :=
  Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of R) z

end LieTangent

open LieTangent

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

namespace LieModel

theorem pt_zero {R : Type} [CommRing R] {x : Spec (CommRingCat.of R) ⟶ X} {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) : M.pt 0 = 1 := by
  have := M.add 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem pt_smul {R : Type} [CommRing R] {x : Spec (CommRingCat.of R) ⟶ X} {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G x E) (c : R) (e : E) : M.pt (c • e) = epsScale x c ≫ M.pt e :=
  Over.OverMorphism.ext (M.smul c e)

variable (M : LieModel G ξ E)

theorem extends_iff (p : Cpt ξ) (e : E)
    (v : epsAt (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ⟶ G) :
    M.Extends p e v ↔ IsTanAt G _ v ∧ M.pt e = epsBase (genMap ξ p) (spec_genMap ξ p) ≫ v :=
  and_congr Iff.rfl (left_eq_iff _ _ _ _)

theorem extends_zero (p : Cpt ξ) : M.Extends p 0 1 :=
  (M.extends_iff _ _ _).2 ⟨isTanAt_one, by rw [pt_zero, comp_one]⟩

variable {M}

theorem Extends.add {p : Cpt ξ} {e e' : E}
    {v v' : epsAt (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ⟶ G}
    (h : M.Extends p e v) (h' : M.Extends p e' v') : M.Extends p (e + e') (v * v') := by
  rw [extends_iff] at *
  exact ⟨isTanAt_mul h.1 h'.1, by rw [M.add, comp_mul, h.2, h'.2]⟩

theorem Extends.smul {p : Cpt ξ} {e : E}
    {v : epsAt (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ⟶ G}
    (h : M.Extends p e v) (s : X.presheaf.stalk p.1) :
    M.Extends p (genMap ξ p s • e) (epsScale (R := X.presheaf.stalk p.1) _ s ≫ v) := by
  rw [extends_iff] at *
  exact ⟨isTanAt_scale s h.1, by rw [M.pt_smul, h.2, ← Category.assoc, ← base_scale, Category.assoc]⟩

theorem mem_lat_iff (M : LieModel G ξ E) (p : Cpt ξ) (e : E) : e ∈ M.lat p ↔ ∃ v, M.Extends p e v := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem e he => exact he
  | zero => exact ⟨_, M.extends_zero p⟩
  | add a b _ _ ha hb => exact ⟨_, ha.choose_spec.add hb.choose_spec⟩
  | smul c a _ ha =>
    obtain ⟨_, s, rfl⟩ := c
    exact ⟨_, ha.choose_spec.smul s⟩

theorem Extends.unique {p : Cpt ξ} (hp : Function.Injective (genMap ξ p)) {e : E}
    {v v' : epsAt (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ⟶ G}
    (h : M.Extends p e v) (h' : M.Extends p e v') : v = v' :=
  tan_ext hp h.1 h'.1 (h.2.symm.trans h'.2)

variable {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}

theorem valAt_iff (M : LieModel G ξ E) (z : Spec (CommRingCat.of R) ⟶ X) (e : E) (w : epsAt z ⟶ G) :
    M.ValAt z e w ↔ ∃ (h : genPt ξ ⤳ centre z)
      (v : epsAt (R := X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z)) ⟶ G),
      M.Extends ⟨centre z, h⟩ e v ∧ w = epsBase _ (spec_centre z) ≫ v :=
  exists_congr fun _ => exists_congr fun _ => and_congr Iff.rfl (left_eq_iff _ _ _ _)

theorem ValAt.unique (hξ : IsCptGen ξ) {e : E} {w w' : epsAt z ⟶ G} (h : M.ValAt z e w) (h' : M.ValAt z e w') :
    w = w' := by
  rw [valAt_iff] at h h'
  obtain ⟨h1, v, hv, rfl⟩ := h
  obtain ⟨_, v', hv', rfl⟩ := h'
  rw [hv.unique (hξ.inj _) hv']

theorem ValAt.isTanAt {e : E} {w : epsAt z ⟶ G} (h : M.ValAt z e w) : IsTanAt G z w := by
  rw [valAt_iff] at h
  obtain ⟨h1, v, hv, rfl⟩ := h
  exact isTanAt_base _ _ hv.1

theorem exists_valAt_iff (M : LieModel G ξ E) (z : Spec (CommRingCat.of R) ⟶ X) (e : E) :
    (∃ w, M.ValAt z e w) ↔ ∃ h : genPt ξ ⤳ centre z, e ∈ M.lat ⟨centre z, h⟩ := by
  constructor
  · rintro ⟨_, h, v, hv, -⟩
    exact ⟨h, (M.mem_lat_iff _ _).2 ⟨v, hv⟩⟩
  · rintro ⟨h, he⟩
    obtain ⟨v, hv⟩ := (M.mem_lat_iff _ _).1 he
    exact ⟨_, (M.valAt_iff _ _ _).2 ⟨h, v, hv, rfl⟩⟩

theorem ValAt.add {e e' : E} {w w' : epsAt z ⟶ G} (h : M.ValAt z e w) (h' : M.ValAt z e' w') :
    M.ValAt z (e + e') (w * w') := by
  rw [valAt_iff] at *
  obtain ⟨h1, v, hv, rfl⟩ := h
  obtain ⟨_, v', hv', rfl⟩ := h'
  exact ⟨h1, v * v', hv.add hv', (comp_mul _ _ _).symm⟩

theorem valAt_zero (M : LieModel G ξ E) (h : genPt ξ ⤳ centre z) : M.ValAt z 0 1 :=
  (M.valAt_iff _ _ _).2 ⟨h, 1, M.extends_zero _, (comp_one _).symm⟩

theorem ValAt.smul {e : E} {w : epsAt z ⟶ G} (h : M.ValAt z e w) (h1 : genPt ξ ⤳ centre z)
    (s : X.presheaf.stalk (centre z)) :
    M.ValAt z (genMap ξ ⟨centre z, h1⟩ s • e) (epsScale z ((Scheme.stalkClosedPointTo z).hom s) ≫ w) := by
  rw [valAt_iff] at *
  obtain ⟨_, v, hv, rfl⟩ := h
  exact ⟨h1, _, hv.smul s, by rw [← Category.assoc, ← base_scale, Category.assoc]⟩

end LieModel

namespace LieTangent

open LieInh

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem specializes_of_injective {p : Cpt ξ} (hp : Function.Injective (genMap ξ p)) {y : X} (hy : y ⤳ p.1) :
    genPt ξ ⤳ y := by
  have hr : y ∈ Set.range (X.fromSpecStalk p.1) := by
    rw [Scheme.range_fromSpecStalk]; exact hy
  obtain ⟨t, rfl⟩ := hr
  have e : genPt ξ = X.fromSpecStalk p.1 (genPt (CptModel.pt (genMap ξ p))) :=
    congrArg (fun g => g (IsLocalRing.closedPoint Ω)) (spec_genMap ξ p).symm
  have h2 : genPt (CptModel.pt (genMap ξ p)) ⤳ t := (PrimeSpectrum.le_iff_specializes _ _).1 (by
    change (genPt (CptModel.pt (genMap ξ p))).asIdeal ≤ _
    rw [CptModel.genPt_asIdeal, (RingHom.injective_iff_ker_eq_bot _).1 hp]
    exact bot_le)
  have h3 := h2.map (X.fromSpecStalk p.1).continuous
  rwa [← e] at h3

theorem genMap_specializes (p : Cpt ξ) {y : X} (hy : genPt ξ ⤳ y) (c : y ⤳ p.1) (s : X.presheaf.stalk p.1) :
    genMap ξ ⟨y, hy⟩ (X.presheaf.stalkSpecializes c s) = genMap ξ p s := by
  have e : X.presheaf.stalkSpecializes c ≫ X.presheaf.stalkSpecializes hy ≫ Scheme.stalkClosedPointTo ξ =
      X.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo ξ := by
    rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  exact congrArg (fun g => g.hom s) e

theorem centre_specializes {R' : Type} [CommRing R'] [IsLocalRing R'] (φ : R →+* R')
    (z : Spec (CommRingCat.of R) ⟶ X) : centre (Spec.map (CommRingCat.ofHom φ) ≫ z) ⤳ centre z :=
  (IsLocalRing.specializes_closedPoint (R := R) _).map z.continuous

theorem stalk_base {R' : Type} [CommRing R'] [IsLocalRing R'] (φ : R →+* R')
    (z : Spec (CommRingCat.of R) ⟶ X) :
    X.presheaf.stalkSpecializes (centre_specializes φ z) ≫
        Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom φ) ≫ z) =
      Scheme.stalkClosedPointTo z ≫ CommRingCat.ofHom φ := by
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecStalk (centre z)), Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact (spec_centre _).trans (congrArg (_ ≫ ·) (spec_centre z)).symm

theorem valAt_base (hξ : IsCptGen ξ) {R' : Type} [CommRing R'] [IsLocalRing R'] (φ : R →+* R')
    {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r : R} (h : Ar.ValAt ξ z a r) :
    Ar.ValAt ξ (Spec.map (CommRingCat.ofHom φ) ≫ z) a (φ r) := by
  obtain ⟨h, s, rfl, rfl⟩ := h
  have h' := specializes_of_injective (hξ.inj ⟨_, h⟩) (centre_specializes φ z)
  refine ⟨h', X.presheaf.stalkSpecializes (centre_specializes φ z) s, ?_, ?_⟩
  · exact genMap_specializes ⟨centre z, h⟩ h' (centre_specializes φ z) s
  · exact congrArg (fun g => g.hom s) (stalk_base φ z)

theorem valAt_unique (hξ : IsCptGen ξ) {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r r' : R}
    (h : Ar.ValAt ξ z a r) (h' : Ar.ValAt ξ z a r') : r = r' := by
  obtain ⟨h1, s, hs, rfl⟩ := h
  obtain ⟨_, s', hs', rfl⟩ := h'
  rw [hξ.inj ⟨_, h1⟩ (hs.trans hs'.symm)]

end LieTangent

end GlobalTheory.CompanionTheory.Ar
