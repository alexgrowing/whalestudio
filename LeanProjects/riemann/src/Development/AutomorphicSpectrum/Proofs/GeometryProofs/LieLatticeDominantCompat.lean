import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapFromSpecStalk
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeMapStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOverLocalRingStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LiePull

section BC

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem bc {G : Over S} [GrpObj G] (hs : Smooth G.hom) (f : R →+* R') (x : Sp R ⟶ S) (y : Sp R' ⟶ S)
    (hy : Spec.map (CommRingCat.ofHom f) ≫ x = y) {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E']
    [Module R' E'] (M : LieModel G x E) (M' : LieModel G y E') {n : ℕ} (b : Module.Basis (Fin n) R E)
    (b' : Fin n → E')
    (hb : ∀ k, (M'.pt (b' k)).left = Spec.map (CommRingCat.ofHom (dualMap f)) ≫ (M.pt (b k)).left) :
    LinearIndependent R' b' ∧ Submodule.span R' (Set.range b') = ⊤ := by
  subst hy
  letI := f.toAlgebra
  obtain ⟨j, hj, -, hsp⟩ := GlobalTheory.T.lie_model_base_change_map S G R R' x E E' M M'
  have e : (fun k => j (b k)) = b' :=
    funext fun k => M'.inj (Over.OverMorphism.ext ((hj _).trans (hb k).symm))
  have := hsp hs n b
  rwa [e] at this

theorem dualMap_comp {R'' : Type} [CommRing R''] (a : R →+* R') (b : R' →+* R'') :
    (dualMap b).comp (dualMap a) = dualMap (b.comp a) := by
  refine RingHom.ext fun t => ?_
  ext <;> simp [dualMap]

theorem tan_pull {G : Over S} [GrpObj G] (φ : R →+* R') (x : Sp R ⟶ S) (x' : Sp R' ⟶ S)
    (h : Spec.map (CommRingCat.ofHom φ) ≫ x = x') (v : epsAt x ⟶ G) (hv : IsTanAt G x v) :
    IsTanAt G x' (LieCarrier.epsHom φ x x' h ≫ v) := by
  let u : Over.mk x' ⟶ Over.mk x := Over.homMk (Spec.map (CommRingCat.ofHom φ)) h
  have e : (LieEx.zsec x' : _ ⟶ LieEx.ob x' R') ≫ LieCarrier.epsHom φ x x' h = u ≫ LieEx.zsec x := by
    apply Over.OverMorphism.ext
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun a => ?_
    simp [dualMap]
  refine (LieEx.isTanAt_iff x' G _).2 ?_
  rw [← Category.assoc, e, Category.assoc, (LieEx.isTanAt_iff x G _).1 hv, MonObj.comp_one]

end BC

section Ext

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω]
  {ξ : Sp Ω ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E] {A : Type} [CommRing A]

def Ext (g : A →+* Ω) (x : Sp A ⟶ X) (M : LieModel G ξ E) (e : E) (v : epsAt x ⟶ G) : Prop :=
  IsTanAt G x v ∧ (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ v.left

variable {g : A →+* Ω} {x : Sp A ⟶ X} {M : LieModel G ξ E}

theorem Ext.unique (hg : Function.Injective g) {e : E} {v v' : epsAt x ⟶ G} (hv : Ext g x M e v)
    (hv' : Ext g x M e v') : v = v' :=
  LieCarrier.tan_ext g hg _ v v' hv.1 hv'.1 (hv.2.symm.trans hv'.2)

theorem Ext.mul (hx : Spec.map (CommRingCat.ofHom g) ≫ x = ξ) {e e' : E} {v v' : epsAt x ⟶ G}
    (hv : Ext g x M e v) (hv' : Ext g x M e' v') : Ext g x M (e + e') (v * v') := by
  refine ⟨(LieEx.isTanAt_iff _ G _).2 ?_, ?_⟩
  · rw [MonObj.comp_mul, (LieEx.isTanAt_iff _ G _).1 hv.1, (LieEx.isTanAt_iff _ G _).1 hv'.1, _root_.mul_one]
  · have e1 : M.pt e = LieCarrier.epsHom g x ξ hx ≫ v := Over.OverMorphism.ext hv.2
    have e2 : M.pt e' = LieCarrier.epsHom g x ξ hx ≫ v' := Over.OverMorphism.ext hv'.2
    have : M.pt (e + e') = LieCarrier.epsHom g x ξ hx ≫ (v * v') := by
      rw [M.add, MonObj.comp_mul, e1, e2]
    exact congrArg CommaMorphism.left this

theorem Ext.smul {e : E} {v : epsAt x ⟶ G} (hv : Ext g x M e v) (c : A) :
    Ext g x M (g c • e) (LieEx.hom x (c • (LinearMap.id : A →ₗ[A] A)) ≫ v) := by
  refine ⟨(LieEx.isTanAt_iff _ G _).2 ?_, ?_⟩
  · rw [← Category.assoc, LieEx.zsec_hom]
    exact (LieEx.isTanAt_iff _ G _).1 hv.1
  · change (M.pt (g c • e)).left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫
      Spec.map (CommRingCat.ofHom (epsMul c)) ≫ v.left
    rw [M.smul, hv.2]
    have : Spec.map (CommRingCat.ofHom (epsMul (g c))) ≫ Spec.map (CommRingCat.ofHom (dualMap g)) =
        Spec.map (CommRingCat.ofHom (dualMap g)) ≫ Spec.map (CommRingCat.ofHom (epsMul c)) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
        LieCarrier.dualMap_epsMul]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ v.left) this).trans (Category.assoc _ _ _))

theorem Ext.zero (hx : Spec.map (CommRingCat.ofHom g) ≫ x = ξ) : Ext g x M 0 (1 : epsAt x ⟶ G) := by
  refine ⟨(LieEx.isTanAt_iff x G _).2 (MonObj.comp_one _), ?_⟩
  have h0 : M.pt 0 = 1 := by
    have := M.add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have : M.pt 0 = LieCarrier.epsHom g x ξ hx ≫ (1 : epsAt x ⟶ G) := by rw [h0, MonObj.comp_one]
  exact congrArg CommaMorphism.left this

def extLat (hx : Spec.map (CommRingCat.ofHom g) ≫ x = ξ) (M : LieModel G ξ E) : AddSubgroup E where
  carrier := {e | ∃ v, Ext g x M e v}
  add_mem' := fun ⟨v, hv⟩ ⟨v', hv'⟩ => ⟨_, hv.mul hx hv'⟩
  zero_mem' := ⟨_, Ext.zero hx⟩
  neg_mem' := fun {e} ⟨v, hv⟩ => ⟨_, by simpa using hv.smul (-1)⟩

def ExtE (hx : Spec.map (CommRingCat.ofHom g) ≫ x = ξ) (M : LieModel G ξ E) : Type := ↥(extLat hx M)

variable {hx : Spec.map (CommRingCat.ofHom g) ≫ x = ξ}

instance : AddCommGroup (ExtE hx M) := inferInstanceAs (AddCommGroup ↥(extLat hx M))

def val : ExtE hx M →+ E := (extLat hx M).subtype

theorem val_inj : Function.Injective (val : ExtE hx M →+ E) := Subtype.val_injective

theorem smul_mem (c : A) (y : ExtE hx M) : g c • val y ∈ extLat hx M :=
  let ⟨_, hv⟩ := y.2
  ⟨_, hv.smul c⟩

instance : SMul A (ExtE hx M) := ⟨fun c y => ⟨g c • val y, smul_mem c y⟩⟩

theorem val_smul (c : A) (y : ExtE hx M) : val (c • y) = g c • val y := rfl

instance : Module A (ExtE hx M) where
  one_smul y := val_inj (by rw [val_smul, map_one, one_smul])
  mul_smul a b y := val_inj (by simp only [val_smul, map_mul, mul_smul])
  smul_zero a := val_inj (by simp [val_smul])
  smul_add a y z := val_inj (by simp [val_smul, smul_add])
  add_smul a b y := val_inj (by simp [val_smul, add_smul])
  zero_smul y := val_inj (by simp [val_smul])

theorem val_spec (y : ExtE hx M) : ∃ v, Ext g x M (val y) v := y.2

def vec (y : ExtE hx M) : epsAt x ⟶ G := (val_spec y).choose

theorem vec_spec (y : ExtE hx M) : Ext g x M (val y) (vec y) := (val_spec y).choose_spec

def extModel (hg : Function.Injective g) (hx : Spec.map (CommRingCat.ofHom g) ≫ x = ξ) (M : LieModel G ξ E) :
    LieModel G x (ExtE hx M) where
  pt y := vec y
  tan y := (vec_spec y).1
  inj a b e := val_inj (M.inj (Over.OverMorphism.ext ((vec_spec a).2.trans (by
    rw [show vec a = vec b from e]
    exact (vec_spec b).2.symm))))
  onto v t := by
    obtain ⟨e, he⟩ := M.onto _ (tan_pull g x ξ hx v t)
    have ex : Ext g x M e v := ⟨t, congrArg CommaMorphism.left he⟩
    exact ⟨⟨e, v, ex⟩, (vec_spec (hx := hx) (M := M) ⟨e, v, ex⟩).unique hg ex⟩
  add a b := (vec_spec (a + b)).unique hg ((vec_spec a).mul hx (vec_spec b))
  smul c y := congrArg CommaMorphism.left ((vec_spec (c • y)).unique hg ((vec_spec y).smul c))

end Ext

section Pull

variable {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω' ⟶ X'} {f : X' ⟶ X}
  {i : Ω →+* Ω'} {G : Over X} {G' : Over X'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}
  {V V' : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']
  {M : LieModel G ξ V} {M' : LieModel G' ξ' V'} {j : V →+ V'}
  {A A' : Type} [CommRing A] [CommRing A'] {g : A →+* Ω} {g' : A' →+* Ω'} {ρ : A →+* A'}
  {x : Sp A ⟶ X} {x' : Sp A' ⟶ X'}

theorem ext_up (hG : IsGrpPullback G' G f φ)
    (hj : ∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left)
    (hρ : Spec.map (CommRingCat.ofHom ρ) ≫ x = x' ≫ f) (hρ' : g'.comp ρ = i.comp g)
    (hx' : Spec.map (CommRingCat.ofHom g') ≫ x' = ξ') {e : V} {v : epsAt x ⟶ G} (hv : Ext g x M e v) :
    ∃ v' : epsAt x' ⟶ G', Ext g' x' M' (j e) v' ∧
      v'.left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap ρ)) ≫ v.left := by
  have tw := tan_pull ρ x (x' ≫ f) hρ v hv.1
  have h1 := LieMove.liftEps_left hG (LieCarrier.epsHom ρ x (x' ≫ f) hρ ≫ v)
  have h1' : (LieMove.liftEps hG (LieCarrier.epsHom ρ x (x' ≫ f) hρ ≫ v)).left ≫ φ =
      Spec.map (CommRingCat.ofHom (dualMap ρ)) ≫ v.left := h1
  refine ⟨LieMove.liftEps hG (LieCarrier.epsHom ρ x (x' ≫ f) hρ ≫ v),
    ⟨(LieMove.tan_iff hG _).2 (by rw [LieMove.push_lift]; exact tw), ?_⟩, h1'⟩
  have key : Spec.map (CommRingCat.ofHom (dualMap i)) ≫ Spec.map (CommRingCat.ofHom (dualMap g)) =
      Spec.map (CommRingCat.ofHom (dualMap g')) ≫ Spec.map (CommRingCat.ofHom (dualMap ρ)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, dualMap_comp,
      dualMap_comp, hρ']
  refine hG.1.hom_ext ?_ ?_
  · rw [hj, hv.2, Category.assoc, h1', ← Category.assoc, key, Category.assoc]
  · have w₁ := Over.w (M'.pt (j e))
    have w₂ := Over.w (LieCarrier.epsHom g' x' ξ' hx' ≫ LieMove.liftEps hG (LieCarrier.epsHom ρ x (x' ≫ f) hρ ≫ v))
    exact w₁.trans w₂.symm

theorem core [IsLocalRing A] (hs : Smooth G.hom) (hG : IsGrpPullback G' G f φ)
    (hj : ∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left)
    (hg : Function.Injective g) (hg' : Function.Injective g')
    (hρ : Spec.map (CommRingCat.ofHom ρ) ≫ x = x' ≫ f) (hρ' : g'.comp ρ = i.comp g)
    (hx : Spec.map (CommRingCat.ofHom g) ≫ x = ξ) (hx' : Spec.map (CommRingCat.ofHom g') ≫ x' = ξ')
    {e' : V'} {v' : epsAt x' ⟶ G'} (hv' : Ext g' x' M' e' v') :
    ∃ (n : ℕ) (b : Fin n → V) (c : Fin n → A'), (∀ k, ∃ v, Ext g x M (b k) v) ∧
      e' = ∑ k, g' (c k) • j (b k) := by
  obtain ⟨n, ⟨b⟩⟩ := GlobalTheory.T.lie_model_free_over_local_ring X G hs A x (ExtE hx M) (extModel hg hx M)
  have up : ∀ k, ∃ u : epsAt x' ⟶ G', Ext g' x' M' (j (val (b k))) u ∧
      u.left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap ρ)) ≫ (vec (b k)).left :=
    fun k => ext_up hG hj hρ hρ' hx' (vec_spec (b k))
  choose u hu huφ using up
  let b' : Fin n → ExtE hx' M' := fun k => ⟨j (val (b k)), u k, hu k⟩
  obtain ⟨-, hsp⟩ := bc hs ρ x (x' ≫ f) hρ (extModel hg hx M) (LieMove.pushModel hG (extModel hg' hx' M')) b b'
    (fun k => by
      have e₁ : vec (b' k) = u k := (vec_spec (b' k)).unique hg' (hu k)
      show (vec (b' k)).left ≫ φ = _
      rw [e₁]
      exact huφ k)
  obtain ⟨y, rfl⟩ : ∃ y : ExtE hx' M', val y = e' := ⟨⟨e', v', hv'⟩, rfl⟩
  have hy : y ∈ Submodule.span A' (Set.range b') := by rw [hsp]; trivial
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A').1 hy
  exact ⟨n, fun k => val (b k), c, fun k => val_spec (b k), map_sum val _ _⟩

theorem semilin (hG : IsGrpPullback G' G f φ)
    (hj : ∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left) (a : Ω) (e : V) :
    j (a • e) = i a • j e := by
  refine M'.inj (Over.OverMorphism.ext (hG.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)))
  have key : Spec.map (CommRingCat.ofHom (epsMul (i a))) ≫ Spec.map (CommRingCat.ofHom (dualMap i)) =
      Spec.map (CommRingCat.ofHom (dualMap i)) ≫ Spec.map (CommRingCat.ofHom (epsMul a)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      LieCarrier.dualMap_epsMul]
  rw [hj, M.smul, M'.smul, Category.assoc, hj, ← Category.assoc (Spec.map (CommRingCat.ofHom (epsMul (i a)))), key,
    Category.assoc]

theorem indep_of_bases {F : Type} [AddCommGroup F] [Module Ω' F] {m : ℕ} (b₁ : Module.Basis (Fin m) Ω V) (j : V →+ F)
    (hall : ∀ (m : ℕ) (B : Module.Basis (Fin m) Ω V), LinearIndependent Ω' fun k => j (B k))
    {n : ℕ} (b : Fin n → V) (hb : LinearIndependent Ω b) : LinearIndependent Ω' fun k => j (b k) := by
  have hs : LinearIndepOn Ω id (Set.range b) := hb.linearIndepOn_id
  let B := Module.Basis.extend hs
  haveI : Module.Finite Ω V := Module.Finite.of_basis b₁
  haveI := Module.Finite.finite_basis B
  let eq := Finite.equivFin (hs.extend (Set.subset_univ _))
  have h := (hall _ (B.reindex eq)).comp
    (fun k => eq ⟨b k, hs.subset_extend _ (Set.mem_range_self k)⟩)
    (fun a c hac => hb.injective (congrArg Subtype.val (eq.injective hac)))
  convert h using 2 with k
  simp only [Function.comp, B, Module.Basis.reindex_apply, Equiv.symm_apply_apply, Module.Basis.extend_apply_self]

end Pull

theorem main : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X)
    (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    (φ : G'.left ⟶ G.left) (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V']
    (M : LieModel G ξ V) (M' : LieModel G' ξ' V') (j : V →+ V'), IsCptGen ξ → IsCptGen ξ' →
    GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → Smooth G.hom →
    (∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left) →
    IsExtOver i j ∧ Submodule.span Ω' (Set.range j) = ⊤ ∧ M'.lat = M.lat.pull ξ' f j := by
  intro X X' Ω Ω' _ _ ξ ξ' f i G G' _ _ _ _ φ V V' _ _ _ _ M M' j hξ hξ' hd hG hs hj
  have hbc : ∀ (m : ℕ) (B : Module.Basis (Fin m) Ω V), LinearIndependent Ω' (fun k => j (B k)) ∧
      Submodule.span Ω' (Set.range fun k => j (B k)) = ⊤ := fun m B =>
    bc hs i ξ (ξ' ≫ f) (Eq.symm hd) M (LieMove.pushModel hG M') B (fun k => j (B k)) (fun k => hj _)
  obtain ⟨m, ⟨b₁⟩⟩ := GlobalTheory.T.lie_model_free_over_local_ring X G hs Ω ξ V M
  refine ⟨⟨semilin hG hj, fun n b hb => indep_of_bases b₁ j (fun m B => (hbc m B).1) b hb⟩, ?_, ?_⟩
  · refine top_le_iff.1 ((hbc m b₁).2.symm.le.trans (Submodule.span_mono ?_))
    rintro _ ⟨k, rfl⟩
    exact ⟨_, rfl⟩
  · funext p'
    have hp : genPt ξ ⤳ f p'.1 := RegAtDom.map_genPt hd ▸ p'.2.map f.continuous
    have hx := LieCarrier.genMap_fromSpecStalk (ξ := ξ) ⟨f p'.1, hp⟩
    have hx' := LieCarrier.genMap_fromSpecStalk (ξ := ξ') p'
    have hρ : Spec.map (CommRingCat.ofHom (f.stalkMap p'.1).hom) ≫ X.fromSpecStalk (f p'.1) =
        X'.fromSpecStalk p'.1 ≫ f := Scheme.SpecMap_stalkMap_fromSpecStalk f
    have hρ' : (genMap ξ' p').comp (f.stalkMap p'.1).hom = i.comp (genMap ξ ⟨f p'.1, hp⟩) :=
      RingHom.ext (RegAtDom.genMap_stalkMap hd p'.1 p'.2 hp)
    have car := fun e => (lieLat_carrier X G Ω ξ V M ⟨f p'.1, hp⟩).1 e
    have car' := fun e => (lieLat_carrier X' G' Ω' ξ' V' M' p').1 e
    apply le_antisymm
    · intro e' he'
      obtain ⟨v', hv'⟩ := (car' e').1 he'
      obtain ⟨n, b, c, hb, rfl⟩ := core (A := X.presheaf.stalk (f p'.1)) (A' := X'.presheaf.stalk p'.1)
        (g := genMap ξ ⟨f p'.1, hp⟩) (g' := genMap ξ' p') (ρ := (f.stalkMap p'.1).hom) (x := X.fromSpecStalk (f p'.1))
        (x' := X'.fromSpecStalk p'.1) (M := M) (M' := M') (j := j) hs hG hj (hξ.inj _) (hξ'.inj p') hρ hρ' hx hx' hv'
      refine Submodule.sum_mem _ fun k _ => ?_
      have h₁ : j (b k) ∈ M.lat.pull ξ' f j p' :=
        Submodule.subset_span ⟨hp, b k, (car _).2 (hb k), rfl⟩
      exact Submodule.smul_mem _ (⟨genMap ξ' p' (c k), c k, rfl⟩ : regAt ξ' p') h₁
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨h, e, he, rfl⟩
      obtain ⟨v, hv⟩ := (car e).1 he
      obtain ⟨v', hv', -⟩ := ext_up (A := X.presheaf.stalk (f p'.1)) (A' := X'.presheaf.stalk p'.1)
        (g := genMap ξ ⟨f p'.1, hp⟩) (g' := genMap ξ' p') (ρ := (f.stalkMap p'.1).hom) (x := X.fromSpecStalk (f p'.1))
        (x' := X'.fromSpecStalk p'.1) (M := M) (M' := M') (j := j) hG hj hρ hρ' hx' hv
      exact (car' _).2 ⟨v', hv'⟩

end GlobalTheory.CompanionTheory.Ar.LiePull
