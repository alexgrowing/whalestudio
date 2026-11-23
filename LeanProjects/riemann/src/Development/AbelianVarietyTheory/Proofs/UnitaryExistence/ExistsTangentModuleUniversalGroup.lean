import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

noncomputable section

namespace GlobalTheory.TanMod

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem spec_ext_two {R A : Type} [CommRing R] [CommRing A] (p1 p2 : R →+* A)
    (hs : Function.Surjective p1) (hn : ∀ x, p1 x = 0 → x * x = 0)
    (hk : ∀ x, p1 x = 0 → p2 x = 0 → x = 0) {X : Scheme.{0}} (f g : Sp R ⟶ X)
    (h1 : spMap p1 ≫ f = spMap p1 ≫ g) (h2 : spMap p2 ≫ f = spMap p2 ≫ g) : f = g := by
  have hl1 : equalizer.lift (spMap p1) h1 ≫ equalizer.ι f g = spMap p1 := equalizer.lift_ι _ _
  have hl2 : equalizer.lift (spMap p2) h2 ≫ equalizer.ι f g = spMap p2 := equalizer.lift_ι _ _
  have hrange : Set.range (equalizer.ι f g) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx : (show PrimeSpectrum R from x) ∈ Set.range (PrimeSpectrum.comap p1) := by
      rw [range_comap_of_surjective _ _ hs]
      intro a ha
      have h3 : a * a ∈ (show PrimeSpectrum R from x).asIdeal := by
        rw [hn a ha]; exact Ideal.zero_mem _
      exact ((show PrimeSpectrum R from x).isPrime.mem_or_mem h3).elim id id
    obtain ⟨y, hy⟩ := hx
    refine ⟨equalizer.lift (spMap p1) h1 (show Sp A from y), ?_⟩
    have h4 := congrArg (fun φ : Sp A ⟶ Sp R => φ (show Sp A from y)) hl1
    exact h4.trans hy
  have hc : (equalizer.ι f g).coborderRange = ⊤ := by
    apply TopologicalSpace.Opens.ext
    have h5 : Set.range (equalizer.ι f g) ⊆ coborder (Set.range (equalizer.ι f g)) := subset_coborder
    rw [hrange] at h5
    have h5' : (↑(equalizer.ι f g).coborderRange : Set (Sp R)) = coborder (Set.range (equalizer.ι f g)) := rfl
    rw [h5', hrange]
    exact Set.univ_subset_iff.1 h5
  have hci : IsClosedImmersion (equalizer.ι f g) := by
    have : IsIso (equalizer.ι f g).coborderRange.ι := by rw [hc, ← Scheme.topIso_hom]; infer_instance
    rw [← (equalizer.ι f g).liftCoborder_ι]
    infer_instance
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.mp hci
  have hI : ∀ (p : R →+* A) (l : Sp A ⟶ equalizer f g), l ≫ equalizer.ι f g = spMap p → ∀ x ∈ I, p x = 0 := by
    intro p l hl x hx
    rw [he, ← Category.assoc] at hl
    have h6 : Spec.map (Spec.preimage (l ≫ e.hom)) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
        Spec.map (CommRingCat.ofHom p) := by rw [Spec.map_preimage]; exact hl
    rw [← Spec.map_comp] at h6
    have h7 := Spec.map_injective h6
    have h8 := congrArg (fun φ => φ.hom x) h7
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h8
    rw [← h8, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
  have hbot : I = ⊥ := by
    refine le_bot_iff.mp fun x hx => ?_
    exact hk x (hI p1 _ hl1 x hx) (hI p2 _ hl2 x hx)
  subst hbot
  have hiso : IsIso (equalizer.ι f g) := by
    rw [he]
    have : IsIso (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal (CommRingCat.of R)))) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      exact (RingEquiv.quotientBot R).symm.bijective
    infer_instance
  rw [← cancel_epi (equalizer.ι f g), equalizer.condition]

section Tan

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)

theorem homAt_comp {A B C : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] [CommRing C] [Algebra S C]
    (f : A →ₐ[S] B) (g : B →ₐ[S] C) : homAt x0 g ≫ homAt x0 f = homAt x0 (g.comp f) := by
  apply Over.OverMorphism.ext
  simp only [homAt, Over.comp_left, Over.homMk_left, spMap, ← Spec.map_comp]
  rfl

theorem homAt_id {A : Type} [CommRing A] [Algebra S A] : homAt x0 (AlgHom.id S A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp only [homAt, Over.homMk_left, Over.id_left, spMap]
  exact Spec.map_id _

abbrev tm {M N : Type} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    [Module Sᵐᵒᵖ M] [IsCentralScalar S M] [Module Sᵐᵒᵖ N] [IsCentralScalar S N] (L : M →ₗ[S] N) :
    TrivSqZeroExt S M →ₐ[S] TrivSqZeroExt S N := TrivSqZeroExt.map L

variable {G : Over X0} [GrpObj G]

def smT (a : S) (v : overAt x0 (DualNumber S) ⟶ G) : overAt x0 (DualNumber S) ⟶ G :=
  homAt x0 (tm (a • (LinearMap.id : S →ₗ[S] S))) ≫ v

theorem smT_left (a : S) (v : overAt x0 (DualNumber S) ⟶ G) : (smT x0 a v).left = spMap (epsMul a) ≫ v.left := rfl

theorem smT_mul (a : S) (u w : overAt x0 (DualNumber S) ⟶ G) : smT x0 a (u * w) = smT x0 a u * smT x0 a w :=
  MonObj.comp_mul _ _ _

theorem smT_one' (a : S) : smT x0 a (1 : overAt x0 (DualNumber S) ⟶ G) = 1 := MonObj.comp_one _

theorem smT_smT (a b : S) (v : overAt x0 (DualNumber S) ⟶ G) : smT x0 a (smT x0 b v) = smT x0 (a * b) v := by
  simp only [smT]
  rw [← Category.assoc, homAt_comp, ← TrivSqZeroExt.map_comp_map]
  congr 3
  ext
  simp

theorem smT_unit (v : overAt x0 (DualNumber S) ⟶ G) : smT x0 1 v = v := by
  simp only [smT, one_smul, tm]
  rw [TrivSqZeroExt.map_id, homAt_id, Category.id_comp]

theorem smT_comp {G' : Over X0} (a : S) (v : overAt x0 (DualNumber S) ⟶ G) (φ : G ⟶ G') :
    homAt x0 (tm (a • (LinearMap.id : S →ₗ[S] S))) ≫ (v ≫ φ) = smT x0 a v ≫ φ := by
  simp only [smT, Category.assoc]

theorem smT_add (v : overAt x0 (DualNumber S) ⟶ G) (h0 : smT x0 0 v = 1) (a b : S) :
    smT x0 (a + b) v = smT x0 a v * smT x0 b v := by
  have key : homAt x0 (tm (LinearMap.prod LinearMap.id LinearMap.id : S →ₗ[S] S × S)) ≫ v =
      (homAt x0 (tm (LinearMap.inl S S S)) ≫ v) * (homAt x0 (tm (LinearMap.inr S S S)) ≫ v) := by
    have hz : (0 : S →ₗ[S] S) = (0 : S) • (LinearMap.id : S →ₗ[S] S) := by simp
    apply Over.OverMorphism.ext
    apply spec_ext_two (tm (LinearMap.fst S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S)
      (tm (LinearMap.snd S S S) : TrivSqZeroExt S (S × S) →+* DualNumber S)
    · intro y
      refine ⟨tm (LinearMap.inl S S S) y, ?_⟩
      ext <;> simp
    · intro x hx
      have h1 : x.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hx
      ext <;> simp [h1]
    · intro x hx hx'
      have h1 : x.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hx
      have h2 : x.snd.1 = 0 := by simpa using congrArg TrivSqZeroExt.snd hx
      have h3 : x.snd.2 = 0 := by simpa using congrArg TrivSqZeroExt.snd hx'
      ext <;> simp [h1, h2, h3]
    · have h : homAt x0 (tm (LinearMap.fst S S S)) ≫
          homAt x0 (tm (LinearMap.prod LinearMap.id LinearMap.id : S →ₗ[S] S × S)) ≫ v =
          homAt x0 (tm (LinearMap.fst S S S)) ≫
            ((homAt x0 (tm (LinearMap.inl S S S)) ≫ v) * (homAt x0 (tm (LinearMap.inr S S S)) ≫ v)) := by
        rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
          homAt_comp, ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
          LinearMap.fst_prod, LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, hz]
        change _ = _ * smT x0 0 v
        rw [h0, _root_.mul_one]
      exact congrArg (fun φ => φ.left) h
    · have h : homAt x0 (tm (LinearMap.snd S S S)) ≫
          homAt x0 (tm (LinearMap.prod LinearMap.id LinearMap.id : S →ₗ[S] S × S)) ≫ v =
          homAt x0 (tm (LinearMap.snd S S S)) ≫
            ((homAt x0 (tm (LinearMap.inl S S S)) ≫ v) * (homAt x0 (tm (LinearMap.inr S S S)) ≫ v)) := by
        rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
          homAt_comp, ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
          LinearMap.snd_prod, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, hz]
        change _ = smT x0 0 v * _
        rw [h0, _root_.one_mul]
      exact congrArg (fun φ => φ.left) h
  have h := congrArg (fun φ => homAt x0 (tm (LinearMap.coprod (a • (LinearMap.id : S →ₗ[S] S))
    (b • (LinearMap.id : S →ₗ[S] S)))) ≫ φ) key
  beta_reduce at h
  rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp,
    homAt_comp, ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map, ← TrivSqZeroExt.map_comp_map,
    LinearMap.coprod_inl, LinearMap.coprod_inr] at h
  have hs : (LinearMap.coprod (a • (LinearMap.id : S →ₗ[S] S)) (b • (LinearMap.id : S →ₗ[S] S))).comp
      (LinearMap.prod LinearMap.id LinearMap.id) = (a + b) • (LinearMap.id : S →ₗ[S] S) := by
    ext
    simp
  rw [hs] at h
  exact h

theorem smT_post (a : S) (v : overAt x0 (DualNumber S) ⟶ G) (φ : G ⟶ G) :
    smT x0 a (v ≫ φ) = smT x0 a v ≫ φ := (Category.assoc _ _ _).symm

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem smT_zero_of (W : overAt x0 (DualNumber S) ⟶ G)
    (hv : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ W.left = (1 : Over.mk x0 ⟶ G).left) :
    smT x0 0 W = 1 := by
  have he : epsMul (0 : S) = (algebraMap S (DualNumber S)).comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
    apply RingHom.ext
    intro r
    ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  let φ : overAt x0 (DualNumber S) ⟶ Over.mk x0 := Over.homMk (spMap (algebraMap S (DualNumber S))) rfl
  have h1 : (φ ≫ (1 : Over.mk x0 ⟶ G)) = 1 := MonObj.comp_one φ
  apply Over.OverMorphism.ext
  rw [← h1, smT_left]
  simp only [Over.homMk_left, Over.comp_left, φ]
  rw [he, ← spMap_comp', Category.assoc, hv]

theorem unit_of_smT_zero (W : overAt x0 (DualNumber S) ⟶ G) (h : smT x0 0 W = 1) :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ W.left = (1 : Over.mk x0 ⟶ G).left := by
  have hid : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
    apply RingHom.ext
    intro r
    simp
  let ψ : Over.mk x0 ⟶ overAt x0 (DualNumber S) := Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
    show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) ≫ x0 = x0
    rw [← Category.assoc, spMap_comp', hid]
    simp [spMap])
  have hψ : ψ ≫ homAt x0 (tm ((0 : S) • (LinearMap.id : S →ₗ[S] S))) = ψ := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, ψ, Over.homMk_left, homAt]
    rw [spMap_comp']
    congr 1
    apply RingHom.ext
    intro r
    simp
  have h1 : ψ ≫ W = 1 := by
    rw [← hψ, Category.assoc]
    change ψ ≫ smT x0 0 W = 1
    rw [h, MonObj.comp_one]
  exact congrArg (fun φ => φ.left) h1

variable [IsCommMonObj G]

def smHom (a : S) : (overAt x0 (DualNumber S) ⟶ G) →* (overAt x0 (DualNumber S) ⟶ G) where
  toFun := smT x0 a
  map_one' := smT_one' x0 a
  map_mul' := smT_mul x0 a

variable (G) in

def TanSp : Type := Additive (smHom (G := G) x0 0).ker

instance : AddCommGroup (TanSp x0 G) := inferInstanceAs (AddCommGroup (Additive (smHom (G := G) x0 0).ker))

variable {x0}

def TanSp.pt (m : TanSp x0 G) : overAt x0 (DualNumber S) ⟶ G :=
  (Additive.toMul (show Additive (smHom (G := G) x0 0).ker from m)).1

def TanSp.mk (W : overAt x0 (DualNumber S) ⟶ G) (h : smT x0 0 W = 1) : TanSp x0 G :=
  (Additive.ofMul (⟨W, h⟩ : (smHom (G := G) x0 0).ker) : Additive (smHom (G := G) x0 0).ker)

theorem TanSp.pt_mk (W : overAt x0 (DualNumber S) ⟶ G) (h : smT x0 0 W = 1) : (TanSp.mk W h).pt = W := rfl

theorem TanSp.tan (m : TanSp x0 G) : smT x0 0 m.pt = 1 :=
  (Additive.toMul (show Additive (smHom (G := G) x0 0).ker from m)).2

theorem TanSp.ext {m n : TanSp x0 G} (h : m.pt = n.pt) : m = n := Subtype.ext h

theorem TanSp.pt_add (m n : TanSp x0 G) : (m + n).pt = m.pt * n.pt := rfl

theorem TanSp.pt_zero : (0 : TanSp x0 G).pt = 1 := rfl

instance : SMul S (TanSp x0 G) where
  smul a m := TanSp.mk (smT x0 a m.pt) (by rw [smT_smT, zero_mul, m.tan])

theorem TanSp.pt_smul (a : S) (m : TanSp x0 G) : (a • m).pt = smT x0 a m.pt := rfl

instance : Module S (TanSp x0 G) where
  one_smul m := TanSp.ext (smT_unit x0 _)
  mul_smul a b m := TanSp.ext (smT_smT x0 a b _).symm
  smul_zero a := TanSp.ext (smT_one' x0 a)
  smul_add a m n := TanSp.ext (smT_mul x0 a _ _)
  add_smul a b m := TanSp.ext (smT_add x0 _ m.tan a b)
  zero_smul m := TanSp.ext m.tan

theorem TanSp.pt_sum {κ : Type} (s : Finset κ) (f : κ → TanSp x0 G) :
    (∑ i ∈ s, f i).pt = ∏ i ∈ s, (f i).pt := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, TanSp.pt_add, ih]

variable (x0) in

def TanSp.post (φ : G ⟶ G) (hφ : IsMonHom φ) : Module.End S (TanSp x0 G) where
  toFun m := TanSp.mk (m.pt ≫ φ) (by rw [smT_post, m.tan, MonObj.one_comp])
  map_add' m n := TanSp.ext (MonObj.mul_comp _ _ φ)
  map_smul' a m := TanSp.ext (smT_post x0 a _ φ).symm

theorem TanSp.pt_post (φ : G ⟶ G) (hφ : IsMonHom φ) (m : TanSp x0 G) :
    (TanSp.post x0 φ hφ m).pt = m.pt ≫ φ := rfl

variable (x0) in

def TanSp.act {O : Type} [CommRing O] (A : OAct O G) : O →+* Module.End S (TanSp x0 G) :=
  RingHom.mk'
    { toFun := fun a => TanSp.post x0 (A.act a) (A.hom a)
      map_one' := LinearMap.ext fun m => TanSp.ext (by
        rw [TanSp.pt_post, A.one, Category.comp_id]; rfl)
      map_mul' := fun a b => LinearMap.ext fun m => TanSp.ext (by
        rw [Module.End.mul_apply, TanSp.pt_post, TanSp.pt_post, TanSp.pt_post, _root_.mul_comm, A.mul,
          Category.assoc]) }
    (fun a b => LinearMap.ext fun m => TanSp.ext (by
      show m.pt ≫ A.act (a + b) = (m.pt ≫ A.act a) * (m.pt ≫ A.act b)
      rw [A.add, MonObj.comp_mul]))

end Tan

theorem exists_tangent_module : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X), ∃ (N : Type) (_ : AddCommGroup N) (_ : Module S N) (v : N → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (ρ : 𝓞 E →+* Module.End S N), Function.Injective v ∧ (∀ w, IsTanAt x w ↔ w ∈ Set.range v) ∧ (∀ (n : ℕ) (b : Fin n → N) (a : Fin n → S) w, IsCombAt x (fun i => v (b i)) a w ↔ w = v (∑ i, a i • b i)) ∧ (∀ a m, v (ρ a m) = v m ≫ (Xo.univ.t.act.act a).left) ∧ ∀ (s : S) m, v (s • m) = spMap (epsMul s) ≫ v m := by
  intro E _ _ _ H Dw l Xo S _ x
  refine ⟨TanSp x Xo.univ.t.G, inferInstance, inferInstance, fun m => m.pt.left, TanSp.act x Xo.univ.t.act,
    fun m n h => TanSp.ext (Over.OverMorphism.ext h), fun w => ⟨fun h => ?_, ?_⟩, fun n b a w => ⟨?_, ?_⟩,
    fun a m => rfl, fun s m => rfl⟩
  · exact ⟨TanSp.mk (Over.homMk w h.1) (smT_zero_of x _ h.2), rfl⟩
  · rintro ⟨m, rfl⟩
    exact ⟨Over.w m.pt, unit_of_smT_zero x _ m.tan⟩
  · rintro ⟨u, hu, rfl⟩
    have : u = fun i => (a i • b i).pt := funext fun i => Over.OverMorphism.ext (hu i)
    subst this
    rw [List.prod_ofFn, ← TanSp.pt_sum]
  · rintro rfl
    exact ⟨fun i => (a i • b i).pt, fun i => rfl, by rw [List.prod_ofFn, ← TanSp.pt_sum]⟩

end GlobalTheory.TanMod
