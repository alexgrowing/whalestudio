import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Formalism.LocalToGlobal.ProjectiveLattices.UnitIndepOfCharts
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointFieldFromTestRingStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IntRebase

open Formalism.L2.Pj
open Formalism.L2.PjFree (spMap_comp' epsMul_comp_alg)

section Ext

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

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

end Ext

section Tan

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

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

section Comb

variable [IsCommMonObj G]

def combT {m : ℕ} (v : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (a : Fin m → S) : overAt x0 (DualNumber S) ⟶ G :=
  ∏ j, smT x0 (a j) (v j)

def smHom (a : S) : (overAt x0 (DualNumber S) ⟶ G) →* (overAt x0 (DualNumber S) ⟶ G) where
  toFun := smT x0 a
  map_one' := smT_one' x0 a
  map_mul' := smT_mul x0 a

theorem smT_prod {κ : Type} (s : Finset κ) (a : S) (u : κ → (overAt x0 (DualNumber S) ⟶ G)) :
    smT x0 a (∏ i ∈ s, u i) = ∏ i ∈ s, smT x0 a (u i) := map_prod (smHom x0 a) u s

theorem smT_sum {κ : Type} (s : Finset κ) (c : κ → S) (v : overAt x0 (DualNumber S) ⟶ G) (h0 : smT x0 0 v = 1) :
    smT x0 (∑ i ∈ s, c i) v = ∏ i ∈ s, smT x0 (c i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, smT_add x0 v h0, ih]

theorem smT_combT {m : ℕ} (a : S) (v : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (c : Fin m → S) :
    smT x0 a (combT x0 v c) = combT x0 v (fun j => a * c j) := by
  simp only [combT, smT_prod, smT_smT]

theorem combT_combT {m m' : ℕ} (v : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (hv : ∀ j, smT x0 0 (v j) = 1)
    (A : Matrix (Fin m) (Fin m') S) (N : Fin m' → S) :
    combT x0 (fun i => combT x0 v (fun j => A j i)) N = combT x0 v (A.mulVec N) := by
  simp only [combT, smT_prod, smT_smT]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← smT_sum x0 _ _ _ (hv j)]
  congr 1
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun i _ => _root_.mul_comm _ _

theorem combT_zero {m : ℕ} (v : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (hv : ∀ j, smT x0 0 (v j) = 1) :
    combT x0 v 0 = 1 := Finset.prod_eq_one fun j _ => hv j

theorem combT_tan {m : ℕ} (v : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (hv : ∀ j, smT x0 0 (v j) = 1)
    (c : Fin m → S) : smT x0 0 (combT x0 v c) = 1 := by
  rw [smT_combT]
  simp only [zero_mul]
  exact combT_zero x0 v hv

theorem combT_single {m : ℕ} (v : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (hv : ∀ j, smT x0 0 (v j) = 1)
    (j : Fin m) : combT x0 v (Pi.single j 1) = v j := by
  rw [combT, Finset.prod_eq_single j]
  · rw [Pi.single_eq_same, smT_unit]
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij]
    exact hv i
  · intro h; exact absurd (Finset.mem_univ j) h

theorem tan_pull {P : Over X0} (ψ : P ⟶ overAt x0 (DualNumber S))
    (hψ : ψ ≫ homAt x0 (tm ((0 : S) • (LinearMap.id : S →ₗ[S] S))) = ψ) (W : overAt x0 (DualNumber S) ⟶ G)
    (h : smT x0 0 W = 1) : ψ ≫ W = 1 := by
  rw [← hψ, Category.assoc]
  change ψ ≫ smT x0 0 W = 1
  rw [h, MonObj.comp_one]

theorem smT_post (a : S) (v : overAt x0 (DualNumber S) ⟶ G) (φ : G ⟶ G) :
    smT x0 a (v ≫ φ) = smT x0 a v ≫ φ := (Category.assoc _ _ _).symm

def postHom (φ : G ⟶ G) [IsMonHom φ] : (overAt x0 (DualNumber S) ⟶ G) →* (overAt x0 (DualNumber S) ⟶ G) where
  toFun := fun v => v ≫ φ
  map_one' := MonObj.one_comp φ
  map_mul' := fun u w => MonObj.mul_comp u w φ

theorem combT_post {m : ℕ} (v : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (a : Fin m → S) (φ : G ⟶ G) [IsMonHom φ] :
    combT x0 v a ≫ φ = combT x0 (fun j => v j ≫ φ) a := by
  have h := map_prod (postHom x0 φ) (fun j => smT x0 (a j) (v j)) Finset.univ
  simp only [combT, smT_post]
  exact h

end Comb

end Tan

section TanSAB

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)

theorem isCombAtG_iff {m : ℕ} (v : Fin m → (tEpsG x0 ⟶ t.G)) (cf : Fin m → S) (w : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x0 (fun j => (v j).left) cf w ↔ (combT x0 v cf).left = w := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : u = fun i => smT x0 (cf i) (v i) := funext fun i => Over.OverMorphism.ext (hu i)
    subst this
    rw [List.prod_ofFn]
    rfl
  · rintro rfl
    exact ⟨fun i => smT x0 (cf i) (v i), fun i => rfl, by rw [List.prod_ofFn]; rfl⟩

variable {t x0}

def ovT {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x0 v) : tEpsG x0 ⟶ t.G := Over.homMk v hv.1

theorem smT_zero_ovT {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x0 v) : smT x0 0 (ovT hv) = 1 := by
  have he : epsMul (0 : S) = (algebraMap S (DualNumber S)).comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
    apply RingHom.ext
    intro r
    ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  let φ : tEpsG x0 ⟶ Over.mk x0 := Over.homMk (spMap (algebraMap S (DualNumber S))) rfl
  have h1 : (φ ≫ (1 : Over.mk x0 ⟶ t.G)) = 1 := MonObj.comp_one φ
  apply Over.OverMorphism.ext
  rw [← h1, smT_left]
  simp only [ovT, Over.homMk_left, Over.comp_left, φ]
  rw [he, ← spMap_comp', Category.assoc, hv.2]

theorem isTanAtG_of (W : tEpsG x0 ⟶ t.G) (h : smT x0 0 W = 1) : IsTanAtG t x0 W.left := by
  refine ⟨Over.w W, ?_⟩
  have hid : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
    apply RingHom.ext
    intro r
    simp
  let ψ : Over.mk x0 ⟶ tEpsG x0 := Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
    show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) ≫ x0 = x0
    rw [← Category.assoc, spMap_comp', hid]
    simp [spMap])
  have h1 : ψ ≫ W = 1 := by
    refine tan_pull x0 ψ ?_ W h
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, ψ, Over.homMk_left, homAt]
    rw [spMap_comp']
    congr 1
    apply RingHom.ext
    intro r
    simp
  exact congrArg (fun φ => φ.left) h1

end TanSAB

section Sat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

section Gen

variable {X0 : Scheme.{0}} {G : Over X0} [GrpObj G]

def preHom {P Q : Over X0} (f : P ⟶ Q) : (Q ⟶ G) →* (P ⟶ G) where
  toFun := fun v => f ≫ v
  map_one' := MonObj.comp_one f
  map_mul' := fun u w => MonObj.comp_mul f u w

theorem comp_prodT [IsCommMonObj G] {P Q : Over X0} {κ : Type} (s : Finset κ) (f : P ⟶ Q) (u : κ → (Q ⟶ G)) :
    f ≫ ∏ i ∈ s, u i = ∏ i ∈ s, f ≫ u i := map_prod (preHom f) u s

end Gen

section Kap

variable {V : Type} [CommRing V]

def kap : tEpsG (𝟙 (Sp V)) ⟶ epsOver V V := Over.homMk (𝟙 _) (by
  show 𝟙 _ ≫ spMap ((algebraMap V (DualNumber V)).comp (algebraMap V V)) = spMap (algebraMap V (DualNumber V)) ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id])

def kapI : epsOver V V ⟶ tEpsG (𝟙 (Sp V)) := Over.homMk (𝟙 _) (by
  show 𝟙 _ ≫ spMap (algebraMap V (DualNumber V)) ≫ 𝟙 _ = spMap ((algebraMap V (DualNumber V)).comp (algebraMap V V))
  rw [Category.id_comp, Category.comp_id])

theorem kap_kapI : (kap : tEpsG (𝟙 (Sp V)) ⟶ epsOver V V) ≫ kapI = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp [kap, kapI]

theorem kapI_kap : (kapI : epsOver V V ⟶ tEpsG (𝟙 (Sp V))) ≫ kap = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp [kap, kapI]

variable {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G]

theorem isComb_iff {m : ℕ} (ub : Fin m → (epsOver V V ⟶ G)) (a : Fin m → V) (W : tEpsG (𝟙 (Sp V)) ⟶ G) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsComb ub a (kapI ≫ W) ↔ W = combT (𝟙 (Sp V)) (fun i => kap ≫ ub i) a := by
  constructor
  · rintro ⟨u, hu, h⟩
    have h1 : W = kap ≫ (List.ofFn u).prod := by rw [← h, ← Category.assoc, kap_kapI, Category.id_comp]
    rw [h1, List.prod_ofFn, comp_prodT]
    refine Finset.prod_congr rfl fun i _ => Over.OverMorphism.ext ?_
    simp [kap, smT_left, hu i]
  · rintro rfl
    refine ⟨fun i => kapI ≫ smT _ (a i) (kap ≫ ub i), fun i => by simp [kapI, kap, smT_left], ?_⟩
    rw [List.prod_ofFn, ← comp_prodT]
    rfl

theorem isTan_kapI (W : tEpsG (𝟙 (Sp V)) ⟶ G) (h : smT (𝟙 (Sp V)) 0 W = 1) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTan (kapI ≫ W) := by
  have hid : (TrivSqZeroExt.fstHom V V V).toRingHom.comp (algebraMap V (DualNumber V)) = algebraMap V V := by
    apply RingHom.ext
    intro r
    simp
  let ψ : ptOver V V ⟶ tEpsG (𝟙 (Sp V)) := Over.homMk (spMap (TrivSqZeroExt.fstHom V V V).toRingHom) (by
    show spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ spMap (algebraMap V (DualNumber V)) ≫ 𝟙 _ =
      spMap (algebraMap V V)
    rw [Category.comp_id, spMap_comp', hid])
  have h1 : ψ ≫ W = 1 := by
    refine tan_pull _ ψ ?_ W h
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, ψ, Over.homMk_left, homAt]
    rw [spMap_comp']
    congr 1
    apply RingHom.ext
    intro r
    simp
  have h2 := congrArg (fun φ => φ.left) h1
  simp only [Over.comp_left, ψ, Over.homMk_left] at h2
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTan
  simp only [Over.comp_left, kapI, Over.homMk_left, Category.id_comp]
  exact h2

end Kap

end Sat

section Reb

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

section GenA

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {G : Over X0} [GrpObj G] [IsCommMonObj G]

theorem combT_eig {m : ℕ} (U : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (φ : G ⟶ G) [IsMonHom φ] (z : S)
    (hU : ∀ j, U j ≫ φ = smT x0 z (U j)) (a : Fin m → S) : combT x0 U a ≫ φ = smT x0 z (combT x0 U a) := by
  rw [combT_post, smT_combT]
  show ∏ i, smT x0 (a i) (U i ≫ φ) = ∏ i, smT x0 (z * a i) (U i)
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hU, smT_smT, _root_.mul_comm]

theorem reframe_basis {m : ℕ} (U : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (hU : ∀ j, smT x0 0 (U j) = 1)
    (K : Matrix (Fin m) (Fin m) S) (hK : IsUnit K.det) (W : overAt x0 (DualNumber S) ⟶ G)
    (hb : ∃! a : Fin m → S, W = combT x0 U a) :
    ∃! a : Fin m → S, W = combT x0 (fun i => combT x0 U (fun j => K j i)) a := by
  obtain ⟨b, hb1, hb2⟩ := hb
  refine ⟨K⁻¹.mulVec b, ?_, fun a ha => ?_⟩
  · show W = combT x0 (fun i => combT x0 U (fun j => K j i)) (K⁻¹.mulVec b)
    rw [combT_combT x0 U hU, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv K hK, Matrix.one_mulVec]
    exact hb1
  · have ha' : W = combT x0 (fun i => combT x0 U (fun j => K j i)) a := ha
    rw [combT_combT x0 U hU] at ha'
    rw [← hb2 _ ha', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul K hK, Matrix.one_mulVec]

end GenA

section Pull

variable {S' S0 : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S0} [GrpObj G] {f : S' ⟶ S0}
  {φ : G'.left ⟶ G.left}

theorem grpPull_one (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  let e0 : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    show ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = T.hom ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w])
  have h1 : (e0 * e0).left = ((1 : T ⟶ G') * 1).left ≫ φ := h.2 T 1 1 e0 e0 rfl rfl
  rw [_root_.mul_one] at h1
  have h2 : e0 * e0 = e0 := Over.OverMorphism.ext h1
  have h3 : e0 = 1 := mul_eq_left.1 h2
  rw [← h3]
  rfl

theorem grpPull_prod [IsCommMonObj G'] [IsCommMonObj G] (h : IsGrpPullback G' G f φ) (T : Over S') {κ : Type}
    (s : Finset κ) (x : κ → (T ⟶ G')) (x₀ : κ → (Over.mk (T.hom ≫ f) ⟶ G))
    (hx : ∀ j, (x₀ j).left = (x j).left ≫ φ) : (∏ j ∈ s, x₀ j).left = (∏ j ∈ s, x j).left ≫ φ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using grpPull_one h T
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    exact h.2 T _ _ _ _ (hx j) ih

theorem spMap_frac_cancel {V K A : Type} [CommRing V] [CommRing K] [Algebra V K] [IsFractionRing V K] [CommRing A]
    (g h : Sp A ⟶ Sp K) (e : g ≫ spMap (algebraMap V K) = h ≫ spMap (algebraMap V K)) : g = h := by
  rw [← Spec.map_preimage g, ← Spec.map_preimage h] at e ⊢
  simp only [spMap, ← Spec.map_comp] at e
  have e1 := Spec.map_injective e
  congr 1
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (nonZeroDivisors V)
  exact congrArg CommRingCat.Hom.hom e1

end Pull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem isEigAt_iff {S : Type} [CommRing S] [Algebra c.F S] {x : Sp S ⟶ Xo.X} (τ : E →+* ℂ)
    (W : tEpsG x ⟶ Xo.univ.t.G) :
    IsEigAt c τ W.left ↔ ∀ a : 𝓞 E, W ≫ Xo.univ.t.act.act a = smT x (algebraMap c.F S (embK c τ a)) W :=
  ⟨fun h a => Over.OverMorphism.ext (h a), fun h a => congrArg (fun φ => φ.left) (h a)⟩

def rebase₂ {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (K : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (hK : ∀ τ, IsUnit (K τ).det) :
    FrPt Xo c S where
  x := y.x
  x_over := y.x_over
  u := fun τ i => (combT y.x (fun j => ovT (t := Xo.univ.t) (y.tan τ j)) (fun j => K τ j i)).left
  tan := fun τ i => isTanAtG_of (t := Xo.univ.t) _ (combT_tan _ _ (fun j => smT_zero_ovT _) _)
  eig := fun τ i => (isEigAt_iff τ _).2 fun a => by
    have := Xo.univ.t.act.hom a
    exact combT_eig _ _ _ _ (fun j => (isEigAt_iff τ (ovT (t := Xo.univ.t) (y.tan τ j))).1 (y.eig τ j) a) _
  basis := fun τ w hw he => by
    have h2 : ∃! a : Fin (Dw.mult τ) → S, ovT (t := Xo.univ.t) hw =
        combT y.x (fun j => ovT (t := Xo.univ.t) (y.tan τ j)) a := by
      obtain ⟨a, ha, hu⟩ := y.basis τ w hw he
      exact ⟨a, Over.OverMorphism.ext
          ((isCombAtG_iff Xo.univ.t y.x (fun j => ovT (t := Xo.univ.t) (y.tan τ j)) _ _).1 ha).symm,
        fun b hb => hu b ((isCombAtG_iff Xo.univ.t y.x (fun j => ovT (t := Xo.univ.t) (y.tan τ j)) _ _).2
          (by rw [← hb]; rfl))⟩
    obtain ⟨a, ha, hu⟩ := reframe_basis y.x _ (fun j => smT_zero_ovT _) (K τ) (hK τ) _ h2
    exact ⟨a, (isCombAtG_iff Xo.univ.t y.x _ _ _).2 (by rw [← ha]; rfl),
      fun b hb => hu b (Over.OverMorphism.ext ((isCombAtG_iff Xo.univ.t y.x _ _ _).1 hb).symm)⟩
  s := y.s
  gen := y.gen

section KapMore

variable {V : Type} [CommRing V]

theorem kapI_kap_assoc {G : Over (Sp V)} (w : epsOver V V ⟶ G) : kapI ≫ kap ≫ w = w := by
  rw [← Category.assoc, kapI_kap, Category.id_comp]

theorem kap_kapI_assoc {G : Over (Sp V)} (W : tEpsG (𝟙 (Sp V)) ⟶ G) : kap ≫ kapI ≫ W = W := by
  rw [← Category.assoc, kap_kapI, Category.id_comp]

theorem smT_zero_kap {G : Over (Sp V)} [GrpObj G] (w : epsOver V V ⟶ G) (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTan w) :
    smT (𝟙 (Sp V)) 0 (kap ≫ w) = 1 := by
  have he : epsMul (0 : V) = (algebraMap V (DualNumber V)).comp (TrivSqZeroExt.fstHom V V V).toRingHom := by
    apply RingHom.ext
    intro r
    ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  have h' : spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ w.left = (1 : ptOver V V ⟶ G).left := h
  let φ : tEpsG (𝟙 (Sp V)) ⟶ ptOver V V := Over.homMk (spMap (algebraMap V (DualNumber V))) (by
    show spMap (algebraMap V (DualNumber V)) ≫ spMap (algebraMap V V) = spMap (algebraMap V (DualNumber V)) ≫ 𝟙 _
    rw [spMap_comp', Category.comp_id])
  have h1 : (φ ≫ (1 : ptOver V V ⟶ G)) = 1 := MonObj.comp_one φ
  apply Over.OverMorphism.ext
  rw [← h1, smT_left]
  simp only [kap, Over.homMk_left, Over.comp_left, φ, Category.id_comp]
  rw [he, ← spMap_comp', Category.assoc, h']

theorem isEigV_kapI_iff {Fr : Type} [Field Fr] [Algebra V Fr] (io : c.F →+* Fr) (G : SAB H (Sp V)) (τ : E →+* ℂ)
    (W : tEpsG (𝟙 (Sp V)) ⟶ G.G) :
    IsEigV c io G τ (kapI ≫ W) ↔ ∀ (a : 𝓞 E) (z : V), algebraMap V Fr z = io (embK c τ a) →
      W ≫ G.act.act a = smT (𝟙 (Sp V)) z W := by
  constructor
  · intro h a z hz
    apply Over.OverMorphism.ext
    have h1 := h a z hz
    simp only [Over.comp_left, smT_left, kapI, Over.homMk_left, Category.id_comp] at h1 ⊢
    exact h1
  · intro h a z hz
    have h1 := congrArg (fun φ => φ.left) (h a z hz)
    simp only [Over.comp_left, smT_left, kapI, Over.homMk_left, Category.id_comp] at h1 ⊢
    exact h1

end KapMore

theorem dualMap_comp_alg {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (dualMap f).comp (algebraMap A (DualNumber A)) = (algebraMap B (DualNumber B)).comp f := by
  apply RingHom.ext
  intro r
  ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp_epsMul {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    (dualMap f).comp (epsMul a) = (epsMul (f a)).comp (dualMap f) := by
  apply RingHom.ext
  intro r
  ext <;> simp [dualMap, epsMul, _root_.mul_comm]

theorem integral_reb (T : CDVR) (io : c.F →+* T.Fr) : letI := io.toAlgebra
    ∀ (y : FrPt Xo c T.Fr), Integral T io y →
      ∀ (k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V), (∀ τ, IsUnit (k τ).det) →
        ∀ hK : ∀ τ, IsUnit ((k τ).map (algebraMap T.V T.Fr)).det,
          Integral T io (rebase₂ y (fun τ => (k τ).map (algebraMap T.V T.Fr)) hK) := by
  let _ := io.toAlgebra
  intro y h k hk hK
  obtain ⟨G, t', m1, m2, ⟨ub, htan, heig, hbas, hlift⟩, hθ⟩ := h
  let Ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (tEpsG (𝟙 (Sp T.V)) ⟶ G.G) := fun τ j => kap ≫ ub τ j
  have hUb0 : ∀ τ j, smT (𝟙 (Sp T.V)) 0 (Ub τ j) = 1 := fun τ j => smT_zero_kap _ (htan τ j)
  have hUbE : ∀ τ j (a : 𝓞 E) (z : T.V), algebraMap T.V T.Fr z = io (embK c τ a) →
      Ub τ j ≫ G.act.act a = smT (𝟙 (Sp T.V)) z (Ub τ j) := fun τ j =>
    (isEigV_kapI_iff io G τ _).1 (by rw [kapI_kap_assoc]; exact heig τ j)
  refine ⟨G, t', m1, m2, ⟨fun τ i => kapI ≫ combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i), ?_, ?_, ?_, ?_⟩, hθ⟩
  · intro τ i
    exact isTan_kapI _ (combT_tan _ _ (hUb0 τ) _)
  · intro τ i
    refine (isEigV_kapI_iff io G τ _).2 fun a z hz => ?_
    have := G.act.hom a
    exact combT_eig _ _ _ _ (fun j => hUbE τ j a z hz) _
  · intro τ w hw he
    have h1 : ∃! a : Fin (Dw.mult τ) → T.V, kap ≫ w = combT (𝟙 (Sp T.V)) (Ub τ) a := by
      obtain ⟨a, ha, hu⟩ := hbas τ w hw he
      refine ⟨a, (isComb_iff _ _ _).1 (by rw [kapI_kap_assoc]; exact ha), fun b hb => hu b ?_⟩
      have h2 := (isComb_iff (ub τ) b (kap ≫ w)).2 hb
      rw [kapI_kap_assoc] at h2
      exact h2
    obtain ⟨a, ha, hu⟩ := reframe_basis _ (Ub τ) (hUb0 τ) (k τ) (hk τ) _ h1
    have e : (fun i => kap ≫ (kapI ≫ combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i))) =
        fun i => combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i) := funext fun i => kap_kapI_assoc _
    refine ⟨a, ?_, fun b hb => hu b ?_⟩
    · have h2 := (isComb_iff (fun i => kapI ≫ combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i)) a (kap ≫ w)).2
        (by rw [e]; exact ha)
      rw [kapI_kap_assoc] at h2
      exact h2
    · have h2 := (isComb_iff (fun i => kapI ≫ combT (𝟙 (Sp T.V)) (Ub τ) (fun j => k τ j i)) b (kap ≫ w)).1
        (by rw [kapI_kap_assoc]; exact hb)
      rw [e] at h2
      exact h2
  · intro τ i
    choose u' hu1 hu2 using hlift τ
    have hδ : spMap (dualMap (algebraMap T.V T.Fr)) ≫
        spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) =
        spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr) := by
      rw [spMap_comp', spMap_comp']
      show spMap ((dualMap (algebraMap T.V T.Fr)).comp (algebraMap T.V (DualNumber T.V))) = _
      rw [dualMap_comp_alg]
    have hov : ∀ j, u' j ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      intro j
      apply spMap_frac_cancel (V := T.V)
      rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu2 j, Category.assoc, Over.w (ub τ j)]
      exact hδ
    let T' : Over (Sp T.Fr) := Over.mk (spMap (algebraMap T.Fr (DualNumber T.Fr)))
    let cf : Fin (Dw.mult τ) → T.Fr := fun j => algebraMap T.V T.Fr (k τ j i)
    let Y : Fin (Dw.mult τ) → (T' ⟶ t'.G) := fun j => Over.homMk (spMap (epsMul (cf j)) ≫ u' j) (by
      show (spMap (epsMul (cf j)) ≫ u' j) ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr))
      rw [Category.assoc, hov, spMap_comp', epsMul_comp_alg])
    refine ⟨(∏ j, Y j).left, ?_, ?_⟩
    · have hA := grpPull_prod m1.cart T' Finset.univ Y
        (fun j => smT y.x (cf j) (ovT (t := Xo.univ.t) (y.tan τ j))) (fun j => by
          show spMap (epsMul (cf j)) ≫ y.u τ j = (spMap (epsMul (cf j)) ≫ u' j) ≫ m1.φ
          rw [Category.assoc, hu1])
      exact hA.symm
    · let δ : Over.mk (T'.hom ≫ spMap (algebraMap T.V T.Fr)) ⟶ epsOver T.V T.V :=
        Over.homMk (spMap (dualMap (algebraMap T.V T.Fr))) hδ
      have hB := grpPull_prod m2.cart T' Finset.univ Y
        (fun j => δ ≫ kapI ≫ smT (𝟙 (Sp T.V)) (k τ j i) (Ub τ j)) (fun j => by
          simp only [Over.comp_left, δ, kapI, kap, Ub, smT_left, Over.homMk_left, Category.id_comp, Y,
            Category.assoc]
          rw [hu2 j, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_epsMul])
      rw [← hB, ← comp_prodT, ← comp_prodT]
      rfl

theorem id_appLE_apply (X : Scheme.{0}) (U : X.Opens) (h : U ≤ (𝟙 X) ⁻¹ᵁ U) (s : Γ(X, U)) :
    ((𝟙 X : X ⟶ X).appLE U U h).hom s = s := by
  simp only [Scheme.Hom.appLE]
  have e : (homOfLE h).op = 𝟙 _ := Subsingleton.elim _ _
  rw [e]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

theorem scal_mul' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_mul]

theorem scal_one' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x 1 i = 1 := by
  simp [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]

theorem gen_unit' {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} (s s' : ReciprocityTheory.ChartRestriction.G.Semi.LB.Sec (PPx x))
    (hs : ∀ s'' : ReciprocityTheory.ChartRestriction.G.Semi.LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s.f i)
    (hs' : ∀ s'' : ReciprocityTheory.ChartRestriction.G.Semi.LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s'.f i) :
    ∃ u : Sˣ, ∀ i, s'.f i = scal x (u : S) i * s.f i := by
  obtain ⟨a, ha, -⟩ := hs s'
  obtain ⟨b, hb, -⟩ := hs' s
  obtain ⟨c1, -, hc1⟩ := hs s
  have h1 : b * a = 1 := by
    have e1 : ∀ i, s.f i = scal x (b * a) i * s.f i := fun i => by
      rw [scal_mul', _root_.mul_assoc, ← ha i, ← hb i]
    have e2 : ∀ i, s.f i = scal x 1 i * s.f i := fun i => by rw [scal_one', _root_.one_mul]
    exact (hc1 _ e1).trans (hc1 _ e2).symm
  exact ⟨⟨a, b, by rw [_root_.mul_comm]; exact h1, h1⟩, ha⟩

theorem intRebase_of (hA : SpreadSt Xo c) : Formalism.L2.PjFree.IntRebase Xo c := by
  intro T io
  let _ := io.toAlgebra
  intro y0 z hx k hk
  have hK : ∀ τ, IsUnit ((k τ).map (algebraMap T.V T.Fr)).det := fun τ => by
    have e : ((k τ).map (algebraMap T.V T.Fr)).det = algebraMap T.V T.Fr (k τ).det :=
      (RingHom.map_det _ _).symm
    rw [e]
    exact (hk τ).map _
  obtain ⟨zx, zo, zu, zt, ze, zb, zs, zg⟩ := z
  simp only at hx
  subst hx
  obtain ⟨u0, hu0⟩ := gen_unit' (x := y0.1.x) zs y0.1.s zg y0.1.gen
  refine ⟨⟨rebase₂ y0.1 _ hK, hA T.Fr _, integral_reb T io y0.1 y0.2.2 k hk hK⟩, u0, rfl, fun τ i => ?_,
    𝟙 _, Category.id_comp _, Category.id_comp _, ?_⟩
  · exact (isCombAtG_iff Xo.univ.t y0.1.x (fun j => ovT (t := Xo.univ.t) (y0.1.tan τ j)) _ _).2 rfl
  · intro i h
    show ((𝟙 _ : Gx y0.1.x ⟶ Gx y0.1.x).appLE _ _ h).hom (scal y0.1.x (u0 : T.Fr) i * zs.f i) = y0.1.s.f i
    rw [← hu0 i]
    exact id_appLE_apply _ _ h _

end Reb

end GlobalTheory.IntRebase

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem GlobalTheory.IntRebase.intRebase : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Formalism.L2.PjFree.IntRebase Xo c :=
  fun h E _ _ _ H Dw l Xo c => GlobalTheory.IntRebase.intRebase_of (GlobalTheory.T.framedPoint_field_from_testRing h E H Dw l Xo c)
