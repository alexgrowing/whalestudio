import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusIsCommMonObjSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsaRos

universe u

namespace ReciprocityTheory.ChartRestriction.G.Semi

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj MonObj TensorProduct
open AddMonoidAlgebra

namespace Rosenlicht

theorem ringHom_uliftInt_ext {A : Type*} [Semiring A] (f g : ULift.{u} ℤ →+* A) : f = g := by
  first
  | exact Subsingleton.elim f g
  | (ext x
     exact RingHom.congr_fun (RingHom.ext_int (f.comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm.toRingHom)
       (g.comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm.toRingHom)) x.down)

theorem isUnit_eq_single {R A : Type*} [CommRing R] [IsDomain R] [AddCommMonoid A] [TwoUniqueSums A]
    {u : AddMonoidAlgebra R A} (hu : IsUnit u) : ∃ a c, IsUnit c ∧ u = single a c := by
  obtain ⟨v, huv⟩ := hu.exists_right_inv
  have coeffInj : ∀ p q : AddMonoidAlgebra R A, p.coeff = q.coeff → p = q := by
    intro p q hpq
    first
    | exact AddMonoidAlgebra.coeff_injective hpq
    | exact AddMonoidAlgebra.coeff_inj.1 hpq
    | exact AddMonoidAlgebra.ext hpq
    | (cases p; cases q; simp_all)
  have key : ∀ a0 b0 : A, UniqueAdd u.coeff.support v.coeff.support a0 b0 →
      (u * v).coeff (a0 + b0) = u.coeff a0 * v.coeff b0 := by
    intro a0 b0 h
    first
    | exact AddMonoidAlgebra.coeff_mul_apply_add_eq_mul_of_uniqueAdd h
    | exact AddMonoidAlgebra.mul_coeff_add_eq_mul_of_uniqueAdd h
    | exact AddMonoidAlgebra.coeff_mul_of_uniqueAdd h
    | exact AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd h
    | exact Finsupp.mul_apply_add_eq_mul_of_uniqueAdd h
  have hone : (u * v).coeff = Finsupp.single 0 1 := by
    rw [huv]
    first
    | (simp [AddMonoidAlgebra.one_def]; done)
    | exact AddMonoidAlgebra.coeff_one
    | rfl
  have hcard : u.coeff.support.card * v.coeff.support.card ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨p1, hp1, p2, hp2, hne, hu1, hu2⟩ := TwoUniqueSums.uniqueAdd_of_one_lt_card hlt
    rw [Finset.mem_product] at hp1 hp2
    have n1 : u.coeff p1.1 * v.coeff p1.2 ≠ 0 :=
      mul_ne_zero (Finsupp.mem_support_iff.1 hp1.1) (Finsupp.mem_support_iff.1 hp1.2)
    have n2 : u.coeff p2.1 * v.coeff p2.2 ≠ 0 :=
      mul_ne_zero (Finsupp.mem_support_iff.1 hp2.1) (Finsupp.mem_support_iff.1 hp2.2)
    have e1 := key _ _ hu1
    have e2 := key _ _ hu2
    rw [hone] at e1 e2
    have s1 : p1.1 + p1.2 = 0 := by
      by_contra hs
      exact n1 (by simpa [Finsupp.single_apply, Ne.symm hs] using e1.symm)
    have s2 : p2.1 + p2.2 = 0 := by
      by_contra hs
      exact n2 (by simpa [Finsupp.single_apply, Ne.symm hs] using e2.symm)
    obtain ⟨q1, q2⟩ := hu1 hp2.1 hp2.2 (s2.trans s1.symm)
    exact hne (Prod.ext q1.symm q2.symm)
  have nz : ∀ p : AddMonoidAlgebra R A, p * v = 1 ∨ u * p = 1 → p.coeff ≠ 0 := by
    intro p hp h0
    have hp0 : p = 0 := coeffInj p 0 (by simpa using h0)
    rcases hp with hp | hp <;> rw [hp0] at hp <;> simp at hp
  have hprod : u.coeff.support.card * v.coeff.support.card = 1 :=
    le_antisymm hcard (Nat.mul_pos (Finsupp.support_nonempty_iff.2 (nz u (Or.inl huv))).card_pos
      (Finsupp.support_nonempty_iff.2 (nz v (Or.inr huv))).card_pos)
  have cu : u.coeff.support.card = 1 := by
    first
    | exact Nat.eq_one_of_mul_eq_one_right hprod
    | exact (mul_eq_one.1 hprod).1
    | nlinarith
  have cv : v.coeff.support.card = 1 := by
    first
    | exact Nat.eq_one_of_mul_eq_one_left hprod
    | exact (mul_eq_one.1 hprod).2
    | nlinarith
  obtain ⟨a, hc0, hca⟩ := Finsupp.card_support_eq_one.1 cu
  obtain ⟨b, hd0, hdb⟩ := Finsupp.card_support_eq_one.1 cv
  have hu' : u = single a (u.coeff a) := coeffInj _ _ (by simpa using hca)
  have hv' : v = single b (v.coeff b) := coeffInj _ _ (by simpa using hdb)
  rw [hu', hv', single_mul_single] at huv
  have hcd : u.coeff a * v.coeff b = 1 := by
    have h3 := congrArg AddMonoidAlgebra.coeff huv
    simp only [AddMonoidAlgebra.one_def] at h3
    have h4 : Finsupp.single (a + b) (u.coeff a * v.coeff b) = Finsupp.single 0 1 := by
      simpa using h3
    rcases (Finsupp.single_eq_single_iff _ _ _ _).1 h4 with h5 | h5
    · exact h5.2
    · exact absurd h5.2 one_ne_zero
  have hcu : IsUnit (u.coeff a) := by
    first
    | exact isUnit_of_mul_eq_one _ _ hcd
    | exact IsUnit.of_mul_eq_one _ hcd
  exact ⟨a, u.coeff a, hcu, hu'⟩

theorem isUnit_single_one {R A : Type*} [CommRing R] [AddCommGroup A] (a : A) :
    IsUnit (single a (1 : R)) := by
  first
  | exact ⟨⟨single a 1, single (-a) 1, by simp [single_mul_single, AddMonoidAlgebra.one_def],
      by simp [single_mul_single, AddMonoidAlgebra.one_def]⟩, rfl⟩
  | exact isUnit_of_mul_eq_one _ (single (-a) 1)
      (by rw [single_mul_single, add_neg_cancel, mul_one, AddMonoidAlgebra.one_def])

theorem ringHom_ext_ZU {A Y : Type*} [Semiring A] [AddCommGroup Y]
    {f g : AddMonoidAlgebra (ULift.{u} ℤ) Y →+* A} (h : ∀ y, f (single y 1) = g (single y 1)) :
    f = g := by
  refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) h
  exact RingHom.congr_fun (ringHom_uliftInt_ext (f.comp AddMonoidAlgebra.singleZeroRingHom)
    (g.comp AddMonoidAlgebra.singleZeroRingHom)) b

theorem cr_iso_bij {R S : CommRingCat.{u}} (e : R ≅ S) : Function.Bijective e.hom.hom := by
  first
  | exact ConcreteCategory.bijective_of_isIso e.hom
  | exact e.commRingCatIsoToRingEquiv.bijective
  | exact ⟨fun x y hxy => by simpa using congrArg e.inv.hom hxy, fun y => ⟨e.inv.hom y, by simp⟩⟩

theorem isIso_appTop_bij {A B : Scheme.{u}} (e : A ≅ B) : Function.Bijective e.hom.appTop.hom := by
  first
  | exact cr_iso_bij (Scheme.Γ.mapIso e.op)
  | exact ConcreteCategory.bijective_of_isIso e.hom.appTop
  | exact cr_iso_bij (asIso e.hom.appTop)

private theorem comp_appTop_lemma {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).appTop = g.appTop ≫ f.appTop := by
  first
  | rfl
  | (simp; done)
  | exact Scheme.Hom.comp_appTop f g

theorem appTop_comp_apply {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (x : Γ(C, ⊤)) :
    (f ≫ g).appTop.hom x = f.appTop.hom (g.appTop.hom x) := by
  rw [comp_appTop_lemma]
  rfl

section
variable {S : Scheme.{u}}

noncomputable def torusFst (S : Scheme.{u}) (Y : Type u) [AddCommGroup Y] :
    (splitTorus S Y).left ⟶ Spec (torusRing ZU Y) :=
  pullback.fst (splitTorusAff ZU Y).hom (toZ S)

noncomputable def coord {Z : Over S} {Y : Type u} [AddCommGroup Y] (g : Z ⟶ splitTorus S Y) :
    torusRing ZU Y ⟶ Γ(Z.left, ⊤) :=
  (Scheme.ΓSpecIso (torusRing ZU Y)).inv ≫ (g.left ≫ torusFst S Y).appTop

theorem coord_comp {Z W : Over S} {Y : Type u} [AddCommGroup Y] (h : W ⟶ Z)
    (g : Z ⟶ splitTorus S Y) : coord (h ≫ g) = coord g ≫ h.left.appTop := by
  first
  | (simp only [coord, Over.comp_left, comp_appTop_lemma, Category.assoc]; done)
  | (simp only [coord, Comma.comp_left, comp_appTop_lemma, Category.assoc]; done)
  | (simp [coord, comp_appTop_lemma]; done)

theorem coord_injective {Z : Over S} {Y : Type u} [AddCommGroup Y] {g g' : Z ⟶ splitTorus S Y}
    (h : coord g = coord g') : g = g' := by
  have h1 : (g.left ≫ torusFst S Y).appTop = (g'.left ≫ torusFst S Y).appTop := by
    have h0 := congrArg (fun φ => (Scheme.ΓSpecIso (torusRing ZU Y)).hom ≫ φ) h
    simpa only [coord, Iso.hom_inv_id_assoc] using h0
  have h2 : g.left ≫ torusFst S Y = g'.left ≫ torusFst S Y := by
    first
    | exact ext_of_isAffine h1
    | exact Scheme.ext_of_isAffine h1
    | exact Scheme.Hom.ext_of_isAffine h1
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h2
  · exact (Over.w g).trans (Over.w g').symm

theorem toUnit_left (Z : Over S) : (toUnit Z).left = Z.hom := by
  first
  | simpa using Over.w (toUnit Z)
  | exact (Category.comp_id _).symm.trans (Over.w (toUnit Z))
  | (simp; done)
  | rfl

theorem over_appTop_comp {W Z V : Over S} (p : W ⟶ Z) (q : Z ⟶ V) (x : Γ(V.left, ⊤)) :
    p.left.appTop.hom (q.left.appTop.hom x) = (p ≫ q).left.appTop.hom x := by
  first
  | exact (appTop_comp_apply p.left q.left x).symm
  | (rw [Over.comp_left, appTop_comp_apply])

theorem toUnit_comp_appTop (Z : Over S) {V : Over S} (e : 𝟙_ (Over S) ⟶ V) (x : Γ(V.left, ⊤)) :
    (toUnit Z ≫ e).left.appTop.hom x = Z.hom.appTop.hom (e.left.appTop.hom x) := by
  first
  | (rw [← over_appTop_comp, toUnit_left])
  | exact (over_appTop_comp (toUnit Z) e x).symm.trans (by rw [toUnit_left])

theorem coord_toUnit_comp (Z : Over S) {Y : Type u} [AddCommGroup Y]
    (e : 𝟙_ (Over S) ⟶ splitTorus S Y) (x : torusRing ZU Y) :
    (coord (toUnit Z ≫ e)).hom x = Z.hom.appTop.hom ((coord e).hom x) := by
  rw [coord_comp]
  first
  | exact congrArg (fun f => Scheme.Hom.appTop f |>.hom ((coord e).hom x)) (toUnit_left Z)
  | (rw [CommRingCat.comp_apply, toUnit_left])
  | (simp [toUnit_left]; done)

noncomputable def chi (X : Type u) [AddCommGroup X] (a : X) : Γ((splitTorus S X).left, ⊤) :=
  (coord (𝟙 (splitTorus S X))).hom (single a 1)

theorem chi_zero (X : Type u) [AddCommGroup X] : chi (S := S) X 0 = 1 := by
  first
  | (show (coord (𝟙 (splitTorus S X))).hom (single 0 1) = 1
     rw [← AddMonoidAlgebra.one_def, map_one])
  | (simp only [chi]; rw [← AddMonoidAlgebra.one_def, map_one])
  | (simp [chi, AddMonoidAlgebra.one_def]; done)

theorem isUnit_chi (X : Type u) [AddCommGroup X] (a : X) : IsUnit (chi (S := S) X a) := by
  exact (isUnit_single_one (R := ULift.{u} ℤ) a).map (coord (𝟙 (splitTorus S X))).hom
end

section
variable (K : Type u) [Field K] (X : Type u) [AddCommGroup X]

noncomputable abbrev zuAlgebra : Algebra ZU K := ULift.algebra' ℤ K

attribute [local instance] zuAlgebra
open scoped AlgebraMonoidAlgebra

theorem toZ_eq : toZ (Spec (.of K)) = Spec.map (CommRingCat.ofHom (algebraMap ZU.{u} K)) := by
  first
  | exact specULiftZIsTerminal.hom_ext _ _
  | exact AlgebraicGeometry.specULiftZIsTerminal.hom_ext _ _
  | exact IsTerminal.hom_ext specULiftZIsTerminal _ _

instance isScalarTower_torus :
    IsScalarTower ZU.{u} (AddMonoidAlgebra ZU.{u} X) (AddMonoidAlgebra K X) :=
  ⟨fun r a b => by
    obtain ⟨n⟩ := r
    show (n • a) • b = n • (a • b)
    simp only [Algebra.smul_def, map_mul, _root_.mul_assoc, eq_intCast, map_intCast]⟩

theorem isPushout_torusRing :
    IsPushout (CommRingCat.ofHom (algebraMap ZU.{u} (AddMonoidAlgebra ZU.{u} X)))
      (CommRingCat.ofHom (algebraMap ZU.{u} K))
      (CommRingCat.ofHom (algebraMap (AddMonoidAlgebra ZU.{u} X) (AddMonoidAlgebra K X)))
      (CommRingCat.ofHom (algebraMap K (AddMonoidAlgebra K X))) := by
  first
  | exact CommRingCat.isPushout_of_isPushout ZU.{u} (AddMonoidAlgebra ZU.{u} X) K (AddMonoidAlgebra K X)
  | exact (CommRingCat.isPushout_iff_isPushout).2 inferInstance
  | (haveI := Algebra.IsPushout.symm
        (inferInstance : Algebra.IsPushout ZU.{u} K (AddMonoidAlgebra ZU.{u} X) (AddMonoidAlgebra K X))
     exact CommRingCat.isPushout_of_isPushout ZU.{u} (AddMonoidAlgebra ZU.{u} X) K (AddMonoidAlgebra K X))

theorem isPullback_torus :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap (AddMonoidAlgebra ZU.{u} X) (AddMonoidAlgebra K X))))
      (Spec.map (CommRingCat.ofHom (algebraMap K (AddMonoidAlgebra K X))))
      (splitTorusAff ZU X).hom (toZ (Spec (.of K))) := by
  rw [toZ_eq]
  first
  | exact isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_torusRing K X)
  | exact isPullback_Spec_map_isPushout _ _ _ _ (isPushout_torusRing K X)
  | exact (isPushout_torusRing K X).op.map Scheme.Spec
  | exact (isPushout_torusRing K X).op.flip.map Scheme.Spec

noncomputable def torusIso :
    Spec (.of (AddMonoidAlgebra K X)) ≅ (splitTorus (Spec (.of K)) X).left :=
  (isPullback_torus K X).isoPullback

theorem torusIso_hom_fst : (torusIso K X).hom ≫ torusFst (Spec (.of K)) X =
    Spec.map (CommRingCat.ofHom (algebraMap (AddMonoidAlgebra ZU.{u} X) (AddMonoidAlgebra K X))) := by
  first
  | exact (isPullback_torus K X).isoPullback_hom_fst
  | (simp [torusIso, torusFst]; done)

theorem torusIso_hom_hom : (torusIso K X).hom ≫ (splitTorus (Spec (.of K)) X).hom =
    Spec.map (CommRingCat.ofHom (algebraMap K (AddMonoidAlgebra K X))) := by
  first
  | exact (isPullback_torus K X).isoPullback_hom_snd
  | (simp [torusIso]; done)

noncomputable def torusGamma :
    Γ((splitTorus (Spec (.of K)) X).left, ⊤) ⟶ CommRingCat.of (AddMonoidAlgebra K X) :=
  (torusIso K X).hom.appTop ≫ (Scheme.ΓSpecIso _).hom

theorem torusGamma_bijective : Function.Bijective (torusGamma K X).hom := by
  have h1 := isIso_appTop_bij (torusIso K X)
  have h2 := cr_iso_bij (Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra K X)))
  first
  | exact h2.comp h1
  | (simp only [torusGamma, CommRingCat.hom_comp, RingHom.coe_comp]; exact h2.comp h1)

theorem coord_id_torusGamma :
    coord (𝟙 (splitTorus (Spec (.of K)) X)) ≫ torusGamma K X =
      CommRingCat.ofHom (algebraMap (AddMonoidAlgebra ZU.{u} X) (AddMonoidAlgebra K X)) := by
  have key : (torusFst (Spec (.of K)) X).appTop ≫ (torusIso K X).hom.appTop =
      ((torusIso K X).hom ≫ torusFst (Spec (.of K)) X).appTop := (comp_appTop_lemma _ _).symm
  show (Scheme.ΓSpecIso _).inv ≫ (𝟙 _ ≫ torusFst (Spec (.of K)) X).appTop ≫
    (torusIso K X).hom.appTop ≫ (Scheme.ΓSpecIso _).hom = _
  rw [Category.id_comp, ← Category.assoc (torusFst (Spec (.of K)) X).appTop, key, torusIso_hom_fst,
    Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

theorem torusGamma_chi (a : X) : (torusGamma K X).hom (chi X a) = single a 1 := by
  have h := congrArg (fun φ => φ.hom (single a (1 : ULift.{u} ℤ))) (coord_id_torusGamma K X)
  refine h.trans ?_
  first
  | (simp; done)
  | rfl

theorem torusGamma_const (c : Γ(Spec (.of K), ⊤)) :
    (torusGamma K X).hom ((splitTorus (Spec (.of K)) X).hom.appTop.hom c) =
      single 0 ((Scheme.ΓSpecIso (.of K)).hom.hom c) := by
  have key : (splitTorus (Spec (.of K)) X).hom.appTop ≫ (torusIso K X).hom.appTop =
      ((torusIso K X).hom ≫ (splitTorus (Spec (.of K)) X).hom).appTop := (comp_appTop_lemma _ _).symm
  have e1 : (splitTorus (Spec (.of K)) X).hom.appTop ≫ torusGamma K X =
      (Scheme.ΓSpecIso (.of K)).hom ≫ CommRingCat.ofHom (algebraMap K (AddMonoidAlgebra K X)) := by
    rw [torusGamma, ← Category.assoc, key, torusIso_hom_hom, Scheme.ΓSpecIso_naturality]
  refine (congrArg (fun φ => φ.hom c) e1).trans ?_
  first
  | (simp; done)
  | (simp [AddMonoidAlgebra.coe_algebraMap]; done)

end

section
variable (K : Type u) [Field K] (X : Type u) [AddCommGroup X]

theorem torus_units [TwoUniqueSums X] {w : Γ((splitTorus (Spec (.of K)) X).left, ⊤)} (hw : IsUnit w) :
    ∃ (c : Γ(Spec (.of K), ⊤)) (a : X), IsUnit c ∧
      w = (splitTorus (Spec (.of K)) X).hom.appTop.hom c * chi X a := by
  obtain ⟨a, c, hc, he⟩ := isUnit_eq_single (hw.map (torusGamma K X).hom)
  refine ⟨(Scheme.ΓSpecIso (.of K)).inv.hom c, a, hc.map _, (torusGamma_bijective K X).1 ?_⟩
  rw [he, map_mul, torusGamma_const, torusGamma_chi, single_mul_single, zero_add, mul_one]
  have hinv : (Scheme.ΓSpecIso (.of K)).hom.hom ((Scheme.ΓSpecIso (.of K)).inv.hom c) = c := by
    first
    | exact congrArg (fun φ => φ.hom c) (Scheme.ΓSpecIso (.of K)).inv_hom_id
    | (simp; done)
  rw [hinv]

theorem torus_const_mul_chi {c₁ c₂ : Γ(Spec (.of K), ⊤)} (h1 : IsUnit c₁) {a : X}
    (h : (splitTorus (Spec (.of K)) X).hom.appTop.hom c₁ * chi X a =
      (splitTorus (Spec (.of K)) X).hom.appTop.hom c₂) : a = 0 := by
  have h' := congrArg (torusGamma K X).hom h
  rw [map_mul, torusGamma_const, torusGamma_chi, torusGamma_const, single_mul_single, zero_add,
    mul_one] at h'
  have hc : (Scheme.ΓSpecIso (.of K)).hom.hom c₁ ≠ 0 :=
    (h1.map (Scheme.ΓSpecIso (.of K)).hom.hom).ne_zero
  first
  | exact (((AddMonoidAlgebra.single_eq_single_iff _ _ _ _).1 h').resolve_right (fun h => hc h.1)).1
  | exact ((AddMonoidAlgebra.single_eq_single_iff.1 h').resolve_right (fun h => hc h.1)).1
  | (simp [AddMonoidAlgebra.single_eq_single_iff, hc] at h'; exact h'.1)
  | (simp [hc] at h'; exact h'.1)
  | (simp [hc] at h'; exact h')
  | (by_contra ha
     have h2 := congrArg (fun p => AddMonoidAlgebra.coeff p a) h'
     simp [Ne.symm ha] at h2
     exact hc h2)

theorem torus_const_injective :
    Function.Injective (splitTorus (Spec (.of K)) X).hom.appTop.hom := by
  intro c₁ c₂ h
  have h' := congrArg (torusGamma K X).hom h
  rw [torusGamma_const, torusGamma_const] at h'
  first
  | exact (cr_iso_bij (Scheme.ΓSpecIso (.of K))).1 (AddMonoidAlgebra.single_injective (0 : X) h')
  | exact (cr_iso_bij (Scheme.ΓSpecIso (.of K))).1 (by simpa using h')
  | exact (cr_iso_bij (Scheme.ΓSpecIso (.of K))).1 (AddMonoidAlgebra.single_inj.1 h')

theorem isPullback_torus2 :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        AddMonoidAlgebra K X →+* AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X)) ≫ (torusIso K X).hom)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        AddMonoidAlgebra K X →ₐ[K] AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X).toRingHom) ≫
          (torusIso K X).hom)
      (splitTorus (Spec (.of K)) X).hom (splitTorus (Spec (.of K)) X).hom := by
  have hp : IsPushout (CommRingCat.ofHom (algebraMap K (AddMonoidAlgebra K X)))
      (CommRingCat.ofHom (algebraMap K (AddMonoidAlgebra K X)))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        AddMonoidAlgebra K X →+* AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        AddMonoidAlgebra K X →ₐ[K] AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X).toRingHom) := by
    first
    | exact CommRingCat.isPushout_tensorProduct K (AddMonoidAlgebra K X) (AddMonoidAlgebra K X)
    | exact CommRingCat.isPushout_of_isPushout K (AddMonoidAlgebra K X) (AddMonoidAlgebra K X)
        (AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X)
  have h : IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        AddMonoidAlgebra K X →+* AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X)))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        AddMonoidAlgebra K X →ₐ[K] AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap K (AddMonoidAlgebra K X))))
      (Spec.map (CommRingCat.ofHom (algebraMap K (AddMonoidAlgebra K X)))) := by
    first
    | exact isPullback_SpecMap_of_isPushout _ _ _ _ hp
    | exact isPullback_Spec_map_isPushout _ _ _ _ hp
    | exact hp.op.map Scheme.Spec
    | exact hp.op.flip.map Scheme.Spec
  refine IsPullback.of_iso h (Iso.refl _) (torusIso K X) (torusIso K X) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp [torusIso_hom_hom]
  · simp [torusIso_hom_hom]

noncomputable def torus2Iso :
    Spec (.of (AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X)) ≅
      (splitTorus (Spec (.of K)) X ⊗ splitTorus (Spec (.of K)) X).left :=
  (isPullback_torus2 K X).isoPullback

theorem torus2Iso_hom_fst : (torus2Iso K X).hom ≫
    (fst (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        AddMonoidAlgebra K X →+* AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X)) ≫ (torusIso K X).hom := by
  first
  | exact (isPullback_torus2 K X).isoPullback_hom_fst
  | (simp [torus2Iso]; done)

theorem torus2Iso_hom_snd : (torus2Iso K X).hom ≫
    (snd (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        AddMonoidAlgebra K X →ₐ[K] AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X).toRingHom) ≫
          (torusIso K X).hom := by
  first
  | exact (isPullback_torus2 K X).isoPullback_hom_snd
  | (simp [torus2Iso]; done)

noncomputable def torus2Gamma :
    Γ((splitTorus (Spec (.of K)) X ⊗ splitTorus (Spec (.of K)) X).left, ⊤) ⟶
      CommRingCat.of (AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X) :=
  (torus2Iso K X).hom.appTop ≫ (Scheme.ΓSpecIso _).hom

theorem torus2Gamma_bijective : Function.Bijective (torus2Gamma K X).hom := by
  have h1 := isIso_appTop_bij (torus2Iso K X)
  have h2 := cr_iso_bij (Scheme.ΓSpecIso
    (CommRingCat.of (AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X)))
  first
  | exact h2.comp h1
  | (simp only [torus2Gamma, CommRingCat.hom_comp, RingHom.coe_comp]; exact h2.comp h1)

theorem torus2Gamma_fst (x : Γ((splitTorus (Spec (.of K)) X).left, ⊤)) :
    (torus2Gamma K X).hom
      ((fst (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left.appTop.hom x) =
      (torusGamma K X).hom x ⊗ₜ 1 := by
  have e1 : (fst (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left.appTop ≫
      torus2Gamma K X = torusGamma K X ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        AddMonoidAlgebra K X →+* AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X) := by
    rw [torus2Gamma, torusGamma, ← Category.assoc, ← comp_appTop_lemma, torus2Iso_hom_fst,
      comp_appTop_lemma]
    simp only [Category.assoc]
    rw [Scheme.ΓSpecIso_naturality]
  refine (congrArg (fun φ => φ.hom x) e1).trans ?_
  first
  | (simp; done)
  | rfl

theorem torus2Gamma_snd (x : Γ((splitTorus (Spec (.of K)) X).left, ⊤)) :
    (torus2Gamma K X).hom
      ((snd (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left.appTop.hom x) =
      1 ⊗ₜ (torusGamma K X).hom x := by
  have e1 : (snd (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left.appTop ≫
      torus2Gamma K X = torusGamma K X ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        AddMonoidAlgebra K X →ₐ[K] AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X).toRingHom := by
    rw [torus2Gamma, torusGamma, ← Category.assoc, ← comp_appTop_lemma, torus2Iso_hom_snd,
      comp_appTop_lemma]
    simp only [Category.assoc]
    rw [Scheme.ΓSpecIso_naturality]
  refine (congrArg (fun φ => φ.hom x) e1).trans ?_
  first
  | (simp; done)
  | rfl

theorem torus2_units [TwoUniqueSums X]
    {w : Γ((splitTorus (Spec (.of K)) X ⊗ splitTorus (Spec (.of K)) X).left, ⊤)} (hw : IsUnit w) :
    ∃ (c : Γ(Spec (.of K), ⊤)) (a b : X), IsUnit c ∧
      w = (fst (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left.appTop.hom
          ((splitTorus (Spec (.of K)) X).hom.appTop.hom c * chi X a) *
        (snd (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left.appTop.hom
          (chi X b) := by
  classical
  let L : (AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X) →ₐ[K] AddMonoidAlgebra K (X × X) :=
    Algebra.TensorProduct.lift (AddMonoidAlgebra.mapDomainAlgHom K K (AddMonoidHom.inl X X))
      (AddMonoidAlgebra.mapDomainAlgHom K K (AddMonoidHom.inr X X)) (fun _ _ => Commute.all _ _)
  let Mh : Multiplicative (X × X) →* (AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X) :=
    { toFun := fun z => single (Multiplicative.toAdd z).1 (1 : K) ⊗ₜ single (Multiplicative.toAdd z).2 (1 : K)
      map_one' := by
        simp only [toAdd_one, Prod.fst_zero, Prod.snd_zero]
        rw [← AddMonoidAlgebra.one_def, Algebra.TensorProduct.one_def]
      map_mul' := fun z z' => by
        simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, Algebra.TensorProduct.tmul_mul_tmul,
          AddMonoidAlgebra.single_mul_single, mul_one] }
  let M := AddMonoidAlgebra.lift K (AddMonoidAlgebra K X ⊗[K] AddMonoidAlgebra K X) (X × X) Mh
  have hML : M.comp L = AlgHom.id K _ := by
    ext x <;> simp [L, M, Mh, AddMonoidAlgebra.one_def]
  have hu : IsUnit ((torus2Gamma K X).hom w) := hw.map _
  obtain ⟨z, c, hc, hz⟩ := isUnit_eq_single (hu.map L)
  have htw : (torus2Gamma K X).hom w = c • (single z.1 (1 : K) ⊗ₜ single z.2 (1 : K)) := by
    have h1 : M (L ((torus2Gamma K X).hom w)) = (torus2Gamma K X).hom w := by
      rw [← AlgHom.comp_apply, hML]
      rfl
    rw [← h1, hz, AddMonoidAlgebra.lift_single]
    rfl
  refine ⟨(Scheme.ΓSpecIso (.of K)).inv.hom c, z.1, z.2, hc.map _, ?_⟩
  apply (torus2Gamma_bijective K X).1
  rw [htw, map_mul, torus2Gamma_fst, torus2Gamma_snd, map_mul, torusGamma_const, torusGamma_chi, torusGamma_chi,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, AddMonoidAlgebra.single_mul_single, zero_add, mul_one,
    TensorProduct.smul_tmul', AddMonoidAlgebra.smul_single', mul_one]
  congr 2
  simp

end

section
variable (K : Type u) [Field K] (X : Type u) [AddCommGroup X]

theorem torus_hom_coord [TwoUniqueSums X] {Y : Type u} [AddCommGroup Y]
    (g : splitTorus (Spec (.of K)) X ⟶ splitTorus (Spec (.of K)) Y) (y : Y) :
    ∃ (c : Γ(Spec (.of K), ⊤)) (a : X), IsUnit c ∧
      (coord g).hom (single y 1) = (splitTorus (Spec (.of K)) X).hom.appTop.hom c * chi X a := by
  exact torus_units K X ((isUnit_single_one (R := ULift.{u} ℤ) y).map (coord g).hom)

end
end Rosenlicht

open Rosenlicht in

theorem splitTorus_rigidity (K : Type u) [Field K] (X : Type u) [AddCommGroup X] [TwoUniqueSums X]
    (Y : Type u) [AddCommGroup Y]
    (f : splitTorus (Spec (.of K)) X ⊗ splitTorus (Spec (.of K)) X ⟶ splitTorus (Spec (.of K)) Y)
    (h1 : lift (𝟙 _) (toUnit _ ≫ η) ≫ f = toUnit _ ≫ η)
    (h2 : lift (toUnit _ ≫ η) (𝟙 _) ≫ f = toUnit _ ≫ η) :
    f = toUnit _ ≫ η := by
  apply coord_injective
  apply CommRingCat.hom_ext
  apply ringHom_ext_ZU
  intro y
  rw [coord_toUnit_comp]
  have capp : ∀ {A B C : CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) (t : A),
      (φ ≫ ψ).hom t = ψ.hom (φ.hom t) := fun _ _ _ => rfl
  have idapp : ∀ (Z : Over (Spec (.of K))) (g : Z ⟶ Z) (t : Γ(Z.left, ⊤)), g = 𝟙 Z →
      g.left.appTop.hom t = t := by
    rintro Z g t rfl
    first
    | rfl
    | (simp; done)
  have etachi : ∀ x : X, (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X).left.appTop.hom (chi X x) = (coord (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X)).hom (single x (1 : ULift.{u} ℤ)) := by
    intro x
    have h0 := congrArg (fun φ => φ.hom (single x (1 : ULift.{u} ℤ))) (coord_comp (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X) (𝟙 (splitTorus (Spec (.of K)) X)))
    simp only [Category.comp_id] at h0
    exact h0.symm
  have etaconst : ∀ t : Γ(Spec (.of K), ⊤), (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X).left.appTop.hom ((splitTorus (Spec (.of K)) X).hom.appTop.hom t) = t := by
    intro t
    rw [← appTop_comp_apply, Over.w, ← toUnit_left]
    exact idapp _ _ t (toUnit_unique _ _)
  have s1f : ∀ z, (lift (𝟙 (splitTorus (Spec (.of K)) X)) (toUnit (splitTorus (Spec (.of K)) X) ≫ (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X))).left.appTop.hom ((fst (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left.appTop.hom z) = z := by
    intro z
    rw [over_appTop_comp, lift_fst]
    exact idapp _ _ z rfl
  have s1s : ∀ z, (lift (𝟙 (splitTorus (Spec (.of K)) X)) (toUnit (splitTorus (Spec (.of K)) X) ≫ (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X))).left.appTop.hom ((snd (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left.appTop.hom z) =
      (splitTorus (Spec (.of K)) X).hom.appTop.hom ((η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X).left.appTop.hom z) := by
    intro z
    rw [over_appTop_comp, lift_snd, toUnit_comp_appTop]
  have s2f : ∀ z, (lift (toUnit (splitTorus (Spec (.of K)) X) ≫ (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X)) (𝟙 (splitTorus (Spec (.of K)) X))).left.appTop.hom ((fst (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left.appTop.hom z) =
      (splitTorus (Spec (.of K)) X).hom.appTop.hom ((η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X).left.appTop.hom z) := by
    intro z
    rw [over_appTop_comp, lift_fst, toUnit_comp_appTop]
  have s2s : ∀ z, (lift (toUnit (splitTorus (Spec (.of K)) X) ≫ (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X)) (𝟙 (splitTorus (Spec (.of K)) X))).left.appTop.hom ((snd (splitTorus (Spec (.of K)) X) (splitTorus (Spec (.of K)) X)).left.appTop.hom z) = z := by
    intro z
    rw [over_appTop_comp, lift_snd]
    exact idapp _ _ z rfl
  obtain ⟨c, a, b, hc, hw⟩ := torus2_units K X
    ((isUnit_single_one (R := ULift.{u} ℤ) y).map (coord f).hom)
  have k1 := congrArg (fun φ => (coord φ).hom (single y (1 : ULift.{u} ℤ))) h1
  have k2 := congrArg (fun φ => (coord φ).hom (single y (1 : ULift.{u} ℤ))) h2
  dsimp only at k1 k2
  rw [coord_toUnit_comp, coord_comp, capp, hw, map_mul (lift (𝟙 (splitTorus (Spec (.of K)) X)) (toUnit (splitTorus (Spec (.of K)) X) ≫ (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X))).left.appTop.hom, s1f, s1s, etachi] at k1
  rw [coord_toUnit_comp, coord_comp, capp, hw, map_mul (lift (toUnit (splitTorus (Spec (.of K)) X) ≫ (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X)) (𝟙 (splitTorus (Spec (.of K)) X))).left.appTop.hom, s2f, s2s,
    map_mul (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X).left.appTop.hom, etaconst, etachi] at k2
  have hea : IsUnit ((coord (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X)).hom (single a (1 : ULift.{u} ℤ)) : Γ(Spec (.of K), ⊤)) :=
    (isUnit_single_one (R := ULift.{u} ℤ) a).map (coord (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X)).hom
  have heb : IsUnit ((coord (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X)).hom (single b (1 : ULift.{u} ℤ)) : Γ(Spec (.of K), ⊤)) :=
    (isUnit_single_one (R := ULift.{u} ℤ) b).map (coord (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) X)).hom
  have ha : a = 0 := torus_const_mul_chi K X (c₂ := (coord (η : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus (Spec (.of K)) Y)).hom (single y (1 : ULift.{u} ℤ)))
    (hc.mul heb) (by rw [map_mul, ← k1]; ring)
  have hb : b = 0 := torus_const_mul_chi K X (hc.mul hea) k2
  subst ha
  subst hb
  simp only [chi_zero, mul_one, map_one, ← AddMonoidAlgebra.one_def] at k1
  have hce := torus_const_injective K X k1
  rw [hw]
  simp only [chi_zero, mul_one, map_one]
  rw [hce, ← appTop_comp_apply, Over.w]

end ReciprocityTheory.ChartRestriction.G.Semi
