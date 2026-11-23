import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.TorusInj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.Torus2GammaBijective

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct AlgebraMonoidAlgebra
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory
namespace TorusUnit

open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (torusFst ringHom_ext_ZU ringHom_uliftInt_ext)
open AddMonoidAlgebra (single)

section Ring

variable {A X : Type} [CommRing A] [AddCommGroup X]

def IsMultiplicative (u : AddMonoidAlgebra A X) : Prop :=
  AddMonoidAlgebra.mapDomainRingHom A ((AddMonoidHom.id X).prod (AddMonoidHom.id X)) u =
    AddMonoidAlgebra.mapDomainRingHom A (AddMonoidHom.inl X X) u *
      AddMonoidAlgebra.mapDomainRingHom A (AddMonoidHom.inr X X) u

lemma coeff_inl_mul_inr (u v : AddMonoidAlgebra A X) (x y : X) :
    (AddMonoidAlgebra.mapDomainRingHom A (AddMonoidHom.inl X X) u *
      AddMonoidAlgebra.mapDomainRingHom A (AddMonoidHom.inr X X) v).coeff (x, y) =
      u.coeff x * v.coeff y := by
  classical
  induction u using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, add_mul]; simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ha, hb, add_mul]
  | single a r =>
    induction v using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add c d hc hd => rw [map_add, mul_add]; simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hc, hd, mul_add]
    | single b s =>
      simp only [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single,
        AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      by_cases h1 : a = x <;> by_cases h2 : b = y <;> simp [h1, h2]

lemma coeff_diag (u : AddMonoidAlgebra A X) (x y : X) [Decidable (x = y)] :
    (AddMonoidAlgebra.mapDomainRingHom A ((AddMonoidHom.id X).prod (AddMonoidHom.id X)) u).coeff
      (x, y) = if x = y then u.coeff x else 0 := by
  classical
  induction u using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add]; simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, ha, hb]
    split_ifs <;> simp
  | single a r =>
    simp only [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases h1 : a = x <;> by_cases h2 : x = y <;> simp [h1, h2]
    all_goals aesop

lemma IsMultiplicative.eq_single {u : AddMonoidAlgebra A X} (hu : IsMultiplicative u) {x : X}
    (hx : IsUnit (u.coeff x)) : u = single x 1 := by
  classical
  have key : ∀ y, (if x = y then u.coeff x else 0) = u.coeff x * u.coeff y := fun y => by
    rw [← coeff_diag, ← coeff_inl_mul_inr, hu]
  ext y
  have := key y
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  apply hx.mul_left_cancel
  rw [← this]
  split_ifs <;> simp

lemma exists_coeff_notMem {u : AddMonoidAlgebra A X} (hu : IsUnit u) (p : Ideal A) (hp : p ≠ ⊤) :
    ∃ x, u.coeff x ∉ p := by
  by_contra h
  push Not at h
  have : Nontrivial (A ⧸ p) := Ideal.Quotient.nontrivial_iff.2 hp
  apply (hu.map (AddMonoidAlgebra.mapRingHom X (Ideal.Quotient.mk p))).ne_zero
  ext x
  simp [Ideal.Quotient.eq_zero_iff_mem, h]

lemma eq_of_single_one_eq [Nontrivial A] {x y : X}
    (h : (single x 1 : AddMonoidAlgebra A X) = single y 1) : x = y := by
  by_contra hxy
  have := congrArg (fun p => p.coeff x) h
  simp [Ne.symm hxy] at this

end Ring

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

def torusPoint {R : CommRingCat.{0}} (φ : torusRing ZU X ⟶ R) (s : Spec R ⟶ S) :
    Over.mk s ⟶ splitTorus S X :=
  Over.homMk (pullback.lift (Spec.map φ) s (specULiftZIsTerminal.hom_ext _ _))
    (pullback.lift_snd _ _ _)

lemma torusPoint_fst {R : CommRingCat.{0}} (φ : torusRing ZU X ⟶ R) (s : Spec R ⟶ S) :
    (torusPoint φ s).left ≫ torusFst S X = Spec.map φ :=
  pullback.lift_fst _ _ _

lemma torus_hom_ext {Z : Over S} {g g' : Z ⟶ splitTorus S X}
    (h : g.left ≫ torusFst S X = g'.left ≫ torusFst S X) : g = g' := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact h
  · exact (Over.w g).trans (Over.w g').symm

lemma pullback_map_fst {A B : Over (Spec ZU.{0})} (f : A ⟶ B) :
    ((Over.pullback (toZ S)).map f).left ≫ pullback.fst B.hom (toZ S) =
      pullback.fst A.hom (toZ S) ≫ f.left := by
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

set_option backward.isDefEq.respectTransparency false in
lemma torusPoint_mul {R : CommRingCat.{0}} (φ φ' ψ : torusRing ZU X ⟶ R) (s : Spec R ⟶ S)
    (h : ∀ x : X, ψ.hom (single x 1) = φ.hom (single x 1) * φ'.hom (single x 1)) :
    torusPoint φ s * torusPoint φ' s = torusPoint ψ s := by
  letI : Algebra ZU.{0} R := ULift.algebra' ℤ R
  apply torus_hom_ext
  let a : torusRing ZU X →ₐ[ZU.{0}] R :=
    { φ.hom with commutes' := fun r => RingHom.congr_fun (ringHom_uliftInt_ext (φ.hom.comp (algebraMap ZU.{0} (torusRing ZU X))) (algebraMap ZU.{0} R)) r }
  let a' : torusRing ZU X →ₐ[ZU.{0}] R :=
    { φ'.hom with commutes' := fun r => RingHom.congr_fun (ringHom_uliftInt_ext (φ'.hom.comp (algebraMap ZU.{0} (torusRing ZU X))) (algebraMap ZU.{0} R)) r }
  let m : torusRing ZU X ⊗[ZU.{0}] torusRing ZU X →ₐ[ZU.{0}] R :=
    Algebra.TensorProduct.lift a a' (fun _ _ => Commute.all _ _)
  have e1 : (lift (torusPoint φ s) (torusPoint φ' s) ≫
      Functor.LaxMonoidal.μ (Over.pullback (toZ S)) (splitTorusAff ZU X) (splitTorusAff ZU X)).left ≫
      pullback.fst (splitTorusAff ZU X ⊗ splitTorusAff ZU X).hom (toZ S) =
      Spec.map (CommRingCat.ofHom m.toRingHom) ≫
        (pullbackSpecIso ZU.{0} (torusRing ZU X) (torusRing ZU X)).inv := by
    apply pullback.hom_ext
    · have := pullback_map_fst (S := S) (fst (splitTorusAff ZU X) (splitTorusAff ZU X))
      rw [Category.assoc]
      erw [← this]
      rw [← Category.assoc, ← Over.comp_left, Category.assoc, Functor.Monoidal.μ_fst]
      erw [lift_fst, torusPoint_fst, Category.assoc, pullbackSpecIso_inv_fst]
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      refine RingHom.ext fun x => ?_
      simp [m, a]
    · have := pullback_map_fst (S := S) (snd (splitTorusAff ZU X) (splitTorusAff ZU X))
      rw [Category.assoc]
      erw [← this]
      rw [← Category.assoc, ← Over.comp_left, Category.assoc, Functor.Monoidal.μ_snd]
      erw [lift_snd, torusPoint_fst, Category.assoc, pullbackSpecIso_inv_snd]
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      refine RingHom.ext fun x => ?_
      simp [m, a']
  have e2 : μ[splitTorus S X] = Functor.LaxMonoidal.μ (Over.pullback (toZ S)) (splitTorusAff ZU X) (splitTorusAff ZU X) ≫ (Over.pullback (toZ S)).map μ[splitTorusAff ZU X] := rfl
  rw [Hom.mul_def, e2, ← Category.assoc, Over.comp_left, Category.assoc, torusPoint_fst]
  erw [pullback_map_fst]
  rw [← Category.assoc]
  erw [e1]
  rw [mul_spec_asOver_spec_left, Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply ringHom_ext_ZU
  intro x
  rw [h]
  change m (Coalgebra.comul (R := ZU.{0}) (single x (1 : ZU.{0}) : AddMonoidAlgebra ZU.{0} X)) = _
  rw [AddMonoidAlgebra.comul_single]
  simp [m, a, a']

variable {Y : Over S}

def prodPoint {R : CommRingCat.{0}} (φ : torusRing ZU X ⟶ R) (y : Spec R ⟶ Y.left) :
    Spec R ⟶ (splitTorus S X ⊗ Y).left :=
  (lift (torusPoint φ (y ≫ Y.hom)) (Over.homMk y rfl : Over.mk (y ≫ Y.hom) ⟶ Y)).left

lemma prodPoint_fst {R : CommRingCat.{0}} (φ : torusRing ZU X ⟶ R) (y : Spec R ⟶ Y.left) :
    prodPoint φ y ≫ (fst (splitTorus S X) Y).left ≫ torusFst S X = Spec.map φ := by
  have := congrArg (fun f => f.left ≫ torusFst S X)
    (lift_fst (torusPoint φ (y ≫ Y.hom)) (Over.homMk y rfl : Over.mk (y ≫ Y.hom) ⟶ Y))
  simp only [Over.comp_left, Category.assoc, torusPoint_fst] at this
  exact this

lemma prodPoint_snd {R : CommRingCat.{0}} (φ : torusRing ZU X ⟶ R) (y : Spec R ⟶ Y.left) :
    prodPoint φ y ≫ (snd (splitTorus S X) Y).left = y :=
  congrArg (fun f => f.left)
    (lift_snd (torusPoint φ (y ≫ Y.hom)) (Over.homMk y rfl : Over.mk (y ≫ Y.hom) ⟶ Y))

variable (X Y) in
lemma isPullback_prod :
    IsPullback ((fst (splitTorus S X) Y).left ≫ torusFst S X) (snd (splitTorus S X) Y).left
      (splitTorusAff ZU X).hom (Y.hom ≫ toZ S) := by
  have h1 : IsPullback (fst (splitTorus S X) Y).left (snd (splitTorus S X) Y).left
      (splitTorus S X).hom Y.hom := IsPullback.of_hasPullback _ _
  have h2 : IsPullback (torusFst S X) (splitTorus S X).hom (splitTorusAff ZU X).hom (toZ S) :=
    IsPullback.of_hasPullback _ _
  exact h1.paste_horiz h2

lemma map_prodPoint {R R' : CommRingCat.{0}} (g : R ⟶ R') (φ : torusRing ZU X ⟶ R)
    (y : Spec R ⟶ Y.left) :
    Spec.map g ≫ prodPoint φ y = prodPoint (φ ≫ g) (Spec.map g ≫ y) := by
  apply (isPullback_prod X Y).hom_ext
  · rw [Category.assoc, prodPoint_fst, prodPoint_fst, Spec.map_comp]
  · rw [Category.assoc, prodPoint_snd, prodPoint_snd]

def value {R : CommRingCat.{0}} (φ : torusRing ZU X ⟶ R) (y : Spec R ⟶ Y.left) :
    Γ((splitTorus S X ⊗ Y).left, ⊤) ⟶ R :=
  (prodPoint φ y).appTop ≫ (Scheme.ΓSpecIso R).hom

lemma value_comp {R R' : CommRingCat.{0}} (g : R ⟶ R') (φ : torusRing ZU X ⟶ R)
    (y : Spec R ⟶ Y.left) : value φ y ≫ g = value (φ ≫ g) (Spec.map g ≫ y) := by
  rw [value, value, ← map_prodPoint, Scheme.Hom.comp_appTop, Category.assoc, Category.assoc,
    Scheme.ΓSpecIso_naturality]

lemma charUnit_val (χ : X) : (charUnit S X χ).val = (torusFst S X).appTop.hom
      ((Scheme.ΓSpecIso (torusRing ZU X)).inv.hom (single χ 1)) := by
  rw [TorusInj.charUnit_val, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

lemma value_char {R : CommRingCat.{0}} (φ : torusRing ZU X ⟶ R) (y : Spec R ⟶ Y.left) (χ : X) :
    (value φ y).hom ((fst (splitTorus S X) Y).left.appTop.hom (charUnit S X χ).val) =
      φ.hom (single χ 1) := by
  have : (Scheme.ΓSpecIso (torusRing ZU X)).inv ≫ (torusFst S X).appTop ≫
      (fst (splitTorus S X) Y).left.appTop ≫ value φ y = φ := by
    rw [value, ← Scheme.Hom.comp_appTop_assoc, ← Scheme.Hom.comp_appTop_assoc,
      prodPoint_fst, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rw [charUnit_val]
  exact congrArg (fun f => f.hom (single χ 1)) this

def IsMulLeft (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)) : Prop :=
  ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
    (lift (t * t') y).left.appTop.hom ρ =
      (lift t y).left.appTop.hom ρ * (lift t' y).left.appTop.hom ρ

lemma IsMulLeft.value_mul {ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)} (hρ : IsMulLeft ρ)
    {R : CommRingCat.{0}} (φ φ' ψ : torusRing ZU X ⟶ R) (y : Spec R ⟶ Y.left)
    (h : ∀ x : X, ψ.hom (single x 1) = φ.hom (single x 1) * φ'.hom (single x 1)) :
    (value ψ y).hom ρ = (value φ y).hom ρ * (value φ' y).hom ρ := by
  have := hρ (Over.mk (y ≫ Y.hom)) (torusPoint φ _) (torusPoint φ' _) (Over.homMk y rfl)
  rw [torusPoint_mul φ φ' ψ _ h] at this
  have h2 := congrArg (Scheme.ΓSpecIso R).hom.hom this
  rw [map_mul] at h2
  exact h2

attribute [local instance] TorusInj.zuAlg

variable (X) in

abbrev grpAlg (R : CommRingCat.{0}) : CommRingCat.{0} := CommRingCat.of (AddMonoidAlgebra R X)

variable (X) in

def fromInt (R : CommRingCat.{0}) : torusRing ZU X ⟶ grpAlg X R :=
  CommRingCat.ofHom (algebraMap (AddMonoidAlgebra ZU.{0} X) (AddMonoidAlgebra R X))

variable (X) in

def const (R : CommRingCat.{0}) : R ⟶ grpAlg X R :=
  CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))

lemma fromInt_single (R : CommRingCat.{0}) (x : X) :
    (fromInt X R).hom (single x 1) = single x 1 := by
  simp [fromInt]

def expand {R : CommRingCat.{0}} (y : Spec R ⟶ Y.left) :
    Γ((splitTorus S X ⊗ Y).left, ⊤) ⟶ grpAlg X R :=
  value (fromInt X R) (Spec.map (const X R) ≫ y)

lemma expand_char {R : CommRingCat.{0}} (y : Spec R ⟶ Y.left) (χ : X) :
    (expand y).hom ((fst (splitTorus S X) Y).left.appTop.hom (charUnit S X χ).val) =
      single χ 1 := by
  rw [expand, value_char, fromInt_single]

lemma expand_map {R R' : CommRingCat.{0}} (g : R ⟶ R') (y : Spec R ⟶ Y.left)
    (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)) :
    (expand (Spec.map g ≫ y)).hom ρ = AddMonoidAlgebra.mapRingHom X g.hom ((expand y).hom ρ) := by
  have h := value_comp (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom X g.hom) :
    grpAlg X R ⟶ grpAlg X R') (fromInt X R) (Spec.map (const X R) ≫ y)
  have h1 : fromInt X R ≫ (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom X g.hom) :
      grpAlg X R ⟶ grpAlg X R') = fromInt X R' := by
    apply CommRingCat.hom_ext
    apply ringHom_ext_ZU
    intro x
    rw [CommRingCat.hom_comp, RingHom.comp_apply, fromInt_single, fromInt_single]
    simp
  have h2 : const X R ≫ (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom X g.hom) :
      grpAlg X R ⟶ grpAlg X R') = g ≫ const X R' := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun r => ?_
    simp [const]
  rw [h1, ← Spec.map_comp_assoc, h2, Spec.map_comp, Category.assoc] at h
  exact (congrArg (fun f => f.hom ρ) h).symm

lemma IsMulLeft.isMultiplicative {ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)} (hρ : IsMulLeft ρ)
    {R : CommRingCat.{0}} (y : Spec R ⟶ Y.left) : IsMultiplicative ((expand y).hom ρ) := by
  let m (f : X →+ X × X) : grpAlg X R ⟶ grpAlg (X × X) R :=
    CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom R f)
  have key (f : X →+ X × X) : AddMonoidAlgebra.mapDomainRingHom R f ((expand y).hom ρ) =
      (value (fromInt X R ≫ m f) (Spec.map (const (X × X) R) ≫ y)).hom ρ := by
    have h := value_comp (m f) (fromInt X R) (Spec.map (const X R) ≫ y)
    have h2 : const X R ≫ m f = const (X × X) R := by
      apply CommRingCat.hom_ext
      refine RingHom.ext fun r => ?_
      simp [const, m]
    rw [← Spec.map_comp_assoc, h2] at h
    exact congrArg (fun f => f.hom ρ) h
  rw [IsMultiplicative, key, key, key]
  apply hρ.value_mul
  intro x
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [fromInt_single]
  simp [m, AddMonoidAlgebra.single_mul_single]

lemma isPushout_grpAlg (A : Type) [CommRing A] :
    IsPushout (CommRingCat.ofHom (algebraMap ZU.{0} (AddMonoidAlgebra ZU.{0} X)))
      (CommRingCat.ofHom (algebraMap ZU.{0} A))
      (CommRingCat.ofHom (algebraMap (AddMonoidAlgebra ZU.{0} X) (AddMonoidAlgebra A X)))
      (CommRingCat.ofHom (algebraMap A (AddMonoidAlgebra A X))) := by
  have : IsScalarTower ZU.{0} (AddMonoidAlgebra ZU.{0} X) (AddMonoidAlgebra A X) :=
    ⟨fun r a b => by
      obtain ⟨n⟩ := r
      show (n • a) • b = n • (a • b)
      simp only [Algebra.smul_def, map_mul, _root_.mul_assoc, eq_intCast, map_intCast]⟩
  have : Algebra.IsPushout ZU.{0} (AddMonoidAlgebra ZU.{0} X) A (AddMonoidAlgebra A X) :=
    AddMonoidAlgebra.instIsPushout'
  exact CommRingCat.isPushout_of_isPushout ZU.{0} (AddMonoidAlgebra ZU.{0} X) A
    (AddMonoidAlgebra A X)

lemma isPullback_expand {R : CommRingCat.{0}} (y : Spec R ⟶ Y.left) :
    IsPullback (prodPoint (fromInt X R) (Spec.map (const X R) ≫ y)) (Spec.map (const X R))
      (snd (splitTorus S X) Y).left y := by
  have h0 : IsPushout (CommRingCat.ofHom (algebraMap ZU.{0} (AddMonoidAlgebra ZU.{0} X)))
      (CommRingCat.ofHom (algebraMap ZU.{0} R)) (fromInt X R) (const X R) :=
    isPushout_grpAlg R
  have h1 := isPullback_SpecMap_of_isPushout _ _ _ _ h0
  refine IsPullback.of_right ?_ (prodPoint_snd _ _) (isPullback_prod X Y)
  rw [prodPoint_fst]
  rw [show y ≫ Y.hom ≫ toZ S = Spec.map (CommRingCat.ofHom (algebraMap ZU.{0} R)) from
    specULiftZIsTerminal.hom_ext _ _]
  exact h1

lemma ext_of_expand {f g : Γ((splitTorus S X ⊗ Y).left, ⊤)}
    (h : ∀ p : Y.left, ∃ (R : CommRingCat.{0}) (y : Spec R ⟶ Y.left), IsOpenImmersion y ∧
      p ∈ Set.range y ∧ (expand y).hom f = (expand y).hom g) : f = g := by
  choose R y hy hp he using h
  refine Scheme.OpenCover.ext_elem f g (Scheme.Cover.mkOfCovers Y.left
    (fun p => Spec (grpAlg X (R p)))
    (fun p => prodPoint (fromInt X (R p)) (Spec.map (const X (R p)) ≫ y p)) (fun q => ?_)
    (fun p => ?_)) (fun p => ?_)
  · obtain ⟨r, hr⟩ := hp ((snd (splitTorus S X) Y).left q)
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback
      (isPullback_expand (X := X) (y ((snd (splitTorus S X) Y).left q))) q r hr.symm
    exact ⟨_, z, hz⟩
  · exact MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (isPullback_expand (X := X) (y p)).flip (hy p)
  · exact (Scheme.ΓSpecIso (grpAlg X (R p))).commRingCatIsoToRingEquiv.injective (he p)

def IsCharNear (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)) (χ : X) (p : Y.left) : Prop :=
  ∃ (R : CommRingCat.{0}) (y : Spec R ⟶ Y.left), IsOpenImmersion y ∧
    p ∈ Set.range y ∧ (expand y).hom ρ = single χ 1

lemma IsCharNear.residueField {ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)} {χ : X} {p : Y.left}
    (h : IsCharNear ρ χ p) : (expand (Y.left.fromSpecResidueField p)).hom ρ = single χ 1 := by
  obtain ⟨R, y, hy, hp, he⟩ := h
  have H : Set.range (Y.left.fromSpecResidueField p) ⊆ Set.range y := by
    rw [Scheme.range_fromSpecResidueField]; simpa using hp
  rw [← IsOpenImmersion.lift_fac y _ H, ← Spec.map_preimage (IsOpenImmersion.lift y _ H),
    expand_map, he]
  simp

lemma IsCharNear.unique {ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)} {χ χ' : X} {p : Y.left}
    (h : IsCharNear ρ χ p) (h' : IsCharNear ρ χ' p) : χ = χ' :=
  eq_of_single_one_eq (h.residueField.symm.trans h'.residueField)

lemma IsMulLeft.exists_isCharNear {ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)} (hρ : IsMulLeft ρ)
    (hu : IsUnit ρ) (p : Y.left) : ∃ χ, IsCharNear ρ χ p := by
  obtain ⟨R, y, hy, q, hq⟩ : ∃ (R : CommRingCat.{0}) (y : Spec R ⟶ Y.left), IsOpenImmersion y ∧
      p ∈ Set.range y :=
    ⟨_, Y.left.affineOpenCover.f (Y.left.affineOpenCover.idx p), inferInstance,
      Y.left.affineOpenCover.covers p⟩
  obtain ⟨χ, hχ⟩ := exists_coeff_notMem (hu.map (expand y).hom) q.asIdeal q.2.ne_top
  set a := ((expand y).hom ρ).coeff χ with ha
  let g : R ⟶ CommRingCat.of (Localization.Away a) :=
    CommRingCat.ofHom (algebraMap R (Localization.Away a))
  refine ⟨χ, _, Spec.map g ≫ y, inferInstance, ?_, ?_⟩
  · have := PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
    obtain ⟨r, hr⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away a))) := by
      rw [this]; exact hχ
    refine ⟨r, ?_⟩
    rw [← hq, ← hr]
    exact Scheme.Hom.comp_apply _ _ _
  · apply (hρ.isMultiplicative _).eq_single
    rw [expand_map, AddMonoidAlgebra.coeff_mapRingHom]
    exact IsLocalization.Away.algebraMap_isUnit a

end TorusUnit

open TorusUnit in

theorem existsUnique_character_of_mul (S : Scheme.{0}) (X : Type) [AddCommGroup X] (Y : Over S)
    [ConnectedSpace Y.left] (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ)
    (hρ : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y),
      (lift (t * t') y).left.appTop.hom ρ.val =
        (lift t y).left.appTop.hom ρ.val * (lift t' y).left.appTop.hom ρ.val) :
    ∃! χ : X, ρ.val = (fst (splitTorus S X) Y).left.appTop.hom (charUnit S X χ).val := by
  choose c hc using IsMulLeft.exists_isCharNear (ρ := ρ.val) hρ ρ.isUnit
  have hlc : IsLocallyConstant c := by
    rw [IsLocallyConstant.iff_exists_open]
    intro p
    obtain ⟨R, y, hy, hp, he⟩ := hc p
    exact ⟨Set.range y, y.isOpenEmbedding.isOpen_range, hp,
      fun p' hp' => (hc p').unique ⟨R, y, hy, hp', he⟩⟩
  obtain ⟨p₀⟩ : Nonempty Y.left := inferInstance
  refine ⟨c p₀, ext_of_expand fun p => ?_, fun χ hχ => ?_⟩
  · obtain ⟨R, y, hy, hp, he⟩ := hc p
    refine ⟨R, y, hy, hp, ?_⟩
    rw [he, expand_char, hlc.apply_eq_of_preconnectedSpace p p₀]
  · have := (hc p₀).residueField
    rw [hχ, expand_char] at this
    exact eq_of_single_one_eq this

end GlobalTheory
