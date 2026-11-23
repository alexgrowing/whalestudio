import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealLocalization
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

theorem le_preimage_top (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) :
    U ≤ p ⁻¹ᵁ ⊤ := by
  intro _ _
  trivial

noncomputable def sectionsAlgebraMap (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) : k →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (le_preimage_top k p U)).hom

theorem sectionsAlgebraMap_eq (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) :
    sectionsAlgebraMap k p U =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (le_preimage_top k p U)).hom :=
  rfl

theorem sectionsAlgebraMap_comp_restrict (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) {U V : X.Opens} (h : V ≤ U) :
    (X.presheaf.map (homOfLE h).op).hom.comp (sectionsAlgebraMap k p U) =
      sectionsAlgebraMap k p V := by
  have key : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (le_preimage_top k p U)) ≫
      X.presheaf.map (homOfLE h).op =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ V (le_preimage_top k p V) := by
    rw [Category.assoc, Scheme.Hom.appLE_map]
  rw [sectionsAlgebraMap_eq k p U, sectionsAlgebraMap_eq k p V, ← CommRingCat.hom_comp, key]

theorem sectionsAlgebraMap_restrict_apply (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) {U V : X.Opens} (h : V ≤ U) (a : k) :
    (X.presheaf.map (homOfLE h).op).hom (sectionsAlgebraMap k p U a) =
      sectionsAlgebraMap k p V a :=
  DFunLike.congr_fun (sectionsAlgebraMap_comp_restrict k p h) a

@[reducible] noncomputable def sectionsAlgebra (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) : Algebra k Γ(X, U) :=
  (sectionsAlgebraMap k p U).toAlgebra

theorem algebraMap_sectionsAlgebra (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) :
    @algebraMap k Γ(X, U) _ _ (sectionsAlgebra k p U) = sectionsAlgebraMap k p U :=
  rfl

theorem isScalarTower_sections (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (f : Γ(X, U))
    [Algebra k Γ(X, U)] [Algebra k Γ(X, X.basicOpen f)]
    [Algebra Γ(X, U) Γ(X, X.basicOpen f)]
    (hU : algebraMap k Γ(X, U) = sectionsAlgebraMap k p U)
    (hV : algebraMap k Γ(X, X.basicOpen f) = sectionsAlgebraMap k p (X.basicOpen f))
    (hres : algebraMap Γ(X, U) Γ(X, X.basicOpen f) =
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom) :
    IsScalarTower k Γ(X, U) Γ(X, X.basicOpen f) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [hV, hres, hU, sectionsAlgebraMap_restrict_apply]

theorem finiteType_sections (k : Type u) [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (U : X.affineOpens)
    [Algebra k Γ(X, U.1)] (h : algebraMap k Γ(X, U.1) = sectionsAlgebraMap k p U.1) :
    Algebra.FiniteType k Γ(X, U.1) := by
  have hft : (p.appLE ⊤ U.1 (le_preimage_top k p U.1)).hom.FiniteType := by
    apply Scheme.Hom.finiteType_appLE p (isAffineOpen_top _) U.2
  have hcomp : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom = RingHom.id _ := by
    rw [← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id]
  have hsurj : Function.Surjective ⇑(Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom := fun y =>
    ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom y, DFunLike.congr_fun hcomp y⟩
  have hiso : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _ hsurj
  have hst : (sectionsAlgebraMap k p U.1).FiniteType := by
    rw [sectionsAlgebraMap_eq, CommRingCat.hom_comp]
    exact hft.comp hiso
  have hinst : ‹Algebra k Γ(X, U.1)› = (sectionsAlgebraMap k p U.1).toAlgebra :=
    Algebra.algebra_ext _ _ fun r => DFunLike.congr_fun h r
  rw [hinst]
  exact hst

theorem isNoetherianRing_sections (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (U : X.affineOpens)
    [Algebra k Γ(X, U.1)] (h : algebraMap k Γ(X, U.1) = sectionsAlgebraMap k p U.1) :
    IsNoetherianRing Γ(X, U.1) := by
  have : Algebra.FiniteType k Γ(X, U.1) := finiteType_sections k p U h
  exact Algebra.FiniteType.isNoetherianRing k Γ(X, U.1)

theorem finitePresentation_kaehlerDifferential_sections (k : Type u) [CommRing k]
    [IsNoetherianRing k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] (U : X.affineOpens) [Algebra k Γ(X, U.1)]
    (h : algebraMap k Γ(X, U.1) = sectionsAlgebraMap k p U.1) :
    Module.FinitePresentation Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1)) := by
  have : Algebra.FiniteType k Γ(X, U.1) := finiteType_sections k p U h
  have : IsNoetherianRing Γ(X, U.1) := isNoetherianRing_sections k p U h
  have : Module.Finite Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1)) := inferInstance
  exact Module.finitePresentation_of_finite ..

private theorem derivIdealSheaf_map_ideal_basicOpen (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (I : X.IdealSheafData) :
    ∀ (U : X.affineOpens) (f : Γ(X, U.1)),
      Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
          (@derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U)) =
        @derivIdeal k _ _ _ (sectionsAlgebra k p (X.affineBasicOpen f).1)
          (I.ideal (X.affineBasicOpen f)) := by
  intro U f
  let algU : Algebra k Γ(X, U.1) := sectionsAlgebra k p U.1
  let algV : Algebra k Γ(X, X.basicOpen f) := sectionsAlgebra k p (X.basicOpen f)
  let algUV : Algebra Γ(X, U.1) Γ(X, X.basicOpen f) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  have htower : IsScalarTower k Γ(X, U.1) Γ(X, X.basicOpen f) :=
    isScalarTower_sections k p U.1 f rfl rfl rfl
  have hloc : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen f
  have hfp : Module.FinitePresentation Γ(X, U.1) (KaehlerDifferential k Γ(X, U.1)) :=
    finitePresentation_kaehlerDifferential_sections k p U rfl
  have hI : Ideal.map (algebraMap Γ(X, U.1) Γ(X, X.basicOpen f)) (I.ideal U) =
      I.ideal (X.affineBasicOpen f) := I.map_ideal_basicOpen U f
  have key := map_derivIdeal_away (k := k) (S' := Γ(X, X.basicOpen f)) f (I.ideal U)
  exact key.trans (congrArg (@derivIdeal k _ Γ(X, X.basicOpen f) _ algV) hI)

noncomputable def derivIdealSheaf (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData) :
    X.IdealSheafData where
  ideal U := @derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U)
  map_ideal_basicOpen := derivIdealSheaf_map_ideal_basicOpen k p I

@[simp] theorem derivIdealSheaf_ideal (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (U : X.affineOpens) :
    (derivIdealSheaf k p I).ideal U = @derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) :=
  rfl

theorem le_derivIdealSheaf (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData) :
    I ≤ derivIdealSheaf k p I := by
  have h : ∀ U : X.affineOpens, I.ideal U ≤ (derivIdealSheaf k p I).ideal U := by
    intro U
    exact @le_derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U)
  exact h

theorem derivIdealSheaf_mono (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] :
    Monotone (derivIdealSheaf k p) := by
  intro I J h
  have key : ∀ U : X.affineOpens,
      (derivIdealSheaf k p I).ideal U ≤ (derivIdealSheaf k p J).ideal U := by
    intro U
    have hU : I.ideal U ≤ J.ideal U := h U
    rw [derivIdealSheaf_ideal, derivIdealSheaf_ideal]
    exact @derivIdeal_le_derivIdeal k _ _ _ (sectionsAlgebra k p U.1) _ _ hU
  exact key

theorem derivIdealSheaf_mul_le (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I J : X.IdealSheafData) :
    derivIdealSheaf k p (I * J) ≤ I * derivIdealSheaf k p J ⊔ J * derivIdealSheaf k p I := by
  have h : ∀ U : X.affineOpens,
      (derivIdealSheaf k p (I * J)).ideal U ≤
        (I * derivIdealSheaf k p J ⊔ J * derivIdealSheaf k p I).ideal U := by
    intro U
    have hmul : ∀ A B : X.IdealSheafData, (A * B).ideal U = A.ideal U * B.ideal U := by
      intro A B
      simp [Scheme.IdealSheafData.ideal_mul]
    have key := @derivIdeal_mul_le k _ Γ(X, U.1) _ (sectionsAlgebra k p U.1)
      (I.ideal U) (J.ideal U)
    have h1 : (derivIdealSheaf k p (I * J)).ideal U =
        @derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U * J.ideal U) := by
      rw [derivIdealSheaf_ideal, hmul]
    have h2 : @derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) =
        (derivIdealSheaf k p I).ideal U := (derivIdealSheaf_ideal k p I U).symm
    have h3 : @derivIdeal k _ _ _ (sectionsAlgebra k p U.1) (J.ideal U) =
        (derivIdealSheaf k p J).ideal U := (derivIdealSheaf_ideal k p J U).symm
    rw [h1]
    refine key.trans (sup_le ?_ ?_)
    · rw [h3, ← hmul]
      exact Scheme.IdealSheafData.le_def.mp le_sup_left U
    · rw [h2, ← hmul]
      exact Scheme.IdealSheafData.le_def.mp le_sup_right U
  exact h

theorem derivIdealSheaf_pow_succ_le (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData) (n : ℕ) :
    derivIdealSheaf k p (I ^ (n + 1)) ≤ I ^ n * derivIdealSheaf k p I := by
  have key : ∀ U : X.affineOpens,
      (derivIdealSheaf k p (I ^ (n + 1))).ideal U ≤ (I ^ n * derivIdealSheaf k p I).ideal U := by
    intro U
    have hmul : ∀ A B : X.IdealSheafData, (A * B).ideal U = A.ideal U * B.ideal U := by
      intro A B
      simp [Scheme.IdealSheafData.ideal_mul]
    have hpow : ∀ m : ℕ, (I ^ m).ideal U = I.ideal U ^ m := fun m =>
      congrFun (Scheme.IdealSheafData.ideal_pow I m) U
    rw [hmul, derivIdealSheaf_ideal, derivIdealSheaf_ideal, hpow, hpow]
    exact @derivIdeal_pow_succ_le k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) n
  exact key

noncomputable def derivIdealSheafIterate (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] :
    ℕ → X.IdealSheafData → X.IdealSheafData
  | 0, I => I
  | (r + 1), I => derivIdealSheaf k p (derivIdealSheafIterate k p r I)

@[simp] theorem derivIdealSheafIterate_zero (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (I : X.IdealSheafData) : derivIdealSheafIterate k p 0 I = I :=
  rfl

theorem derivIdealSheafIterate_succ (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (r : ℕ) (I : X.IdealSheafData) :
    derivIdealSheafIterate k p (r + 1) I = derivIdealSheaf k p (derivIdealSheafIterate k p r I) :=
  rfl

theorem derivIdealSheafIterate_one (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData) :
    derivIdealSheafIterate k p 1 I = derivIdealSheaf k p I :=
  rfl

theorem derivIdealSheafIterate_add (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (r s : ℕ) (I : X.IdealSheafData) :
    derivIdealSheafIterate k p (r + s) I =
      derivIdealSheafIterate k p r (derivIdealSheafIterate k p s I) := by
  induction r with
  | zero => rw [Nat.zero_add, derivIdealSheafIterate_zero]
  | succ n ih =>
      rw [add_right_comm, derivIdealSheafIterate_succ, derivIdealSheafIterate_succ, ih]

@[simp] theorem derivIdealSheafIterate_ideal (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (r : ℕ)
    (I : X.IdealSheafData) (U : X.affineOpens) :
    (derivIdealSheafIterate k p r I).ideal U =
      @derivIdealIterate k _ _ _ (sectionsAlgebra k p U.1) r (I.ideal U) := by
  induction r with
  | zero =>
      rw [derivIdealSheafIterate_zero,
        @derivIdealIterate_zero k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U)]
  | succ n ih =>
      rw [derivIdealSheafIterate_succ, derivIdealSheaf_ideal, ih,
        @derivIdealIterate_succ k _ _ _ (sectionsAlgebra k p U.1) n (I.ideal U)]

theorem le_derivIdealSheafIterate (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (r : ℕ) (I : X.IdealSheafData) :
    I ≤ derivIdealSheafIterate k p r I := by
  induction r with
  | zero => exact le_rfl
  | succ n ih =>
    rw [derivIdealSheafIterate_succ]
    exact le_trans ih (le_derivIdealSheaf k p (derivIdealSheafIterate k p n I))

end FunctorialResolution.EmbeddedResolution
