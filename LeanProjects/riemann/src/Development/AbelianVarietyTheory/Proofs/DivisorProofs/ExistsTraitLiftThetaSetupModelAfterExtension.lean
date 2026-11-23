import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc.TraitLift

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [← Spec.map_comp]; rfl

theorem mem_of_closedPoint {Y : Scheme.{0}} (U : Set Y) (hU : IsOpen U) (V : Type) [CommRing V] [IsLocalRing V]
    (ξ : Sp V ⟶ Y) (h : ξ (closedPoint V) ∈ U) (x : Sp V) : ξ x ∈ U := by
  have hs : x ⤳ closedPoint V := IsLocalRing.specializes_closedPoint x
  exact (hs.map ξ.continuous).mem_open hU h

theorem exists_finite_point {X Y : Scheme.{0}} (π : X ⟶ Y) [IsFinite π] (K : Type) [Field K] (x : Sp K ⟶ Y)
    (hx : x (closedPoint K) ∈ Set.range π) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (η : Sp L ⟶ X),
      η ≫ π = spMap (algebraMap K L) ≫ x := by
  obtain ⟨p, hp⟩ := hx
  haveI : IsAffine (pullback π x) := isAffine_of_isAffineHom (pullback.snd π x)
  obtain ⟨S, e, -⟩ : ∃ (S : CommRingCat.{0}) (_ : Spec S ≅ pullback π x), True :=
    ⟨_, (pullback π x).isoSpec.symm, trivial⟩
  obtain ⟨f, hf⟩ := Spec.map_surjective (R := CommRingCat.of K) (S := S) (e.hom ≫ pullback.snd π x)
  letI : Algebra K S := f.hom.toAlgebra
  have hsp : spMap (algebraMap K S) = e.hom ≫ pullback.snd π x := hf
  have hfin : Module.Finite K S := by
    have h1 : IsFinite (Spec.map f) := by rw [hf]; infer_instance
    exact (IsFinite.SpecMap_iff f).1 h1
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x) p (closedPoint K) hp
  haveI : Nontrivial S := (e.inv z).nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  letI : Field (S ⧸ m) := Ideal.Quotient.field m
  haveI : FiniteDimensional K (S ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap Ideal.Quotient.mk_surjective
  refine ⟨S ⧸ m, inferInstance, inferInstance, inferInstance, spMap (Ideal.Quotient.mk m) ≫ e.hom ≫ pullback.fst π x, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e.hom, ← hsp, ← Category.assoc, spMap_comp']

theorem exists_lift_of_isFinite {X Y : Scheme.{0}} (π : X ⟶ Y) [IsFinite π] (R : Type) [CommRing R] [IsDomain R]
    [ValuationRing R] (η : Sp (FractionRing R) ⟶ X) (ξ : Sp R ⟶ Y) (h : η ≫ π = jK R ≫ ξ) :
    ∃ l : Sp R ⟶ X, l ≫ π = ξ ∧ jK R ≫ l = η := by
  have hUC : UniversallyClosed π := inferInstance
  have h2 : (ValuativeCriterion.Existence ⊓ @QuasiCompact) π := by
    rw [← UniversallyClosed.eq_valuativeCriterion]; exact hUC
  let S : ValuativeCommSq π :=
    { R := R, K := FractionRing R, i₁ := η, i₂ := ξ, commSq := ⟨h⟩ }
  obtain ⟨l⟩ := (h2.1 S).exists_lift
  exact ⟨l.l, l.fac_right, l.fac_left⟩

end GlobalTheory.Poinc.TraitLift

namespace GlobalTheory.Poinc.TraitLift

theorem exists_closure (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    [IsAdicComplete (maximalIdeal V) V] (L : Type) [Field L] [Algebra (FractionRing V) L]
    [FiniteDimensional (FractionRing V) L] :
    ∃ (V₂ : Type) (_ : CommRing V₂) (_ : IsDomain V₂) (_ : IsLocalRing V₂) (j : V →+* V₂) (e : L →+* FractionRing V₂),
      GlobalTheory.Mum.Base V₂ ∧ IsDiscreteValuationRing V₂ ∧ Function.Injective j ∧ IsLocalHom j ∧
        ∀ a : V, e (algebraMap (FractionRing V) L (algebraMap V (FractionRing V) a)) =
          algebraMap V₂ (FractionRing V₂) (j a) := by
  letI : Algebra V L := ((algebraMap (FractionRing V) L).comp (algebraMap V (FractionRing V))).toAlgebra
  haveI : IsScalarTower V (FractionRing V) L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Module.Finite V (integralClosure V L) := GlobalTheory.FormalIsogeny.finite_integralClosure V (FractionRing V) L
  haveI := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful V (FractionRing V) L
  haveI hloc : IsLocalRing (integralClosure V L) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalRing V L
  haveI hdvr : IsDiscreteValuationRing (integralClosure V L) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr V (FractionRing V) L
  haveI : IsFractionRing (integralClosure V L) L := integralClosure.isFractionRing_of_finite_extension (FractionRing V) L
  have hj := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_inj V L
  haveI : CharZero (integralClosure V L) := charZero_of_injective_algebraMap hj
  refine ⟨integralClosure V L, inferInstance, inferInstance, hloc, algebraMap V (integralClosure V L),
    (FractionRing.algEquiv (integralClosure V L) L).symm.toRingEquiv.toRingHom,
    ⟨⟨inferInstance, inferInstance, inferInstance,
      GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local V (integralClosure V L)⟩, inferInstance⟩,
    hdvr, hj, ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom V L, fun a => ?_⟩
  have h1 : algebraMap (FractionRing V) L (algebraMap V (FractionRing V) a) =
      algebraMap (integralClosure V L) L (algebraMap V (integralClosure V L) a) := rfl
  rw [h1]
  exact (FractionRing.algEquiv (integralClosure V L) L).symm.commutes _

end GlobalTheory.Poinc.TraitLift

namespace GlobalTheory.Poinc

open GlobalTheory.Poinc.TraitLift in

theorem exists_trait_lift_setup (hExt : TraitExtSt) : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i), IsClopen (Set.range X₁.π) → ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ Set.range X₁.π → ∃ (T' : Trait F) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V) (ξ₁ : Sp T'.V ⟶ X₁.M.Z), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) ∧ T'.y = spMap fK ≫ T.y ∧ spMap f ≫ ξ = ξ₁ ≫ X₁.π ∧ jK T'.V ≫ ξ₁ ≫ X₁.π = T'.y ≫ i := by
  intro g n F Z i W8 X₁ hcl T ξ hξ hc
  haveI : IsFinite X₁.π := X₁.fin
  have hgen : (jK T.V ≫ ξ) (closedPoint (FractionRing T.V)) ∈ Set.range X₁.π := by
    exact mem_of_closedPoint _ hcl.isOpen T.V ξ hc _
  obtain ⟨L, _, _, _, η, hη⟩ := exists_finite_point X₁.π (FractionRing T.V) (jK T.V ≫ ξ) hgen
  haveI := T.complete
  obtain ⟨V₂, _, _, _, j, e, hB, hD, hj, hjl, he⟩ := exists_closure T.V L
  have hring : (algebraMap V₂ (FractionRing V₂)).comp j =
      (e.comp (algebraMap (FractionRing T.V) L)).comp (algebraMap T.V (FractionRing T.V)) :=
    RingHom.ext fun a => (he a).symm
  haveI : ValuationRing V₂ := inferInstance
  have hsq : (spMap e ≫ η) ≫ X₁.π = jK V₂ ≫ (spMap j ≫ ξ) := by
    rw [Category.assoc, hη, ← Category.assoc, spMap_comp', ← Category.assoc, ← Category.assoc, spMap_comp',
      show jK V₂ = spMap (algebraMap V₂ (FractionRing V₂)) from rfl, spMap_comp', hring]
  obtain ⟨l, hl1, -⟩ := exists_lift_of_isFinite X₁.π V₂ (spMap e ≫ η) (spMap j ≫ ξ) hsq
  obtain ⟨T', f'', fK'', hinj'', hloc'', -, hc'', hy''⟩ := hExt g n _ (zetaAway n) F V₂ hB hD
    (spMap (e.comp (algebraMap (FractionRing T.V) L)) ≫ T.y)
  have hring2 : (algebraMap T'.V (FractionRing T'.V)).comp (f''.comp j) =
      (fK''.comp (e.comp (algebraMap (FractionRing T.V) L))).comp (algebraMap T.V (FractionRing T.V)) := by
    ext a
    simp only [RingHom.comp_apply]
    rw [← hc'', ← he]
  have key : jK T'.V ≫ spMap (f''.comp j) = spMap (fK''.comp (e.comp (algebraMap (FractionRing T.V) L))) ≫ jK T.V := by
    rw [show jK T'.V = spMap (algebraMap T'.V (FractionRing T'.V)) from rfl,
      show jK T.V = spMap (algebraMap T.V (FractionRing T.V)) from rfl, spMap_comp', spMap_comp', hring2]
  haveI := hloc''
  refine ⟨T', f''.comp j, fK''.comp (e.comp (algebraMap (FractionRing T.V) L)), spMap f'' ≫ l, hinj''.comp hj,
    inferInstance, fun a => (RingHom.congr_fun hring2 a).symm, ?_, ?_, ?_⟩
  · rw [hy'', ← Category.assoc, spMap_comp']
  · rw [Category.assoc, hl1, ← Category.assoc, spMap_comp']
  · calc jK T'.V ≫ (spMap f'' ≫ l) ≫ X₁.π = jK T'.V ≫ spMap (f''.comp j) ≫ ξ := by
          rw [Category.assoc, hl1, ← spMap_comp', Category.assoc]
      _ = spMap (fK''.comp (e.comp (algebraMap (FractionRing T.V) L))) ≫ jK T.V ≫ ξ := by
          rw [← Category.assoc, key, Category.assoc]
      _ = T'.y ≫ i := by
          rw [hξ, hy'', ← spMap_comp']
          simp only [Category.assoc]

end GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem traitLift_setup : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i), IsClopen (Set.range X₁.π) → ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ Set.range X₁.π → ∃ (T' : Trait F) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V) (ξ₁ : Sp T'.V ⟶ X₁.M.Z), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) ∧ T'.y = spMap fK ≫ T.y ∧ spMap f ≫ ξ = ξ₁ ≫ X₁.π ∧ jK T'.V ≫ ξ₁ ≫ X₁.π = T'.y ≫ i :=
  exists_trait_lift_setup GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR

end GlobalTheory.Poinc
