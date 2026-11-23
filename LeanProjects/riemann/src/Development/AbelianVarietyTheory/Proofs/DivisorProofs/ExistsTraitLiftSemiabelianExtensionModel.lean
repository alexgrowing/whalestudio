import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZHAbove
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep.TraitLift

theorem exists_point_finite_ext {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f] [Surjective f]
    (K : Type) [Field K] (y : Sp K ⟶ Y) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (x : Sp L ⟶ X),
      x ≫ f = spMap (algebraMap K L) ≫ y := by
  let P := pullback f y
  haveI : Nonempty (Sp K) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨p, -⟩ := (pullback.snd f y).surjective (Classical.arbitrary (Sp K))
  obtain ⟨R, e, he, ⟨q, -⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (X := P) (x := p) (U := ⊤) trivial
  let g' : Spec R ⟶ Sp K := e ≫ pullback.snd f y
  haveI : LocallyOfFiniteType g' := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g'
  have hφf : φ.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hφ]
    infer_instance
  haveI : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨q⟩
  obtain ⟨I, hI⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  letI : Algebra K (R ⧸ I) := ((Ideal.Quotient.mk I).comp φ.hom).toAlgebra
  haveI hft : Algebra.FiniteType K (R ⧸ I) :=
    RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective) hφf
  refine ⟨R ⧸ I, inferInstance, inferInstance, finite_of_finite_type_of_isJacobsonRing _ _,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ e ≫ pullback.fst f y, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e]
  change _ ≫ g' ≫ y = _
  rw [← hφ, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem exists_lift_of_proper {X Y : Scheme.{0}} (f : X ⟶ Y) [IsProper f] [Surjective f]
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (hV : IsCN V) (y : Sp V ⟶ Y) :
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (j : V →+* V') (ξ : Sp V' ⟶ X),
      IsCN V' ∧ Function.Injective j ∧ IsLocalHom j ∧ ξ ≫ f = spMap j ≫ y := by
  haveI := hV.2.2.1
  haveI := hV.2.2.2
  obtain ⟨L, _, _, _, x, hx⟩ :=
    exists_point_finite_ext f (FractionRing V) (spMap (algebraMap V (FractionRing V)) ≫ y)
  obtain ⟨V', _, _, _, hc, _, _, _, hcomp, -, hinj, hloc, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension V (FractionRing V) L
  have hv : ValuativeCriterion f := by
    have h : IsProper f := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  have hsq : x ≫ f = spMap (algebraMap V' L) ≫ spMap (algebraMap V V') ≫ y := by
    rw [hx, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hcomp]
  let S : ValuativeCommSq f := { R := V', K := L, i₁ := x, i₂ := spMap (algebraMap V V') ≫ y, commSq := ⟨hsq⟩ }
  obtain ⟨l, -, hl⟩ := (hv S).some.default
  exact ⟨V', inferInstance, inferInstance, inferInstance, algebraMap V V', l,
    ⟨inferInstance, inferInstance, hc, charZero_of_injective_ringHom hinj⟩, hinj, hloc, hl⟩

theorem surjective_of_isHom_id {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M Y : RatModel o Ω} {f : Y.Z ⟶ M.Z}
    (hf : M.IsHom Y (AlgHom.id o Ω) f) [IsProper f] : Surjective f := by
  have h : Y.pt ≫ f = M.pt := by
    rw [hf]
    exact (congrArg (· ≫ M.pt) (Spec.map_id _)).trans (Category.id_comp _)
  haveI : IsDominant (Y.pt ≫ f) := h ▸ inferInstance
  haveI : IsDominant f := IsDominant.of_comp Y.pt f
  infer_instance

theorem exists_lift : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), IsLocalHom ev → IsCN V → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (_ : IsDiscreteValuationRing V') (j : V →+* V') (ξ : Sp V' ⟶ Y.Z), IsCN V' ∧ Function.Injective j ∧ IsLocalHom j ∧ ξ ≫ πY = spMap (j.comp ev) ≫ X₁.M.Z.fromSpecStalk z₁ := by
  intro g n F W Z i X₁ z₁ Y πY h V _ _ _ _ ev _ hV
  obtain ⟨U₀, EE, -, -, -, hf, hp⟩ := h
  haveI := surjective_of_isHom_id hf
  obtain ⟨V', _, _, _, j, ξ, h1, h2, h3, h4⟩ := exists_lift_of_proper πY V hV (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁)
  refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, j, ξ, h1, h2, h3, ?_⟩
  rw [h4, ← Category.assoc, ← Spec.map_comp]
  rfl

end GlobalTheory.Poinc.Sep.TraitLift
