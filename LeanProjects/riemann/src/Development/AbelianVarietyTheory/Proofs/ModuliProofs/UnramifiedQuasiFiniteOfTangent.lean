import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.TangentCriterion

noncomputable def dualOfDerivation {A B K : Type} [CommRing A] [CommRing B] [Field K] [Algebra A B]
    [Algebra B K] [Algebra A K] (D : Derivation A B K) : B →+* DualNumber K where
  toFun b := TrivSqZeroExt.inl (algebraMap B K b) + TrivSqZeroExt.inr (D b)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
        DualNumber.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
        add_zero, Derivation.leibniz, Algebra.smul_def]
      ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

theorem formallyUnramified_of_tangent {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B]
    (h : ∀ (K : Type) [Field K] (g : B →+* DualNumber K),
      g.comp (algebraMap A B) = (((algebraMap K (DualNumber K)).comp
        (TrivSqZeroExt.fstHom K K K).toRingHom).comp g).comp (algebraMap A B) →
      g = ((algebraMap K (DualNumber K)).comp (TrivSqZeroExt.fstHom K K K).toRingHom).comp g) :
    Algebra.FormallyUnramified A B := by
  refine ⟨?_⟩
  by_contra hn
  rw [not_subsingleton_iff_nontrivial] at hn
  obtain ⟨N, hN, -⟩ : ∃ N : Submodule B Ω[B⁄A], IsCoatom N ∧ ⊥ ≤ N :=
    (eq_top_or_exists_le_coatom (⊥ : Submodule B Ω[B⁄A])).resolve_left bot_ne_top
  have hs : IsSimpleModule B (Ω[B⁄A] ⧸ N) := isSimpleModule_iff_isCoatom.mpr hN
  obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
  letI := Ideal.Quotient.field m
  let φ : Ω[B⁄A] →ₗ[B] (B ⧸ m) := e.toLinearMap ∘ₗ N.mkQ
  let D : Derivation A B (B ⧸ m) := φ.compDer (KaehlerDifferential.D A B)
  have hD := h (B ⧸ m) (dualOfDerivation D) (by
    ext a <;> simp [dualOfDerivation, TrivSqZeroExt.algebraMap_eq_inl])
  have h0 : ∀ b, φ (KaehlerDifferential.D A B b) = 0 := fun b => by
    have := congrArg TrivSqZeroExt.snd (RingHom.congr_fun hD b)
    simpa [dualOfDerivation, TrivSqZeroExt.algebraMap_eq_inl, D] using this
  have hφ : φ = 0 := by
    apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation A B)
    rintro _ ⟨b, rfl⟩
    exact h0 b
  have hsurj : Function.Surjective φ := e.surjective.comp N.mkQ_surjective
  obtain ⟨w, hw⟩ := hsurj 1
  rw [hφ] at hw
  exact zero_ne_one hw

theorem unramified_quasiFinite_of_tangent : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y), LocallyOfFiniteType f → (∀ (K : Type) [Field K] (x : Sp (DualNumber K) ⟶ X), x ≫ f = constPt x ≫ f → x = constPt x) → FormallyUnramified f ∧ LocallyQuasiFinite f := by
  intro X Y f hf h
  have key : ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V)
      (e : V ≤ f ⁻¹ᵁ U), (f.appLE U V e).hom.FormallyUnramified := by
    intro U hU V hV e
    have hft := f.finiteType_appLE hU hV e
    letI := (f.appLE U V e).hom.toAlgebra
    haveI : Algebra.FiniteType Γ(Y, U) Γ(X, V) := hft
    refine formallyUnramified_of_tangent (A := Γ(Y, U)) (B := Γ(X, V)) fun K _ g hg => ?_
    have hc : constPt (Spec.map (CommRingCat.ofHom g) ≫ hV.fromSpec) =
        Spec.map (CommRingCat.ofHom (((algebraMap K (DualNumber K)).comp
          (TrivSqZeroExt.fstHom K K K).toRingHom).comp g)) ≫ hV.fromSpec := by
      simp only [constPt, spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have := h K (Spec.map (CommRingCat.ofHom g) ≫ hV.fromSpec) (by
      rw [hc]
      simp only [Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV e, ← Spec.map_comp_assoc]
      congr 2
      exact CommRingCat.hom_ext hg)
    rw [hc, cancel_mono, Spec.map_inj] at this
    exact congrArg CommRingCat.Hom.hom this
  refine ⟨⟨key⟩, ⟨fun {U} hU {V} hV e => ?_⟩⟩
  have h1 := key hU hV e
  have hft := f.finiteType_appLE hU hV e
  letI := (f.appLE U V e).hom.toAlgebra
  haveI : Algebra.FiniteType Γ(Y, U) Γ(X, V) := hft
  haveI : Algebra.FormallyUnramified Γ(Y, U) Γ(X, V) := h1
  exact (inferInstance : Algebra.QuasiFinite Γ(Y, U) Γ(X, V))

end GlobalTheory.TangentCriterion
