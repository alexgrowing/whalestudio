import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

theorem eq_zero_of_forall_algHom_complex {A : Type*} [CommRing A] [Algebra ℂ A] [_root_.IsReduced A]
    [Algebra.FiniteType ℂ A] (a : A) (h : ∀ e : A →ₐ[ℂ] ℂ, e a = 0) : a = 0 := by
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℂ)
  have hrad : (⊥ : Ideal A).IsRadical := by
    rw [Ideal.isRadical_bot_iff]; infer_instance
  have hj : (⊥ : Ideal A).jacobson = ⊥ := IsJacobsonRing.out inferInstance hrad
  rw [← Ideal.mem_bot, ← hj, Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨-, hm⟩
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite ℂ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (A ⧸ m)
  have hb : Function.Bijective (algebraMap ℂ (A ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let i : ℂ ≃ₐ[ℂ] (A ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId ℂ (A ⧸ m)) hb
  have := h ((i.symm : (A ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m))
  rw [AlgHom.comp_apply] at this
  have h2 : Ideal.Quotient.mkₐ ℂ m a = 0 := by
    apply i.symm.injective
    rw [map_zero]; exact this
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

theorem eq_of_valAt'_eq :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) →
    (∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f) →
    (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') := by
  intro hval haff X hred hft U f f' h
  refine TopCat.Sheaf.eq_of_locally_eq' X.left.sheaf
    (fun V : {V : X.left.Opens // IsAffineOpen V ∧ V ≤ U} => V.1) U (fun V => homOfLE V.2.2) ?_ f f' ?_
  · intro p hp
    obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVU⟩ :=
      X.left.isBasis_affineOpens.exists_subset_of_mem_open hp U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, hVU⟩, hpV⟩
  · rintro ⟨V, hV, hVU⟩
    change resG X.left hVU f = resG X.left hVU f'
    let c : ℂ →+* Γ(X.left, V) :=
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ V (fun _ _ => trivial)).hom
    have hc : c.FiniteType := by
      have h1 : (X.hom.appLE ⊤ V (fun _ _ => trivial)).hom.FiniteType :=
        HasRingHomProperty.appLE @LocallyOfFiniteType X.hom hft ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _
      exact h1.comp (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
    letI : Algebra ℂ Γ(X.left, V) := c.toAlgebra
    haveI : Algebra.FiniteType ℂ Γ(X.left, V) := hc
    rw [← sub_eq_zero]
    apply eq_zero_of_forall_algHom_complex
    intro e
    obtain ⟨x, ⟨hxV, hx⟩, -⟩ := haff X V hV e.toRingHom (fun a => e.commutes a)
    have hres := (hval X.left x.left).2.2.1 U V hVU
    have hxU : ⊤ ≤ x.left ⁻¹ᵁ U := fun p hp => hVU (hxV hp)
    have e1 : e (resG X.left hVU f) = valAt' x.left U f := (hx _).symm.trans (hres f hxV)
    have e2 : e (resG X.left hVU f') = valAt' x.left U f' := (hx _).symm.trans (hres f' hxV)
    rw [map_sub, e1, e2, h x hxU, sub_self]

end GlobalTheory
