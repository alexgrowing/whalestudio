import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pinch_gens_adapted : ∀ (R R₀ R' C' D E ν : Type) [CommRing R] [CommRing R₀] [CommRing R'] [CommRing C'] [CommRing D] [CommRing E] [Algebra R' C'] [Algebra.FiniteType R' C'] [Algebra R₀ D] (a : R →+* R') (m : R →+* R₀) (π : C' →+* E) (ψ : D →+* E) (ζ : ν → D), Function.Surjective m → Function.Surjective π → Function.Surjective (MvPolynomial.aeval ζ : MvPolynomial ν R₀ →ₐ[R₀] D) → IsPushout (CommRingCat.ofHom ((algebraMap R₀ D).comp m)) (CommRingCat.ofHom a) (CommRingCat.ofHom ψ) (CommRingCat.ofHom (π.comp (algebraMap R' C'))) → ∃ (κ : Type) (_ : Finite κ) (ξ : κ ⊕ ν → C'), (∀ s, π (ξ s) = ψ (Sum.elim (fun _ ↦ 0) ζ s)) ∧ Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial (κ ⊕ ν) R' →ₐ[R'] C') := by
  intro R R₀ R' C' D E ν _ _ _ _ _ _ _ _ _ a m π ψ ζ hm hπ hζ po
  choose ξ₀ hξ₀ using fun s => hπ (ψ (ζ s))
  have hcomm : ψ.comp ((algebraMap R₀ D).comp m) = (π.comp (algebraMap R' C')).comp a := by
    have := po.w
    exact congrArg CommRingCat.Hom.hom this
  have hsurj : Function.Surjective (π.comp (MvPolynomial.aeval ξ₀ : MvPolynomial ν R' →ₐ[R'] C').toRingHom) := by
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨r, rfl⟩)
    · obtain ⟨f, rfl⟩ := hζ d
      obtain ⟨g, rfl⟩ := MvPolynomial.map_surjective m hm f
      refine ⟨MvPolynomial.map a g, ?_⟩
      simp only [CommRingCat.hom_ofHom, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      induction g using MvPolynomial.induction_on with
      | C c =>
        have := congrArg (fun h => h c) hcomm
        simpa using this.symm
      | add p q hp hq => simp [hp, hq]
      | mul_X p s hp => simp [hp, hξ₀]
    · exact ⟨MvPolynomial.C r, by simp⟩
  obtain ⟨S, hS⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R' C').FG)
  choose p hp using fun t : S => hsurj (π t)
  refine ⟨S, inferInstance, Sum.elim (fun t => (t : C') - MvPolynomial.aeval ξ₀ (p t)) ξ₀, ?_, ?_⟩
  · rintro (t | s)
    · have := hp t
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
      simp [map_sub, this]
    · simp [hξ₀]
  · intro x
    have hx : x ∈ Algebra.adjoin R' (S : Set C') := by rw [hS]; trivial
    have hle : Algebra.adjoin R' (S : Set C') ≤
        (MvPolynomial.aeval (Sum.elim (fun t : S => (t : C') - MvPolynomial.aeval ξ₀ (p t)) ξ₀) :
          MvPolynomial (S ⊕ ν) R' →ₐ[R'] C').range := by
      rw [Algebra.adjoin_le_iff]
      intro t ht
      refine ⟨MvPolynomial.X (Sum.inl ⟨t, ht⟩) + MvPolynomial.rename Sum.inr (p ⟨t, ht⟩), ?_⟩
      simp [MvPolynomial.aeval_rename, Function.comp_def]
    obtain ⟨y, hy⟩ := hle hx
    exact ⟨y, hy⟩

end GlobalTheory
