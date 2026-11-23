import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupportStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem fibre_subsingleton_of_isClosedImmersion_restrict :
    ∀ (R : Type) [CommRing R] (I : Ideal R) (X Z : Scheme.{0}) (φ : X ⟶ Z)
      (p : Z ⟶ Spec (CommRingCat.of R)),
      IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ) →
      ∀ z : Z, I ≤ (p z).asIdeal → (⇑φ ⁻¹' {z}).Subsingleton := by
  intro R _ I X Z φ p hci z hz
  have hmem : ∀ x : X, φ x = z → x ∈ Set.range ((baseIdeal p I).comap φ).subschemeι := by
    intro x hx
    rw [Scheme.IdealSheafData.range_subschemeι, GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.1 R Z X p φ I]
    show x ∈ (baseIdeal (φ ≫ p) I).support
    refine (GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.2.2 R X (φ ≫ p) I x).mpr ?_
    have e : (φ ≫ p) x = p (φ x) := by simp
    rw [e, hx]
    exact hz
  intro x hx x' hx'
  obtain ⟨y, rfl⟩ := hmem x hx
  obtain ⟨y', rfl⟩ := hmem x' hx'
  have hinj := (((baseIdeal p I).comap φ).subschemeι ≫ φ).isClosedEmbedding.injective
  have : y = y' := hinj (by
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx hx'
    have e : ∀ w, (((baseIdeal p I).comap φ).subschemeι ≫ φ) w = φ (((baseIdeal p I).comap φ).subschemeι w) := fun w => by simp
    rw [e, e, hx, hx'])
  rw [this]

end GlobalTheory.FormalAlg
