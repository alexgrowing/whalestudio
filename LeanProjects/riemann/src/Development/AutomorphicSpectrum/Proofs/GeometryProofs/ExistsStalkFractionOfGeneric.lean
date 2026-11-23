import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem genMap_germ_eq_closedPointTo {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (p : Cpt ξ) (V : X.Opens) (hy : p.1 ∈ V) (hx : genPt ξ ∈ V) (b : Γ(X, V)) :
    genMap ξ p (X.presheaf.germ V p.1 hy b) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ V (genPt ξ) hx b) := by
  have h : X.presheaf.germ V (genPt ξ) hx = X.presheaf.germ V p.1 hy ≫ X.presheaf.stalkSpecializes p.2 :=
    (X.presheaf.germ_stalkSpecializes hy p.2).symm
  rw [h]
  rfl

theorem exists_frac_genMap {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) (a : Ω) :
    ∃ b c : X.presheaf.stalk p.1, genMap ξ p c ≠ 0 ∧ a * genMap ξ p c = genMap ξ p b := by
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (x := p.1) (U := ⊤) trivial
  have hgU : genPt ξ ∈ U := p.2.mem_open U.isOpen hpU
  let _ : Algebra Γ(X, U) (X.presheaf.stalk (genPt ξ)) := (X.presheaf.germ U (genPt ξ) hgU).hom.toAlgebra
  have _ : IsLocalization.AtPrime (X.presheaf.stalk (genPt ξ)) (hU.primeIdealOf ⟨genPt ξ, hgU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨genPt ξ, hgU⟩
  obtain ⟨s, rfl⟩ : ∃ s : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom s = a := hξ.bij.2 a
  obtain ⟨⟨r, d⟩, rfl⟩ := IsLocalization.mk'_surjective (hU.primeIdealOf ⟨genPt ξ, hgU⟩).asIdeal.primeCompl s
  refine ⟨X.presheaf.germ U p.1 hpU r, X.presheaf.germ U p.1 hpU d, ?_, ?_⟩
  · rw [genMap_germ_eq_closedPointTo ξ p U hpU hgU]
    have hu := IsLocalization.map_units (X.presheaf.stalk (genPt ξ)) d
    exact (hu.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  · rw [genMap_germ_eq_closedPointTo ξ p U hpU hgU, genMap_germ_eq_closedPointTo ξ p U hpU hgU]
    have h := congrArg (Scheme.stalkClosedPointTo ξ).hom (IsLocalization.mk'_spec (X.presheaf.stalk (genPt ξ)) r d)
    exact ((Scheme.stalkClosedPointTo ξ).hom.map_mul _ _).symm.trans h

end GlobalTheory.CompanionTheory.Ar
