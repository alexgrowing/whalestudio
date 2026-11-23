import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdealSheafAwayFromP
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem surj_mod_baseIdeal_of_isClosedImmersion : ∀ (R : Type) [CommRing R] (I : Ideal R) (X Z : Scheme.{0}) (φ : X ⟶ Z) (p : Z ⟶ Spec (CommRingCat.of R)), IsClosedImmersion (((baseIdeal p I).comap φ).subschemeι ≫ φ) → ∀ (V : Z.Opens) (hV : IsAffineOpen V), IsAffineOpen (φ ⁻¹ᵁ V) → Function.Surjective ((Ideal.Quotient.mk (((baseIdeal p I).ideal ⟨V, hV⟩).map (φ.app V).hom)).comp (φ.app V).hom) := by
  intro R _ I X Z φ p hg V hV hW
  set K := (baseIdeal p I).comap φ with hK
  have hKid : K.ideal ⟨φ ⁻¹ᵁ V, hW⟩ = ((baseIdeal p I).ideal ⟨V, hV⟩).map (φ.app V).hom := by
    rw [hK, GlobalTheory.Principalise.comapIdealAffine (baseIdeal p I) φ ⟨V, hV⟩ ⟨φ ⁻¹ᵁ V, hW⟩ le_rfl,
      Scheme.Hom.app_eq_appLE]
  intro q
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨b, hb⟩ := Scheme.Hom.app_surjective (K.subschemeι ≫ φ) V hV
    ((K.subschemeι.app (φ ⁻¹ᵁ V)).hom c)
  refine ⟨b, ?_⟩
  simp only [RingHom.comp_apply]
  rw [Ideal.Quotient.eq, ← hKid, ← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker, map_sub]
  rw [Scheme.Hom.comp_app] at hb
  rw [sub_eq_zero]
  exact hb

end GlobalTheory.FormalAlg
