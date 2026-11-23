import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtalePointOfExt
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FiniteTorsionAbelianGeomPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.AbTorsionGeomDescent

theorem finite_torsion_and_descent : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ), (n : k) ≠ 0 → Finite {g : 𝟙_ (Over (Sp k)) ⟶ A // g ^ n = 1} ∧ ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ Sp k) (g : Over.mk x ⟶ A), g ^ n = 1 → ∃ g₀ : 𝟙_ (Over (Sp k)) ⟶ A, g₀ ^ n = 1 ∧ g = toUnit (Over.mk x) ≫ g₀ := by
  intro k _ _ A _ _ hA n hn
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact absurd (by rw [h, Nat.cast_zero]) hn
    · exact h
  refine ⟨?_, ?_⟩
  · exact GlobalTheory.TorusExtTorsion.finite_torsion_abelian_geomPoint A hA k (𝟙 _) n hn1
  · intro κ _ _ x g hg
    letI : Algebra k κ := (Spec.preimage x).hom.toAlgebra
    have hx : x = spMap (algebraMap k κ) := by
      show x = Spec.map (CommRingCat.ofHom (Spec.preimage x).hom)
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    obtain ⟨g₀, hg₀, hgl⟩ := GlobalTheory.AlgClosedDescent.torsion_descent (K := κ) A hA n hn hx g hg
    refine ⟨g₀, hg₀, ?_⟩
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hgl]
    congr 1

end GlobalTheory.AbTorsionGeomDescent
