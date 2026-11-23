import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinLevelAdditiveKilledByLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinFam.PtFacts

theorem mkZ_facts : ∀ {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] {T T' : Over S} (f : T' ⟶ T) (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (g : T ⟶ GlobalTheory.ZarhinFam.Zob A B) (n : ℕ), f ≫ GlobalTheory.ZarhinFam.mkZ A B u v = GlobalTheory.ZarhinFam.mkZ A B (fun i => f ≫ u i) (fun j => f ≫ v j) ∧ GlobalTheory.ZarhinFam.mkZ A B u v ^ n = GlobalTheory.ZarhinFam.mkZ A B (fun i => u i ^ n) (fun j => v j ^ n) ∧ (GlobalTheory.ZarhinFam.mkZ A B u v = 1 ↔ (∀ i, u i = 1) ∧ ∀ j, v j = 1) ∧ g = GlobalTheory.ZarhinFam.mkZ A B (fun i => g ≫ GlobalTheory.ZarhinFam.pa A B i) (fun j => g ≫ GlobalTheory.ZarhinFam.pb A B j) := by
  intro S A B _ _ _ _ T T' f u v g n
  refine ⟨?_, ?_, ⟨fun h => ⟨fun i => ?_, fun j => ?_⟩, fun ⟨hu, hv⟩ => ?_⟩, ?_⟩
  · apply LevAlg.zob_ext
    · intro i; simp only [Category.assoc, LevAlg.mkZ_pa]
    · intro j; simp only [Category.assoc, LevAlg.mkZ_pb]
  · apply LevAlg.zob_ext
    · intro i; rw [MonObj.pow_comp, LevAlg.mkZ_pa, LevAlg.mkZ_pa]
    · intro j; rw [MonObj.pow_comp, LevAlg.mkZ_pb, LevAlg.mkZ_pb]
  · rw [← LevAlg.mkZ_pa A B u v i, h, MonObj.one_comp]
  · rw [← LevAlg.mkZ_pb A B u v j, h, MonObj.one_comp]
  · apply LevAlg.zob_ext
    · intro i; rw [LevAlg.mkZ_pa, MonObj.one_comp, hu]
    · intro j; rw [LevAlg.mkZ_pb, MonObj.one_comp, hv]
  · apply LevAlg.zob_ext
    · intro i; rw [LevAlg.mkZ_pa]
    · intro j; rw [LevAlg.mkZ_pb]

end GlobalTheory.ZarhinFam.PtFacts
