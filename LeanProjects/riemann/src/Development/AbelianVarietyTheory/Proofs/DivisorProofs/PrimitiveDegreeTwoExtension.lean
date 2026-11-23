import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeAndSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.H2StructureBaseChangeExtensionStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem primE2_of_primO2 (hO : PrimitiveStructureSheafDegTwoVanish) : PrimitiveExtendedDegTwoVanish := by
  intro R₀ R₁ _ _ _ q hq A _ g hA hsm c c₁ c₂ hμ h₁ h₂
  obtain ⟨B, _, pr, pr', hB, hBs, hp, hp', eμ, ef, es, -, -⟩ := GlobalTheory.T.exists_abelianScheme_baseChange_and_square R₀ R₁ A g hA hsm
  obtain ⟨e, he⟩ := GlobalTheory.T.h2_structure_base_change_extension R₀ R₁ q hq
  set eX := e A.left B.left A.hom B.hom pr hp
  set eY := e (A ⊗ A).left (B ⊗ B).left (A ⊗ A).hom (B ⊗ B).hom pr' hp'
  have hc : c = eX (eX.symm c) := (eX.apply_symm_apply c).symm
  have hc₁ : c₁ = eY (eY.symm c₁) := (eY.apply_symm_apply c₁).symm
  have hc₂ : c₂ = eY (eY.symm c₂) := (eY.apply_symm_apply c₂).symm
  have hsum : c₁ + c₂ = eY (eY.symm c₁ + eY.symm c₂) := by rw [map_add, ← hc₁, ← hc₂]
  have hd : eX.symm c = 0 := by
    refine hO R₁ B g hB hBs (eX.symm c) (eY.symm c₁) (eY.symm c₂) ?_ ?_ ?_
    · refine he A.left B.left A.hom B.hom pr hp (A ⊗ A).left (B ⊗ B).left (A ⊗ A).hom (B ⊗ B).hom pr' hp'
        (μ[A]).left (μ[B]).left (overW μ[A]) (overW μ[B]) eμ _ _ ?_
      rw [← hc, ← hsum]; exact hμ
    · refine he A.left B.left A.hom B.hom pr hp (A ⊗ A).left (B ⊗ B).left (A ⊗ A).hom (B ⊗ B).hom pr' hp'
        (fst A A).left (fst B B).left (overW (fst A A)) (overW (fst B B)) ef _ _ ?_
      rw [← hc, ← hc₁]; exact h₁
    · refine he A.left B.left A.hom B.hom pr hp (A ⊗ A).left (B ⊗ B).left (A ⊗ A).hom (B ⊗ B).hom pr' hp'
        (snd A A).left (snd B B).left (overW (snd A A)) (overW (snd B B)) es _ _ ?_
      rw [← hc, ← hc₂]; exact h₂
  rw [hc, hd, map_zero]

end GlobalTheory.Obs
