import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pOpEx :
    OpTr.{u} → OpEx.{u} := by
  intro hTr B R _ T hG Z Y Z' p p' s _ _ t hcomm
  obtain ⟨tr, htr⟩ := hG.tr p (s ≫ p) s rfl
  have key := fun A => hTr T hG p (s ≫ p) p' s t rfl hcomm tr htr A
  refine ⟨fun hgs => ⟨tr ∘ₗ T.pull t hcomm, (key _).2 hgs rfl, fun A hA => (key A).1 hA⟩, ?_⟩
  intro A hA W r c hc J _ σ h hsp x
  have hσ : ∀ j, σ j ≫ (s ≫ p) = r := by
    intro j
    rw [← hcomm, ← Category.assoc]
    exact h j
  rw [(key A).1 hA, LinearMap.comp_apply, htr W r c hc J σ hσ hsp]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [T.pull_comp (σ j) t (hσ j) hcomm]
