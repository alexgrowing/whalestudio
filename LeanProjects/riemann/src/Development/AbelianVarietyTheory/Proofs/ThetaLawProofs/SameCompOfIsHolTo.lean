import Mathlib
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.HolFamilyOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem sameComp_of_isHolTo : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsPreconnected B → (∀ b ∈ B, y b ≫ s = spMap σ) → IsHolTo B y → ∀ b ∈ B, ∀ b' ∈ B, SameComp s σ (y b) (y b') := by
  intro K _ σ X s m B y hB hc hs hy b hb b' hb'
  classical
  have hs' : ∀ w ∈ B, y w ≫ s = 𝟙 _ ≫ spMap σ := fun w hw => by rw [Category.id_comp]; exact hs w hw
  let c : (Fin m → ℂ) → (Sp ℂ ⟶ pullback s (spMap σ)) := fun w =>
    if h : w ∈ B then pullback.lift (y w) (𝟙 _) (hs' w h) else pullback.lift (y b) (𝟙 _) (hs' b hb)
  have hcw : ∀ w (h : w ∈ B), c w = pullback.lift (y w) (𝟙 _) (hs' w h) := fun w h => dif_pos h
  have h1 : ∀ w ∈ B, c w ≫ pullback.fst s (spMap σ) = y w := fun w h => by rw [hcw w h, pullback.lift_fst]
  have h2 : ∀ w, c w ≫ pullback.snd s (spMap σ) = 𝟙 _ := fun w => by
    by_cases h : w ∈ B
    · rw [hcw w h, pullback.lift_snd]
    · rw [show c w = pullback.lift (y b) (𝟙 _) (hs' b hb) from dif_neg h, pullback.lift_snd]
  have hopen : ∀ U : (pullback s (spMap σ)).Opens, IsOpen {w | w ∈ B ∧ ⊤ ≤ c w ⁻¹ᵁ U} := fun U => by
    refine (GlobalTheory.holFamily_of_isPullback GlobalTheory.valAt'_rules B (IsPullback.of_hasPullback s (spMap σ)) c
      (fun U f => ?_) (fun U f => ?_) U 0).1
    · have e : {w | w ∈ B ∧ ⊤ ≤ (c w ≫ pullback.fst s (spMap σ)) ⁻¹ᵁ U} = {w | w ∈ B ∧ ⊤ ≤ y w ⁻¹ᵁ U} := by
        ext w
        simp only [Set.mem_setOf_eq]
        exact and_congr_right fun h => by rw [h1 w h]
      rw [e]
      exact ⟨(hy U f).1, (hy U f).2.congr fun w hw => by rw [h1 w hw.1]⟩
    · simp only [h2]
      refine ⟨?_, differentiableOn_const _⟩
      by_cases h : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ U
      · simpa only [h, and_true, Set.setOf_mem_eq] using hB
      · simp only [h, and_false, Set.setOf_false, isOpen_empty]
  have hcont : ContinuousOn (fun w => c w (default : PrimeSpectrum ℂ)) B := by
    rw [continuousOn_open_iff hB]
    intro t ht
    convert hopen ⟨t, ht⟩ using 1
    ext w
    simp only [Set.mem_setOf_eq, GlobalTheory.top_le_preimage_iff_mem]
    rfl
  refine ⟨hs' b hb, hs' b' hb', fun z => ?_⟩
  obtain rfl : z = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  rw [← hcw b hb, ← hcw b' hb']
  exact (hc.image _ hcont).subset_connectedComponent ⟨b', hb', rfl⟩ ⟨b, hb, rfl⟩

end GlobalTheory.KeyFam
