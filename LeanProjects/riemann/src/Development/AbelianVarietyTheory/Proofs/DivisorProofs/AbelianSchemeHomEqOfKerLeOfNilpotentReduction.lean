import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsMonHomLift
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMonHomPointedSplitExtToAbelianVariety
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.QuotEq

theorem eq_of_ker_le_of_reduction : ∀ (A κ : Type) [CommRing A] [CommRing κ] (π : A →+* κ), Function.Surjective π → IsNilpotent (RingHom.ker π) → ∀ (G B : Over (Sp A)) [GrpObj G] [GrpObj B], IsAbelianScheme B → ∀ (q₁ q₂ : G ⟶ B), IsMonHom q₁ → IsMonHom q₂ → Flat q₁.left → Surjective q₁.left → QuasiCompact q₁.left → (∀ (T : Over (Sp A)) (x : T ⟶ G), x ≫ q₁ = 1 → x ≫ q₂ = 1) → pullback.fst G.hom (spMap π) ≫ q₁.left = pullback.fst G.hom (spMap π) ≫ q₂.left → q₁ = q₂ := by
  intro A κ _ _ π hπ hnil G B _ _ hB q₁ q₂ h₁ h₂ hfl hsu hqc hker hκ
  haveI := h₁; haveI := h₂; haveI := hfl; haveI := hsu; haveI := hqc
  obtain ⟨d, hd⟩ := GlobalTheory.ExtensionRigidity.exists_factor q₁ q₂ (fun W a b h => by
    have e : (a * b⁻¹) ≫ q₁ = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, h, mul_inv_cancel]
    have e₂ := hker W (a * b⁻¹) e
    rw [MonObj.mul_comp, GrpObj.inv_comp] at e₂
    exact mul_inv_eq_one.1 e₂)
  have hη : η[B] ≫ d = η[B] := by
    calc η[B] ≫ d = (η[G] ≫ q₁) ≫ d := by rw [IsMonHom.one_hom q₁]
      _ = η[B] := by rw [Category.assoc, hd, IsMonHom.one_hom q₂]
  haveI hdm : IsMonHom d := GlobalTheory.rigidity_holds (Sp A) B B hB hB d hη
  let qκ : pullback G.hom (spMap π) ⟶ pullback B.hom (spMap π) :=
    pullback.lift (pullback.fst G.hom (spMap π) ≫ q₁.left) (pullback.snd G.hom (spMap π))
      (by rw [Category.assoc, Over.w, pullback.condition])
  have hq₁ : qκ ≫ pullback.fst B.hom (spMap π) = pullback.fst G.hom (spMap π) ≫ q₁.left :=
    pullback.lift_fst _ _ _
  have hsq : IsPullback (pullback.fst G.hom (spMap π)) qκ q₁.left (pullback.fst B.hom (spMap π)) := by
    refine IsPullback.of_bot ?_ hq₁.symm (IsPullback.of_hasPullback B.hom (spMap π))
    rw [pullback.lift_snd, Over.w]
    exact IsPullback.of_hasPullback G.hom (spMap π)
  haveI : Flat qκ := MorphismProperty.of_isPullback hsq hfl
  haveI : Surjective qκ := MorphismProperty.of_isPullback hsq hsu
  haveI : QuasiCompact qκ := MorphismProperty.of_isPullback hsq hqc
  have hfib : pullback.fst B.hom (spMap π) ≫ d.left = pullback.fst B.hom (spMap π) := by
    rw [← cancel_epi qκ, reassoc_of% hq₁, ← Over.comp_left, hd, ← hκ, hq₁]
  have hP := isGrpPullback_pullback B (spMap π)
  have hu := GlobalTheory.HomLift.existsUnique_isMonHom_lift A κ π hπ hnil _ _ B B _ _ hP hP hB hB
    (𝟙 ((Over.pullback (spMap π)).obj B)) (𝟙 B) (by simp)
  have hd1 : d = 𝟙 B := hu.unique ⟨hdm, by simpa using hfib⟩ ⟨inferInstance, by simp⟩
  rw [← hd, hd1, Category.comp_id]

end GlobalTheory.Mum.QuotEq
