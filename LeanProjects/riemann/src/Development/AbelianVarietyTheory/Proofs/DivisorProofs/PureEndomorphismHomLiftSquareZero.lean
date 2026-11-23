import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPureBCId
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem pureLift_step : GlobalTheory.Published.GrothendieckMessing → ∀ p : ℕ, p.Prime → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), IsNilpotent (p : R) → Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (g g' : ℕ) (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (i : A₀.left ⟶ A.left) (j : B₀.left ⟶ B.left), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom → IsGrpPullback A₀ A (spMap π) i → IsGrpPullback B₀ B (spMap π) j → ∀ (U : A ⟶ A) (V : B ⟶ B) (U₀ : A₀ ⟶ A₀) (V₀ : B₀ ⟶ B₀) [IsMonHom U] [IsMonHom V] [IsMonHom U₀] [IsMonHom V₀], i ≫ U.left = U₀.left ≫ i → j ≫ V.left = V₀.left ≫ j → ∀ r s r' s' : R, IsPure A U r s → IsPure B V r' s' → IsUnit (r - s') → ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀], U₀ ≫ f₀ = f₀ ≫ V₀ → ∃ f : A ⟶ B, IsMonHom f ∧ i ≫ f.left = f₀.left ≫ j ∧ U ≫ f = f ≫ V ∧ ∀ f' : A ⟶ B, IsMonHom f' → i ≫ f'.left = f₀.left ≫ j → f' = f := by
  intro GM p hp R R₀ _ _ π hR hπ h2 g g' A B _ _ A₀ B₀ _ _ i j hA hgA hB hgB hi hj U V U₀ V₀ _ _ _ _ eU eV
    r s r' s' hU hV hu f₀ _ ef₀
  have h2' : RingHom.ker π ^ 2 = 0 := by rw [Ideal.zero_eq_bot]; exact h2
  obtain ⟨Hc, -, Hl⟩ := GM p hp R hR _ (GlobalTheory.Cris.divided₂ h2') (GlobalTheory.Cris.isDPNilpotent_squareZero h2') R₀ π hπ rfl
  set κ := GlobalTheory.Cris.divided₂ h2'
  have inj := (Hc.crysToDR_bijective hi hA hgA).1
  have key : ∀ d ∈ GlobalTheory.DeRham.liftFil κ hi, GlobalTheory.DeRham.push κ (spMap π) f₀ d ∈ GlobalTheory.DeRham.liftFil κ hj := by
    intro d hd
    have hd' : GlobalTheory.DeRham.crysToDR κ hi d ∈ GlobalTheory.DeRham.Fil A := hd
    have h1 : GlobalTheory.DeRham.push κ (spMap π) U₀ d = r • d := by
      apply inj
      rw [GlobalTheory.DeRham.crysToDR_push κ hi hi U₀ U eU, map_smul]
      exact hU.1 _ hd'
    have h3 : GlobalTheory.DeRham.push κ (spMap π) V₀ (GlobalTheory.DeRham.push κ (spMap π) f₀ d)
        = r • GlobalTheory.DeRham.push κ (spMap π) f₀ d := by
      have := congrArg (fun φ => φ d) (GlobalTheory.DeRham.push_comp κ (spMap π) U₀ f₀)
      have h4 := congrArg (fun φ => φ d) (GlobalTheory.DeRham.push_comp κ (spMap π) f₀ V₀)
      simp only [LinearMap.comp_apply] at this h4
      rw [← h4, ← GlobalTheory.DeRham.push_congr κ (spMap π) ef₀, this, h1, map_smul]
    show GlobalTheory.DeRham.crysToDR κ hj _ ∈ GlobalTheory.DeRham.Fil B
    refine IsPure.mem_Fil hV hu ?_
    rw [← GlobalTheory.DeRham.crysToDR_push κ hj hj V₀ V eV, h3, map_smul]
  obtain ⟨f, ⟨hf, ef⟩, uf⟩ := Hl g A₀ A i hi hA hgA g' B₀ B j hj hB hgB f₀ key
  refine ⟨f, hf, ef, ?_, fun f' hf' ef' => uf f' ⟨hf', ef'⟩⟩
  have e1 : i ≫ (U ≫ f).left = (U₀ ≫ f₀).left ≫ j := by
    simp only [Over.comp_left, ← Category.assoc, eU]
    simp only [Category.assoc, ef]
  have e2 : i ≫ (f ≫ V).left = (U₀ ≫ f₀).left ≫ j := by
    rw [Over.comp_left, ← Category.assoc, ef, Category.assoc, eV, ← Category.assoc, ← Over.comp_left, ← ef₀]
  exact Hl.unique hi hA hgA hj hB hgB (U₀ ≫ f₀) e1 e2

end GlobalTheory
