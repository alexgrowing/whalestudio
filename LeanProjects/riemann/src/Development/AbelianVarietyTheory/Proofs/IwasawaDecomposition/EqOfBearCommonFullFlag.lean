import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoBear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointCarriesFrameFlagsTransferBetweenFlagBundlesStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

theorem GlobalTheory.FlagBundle.eq_of_coBear : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (K : Type) [Field K] (p p' : Sp K ⟶ Y₁.X) (q : Sp K ⟶ Y₂.X), p ≫ f₁ = q ≫ f₂ → p' ≫ f₁ = q ≫ f₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p q → CoBear Eb S₁ φ₁ S₂ φ₂ (p' ≫ f₁) p' q → p = p' := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ K _ p p' q hp hp' hc hc'
  obtain ⟨A, hA, h, hh, hAp, hAq⟩ := hc
  obtain ⟨B, hB, h', -, hBp', hBq⟩ := hc'
  have hA' : A ∈ Eb.S ((q ≫ f₂) (IsLocalRing.closedPoint K)) := hp ▸ hA
  have hB' : B ∈ Eb.S ((q ≫ f₂) (IsLocalRing.closedPoint K)) := hp' ▸ hB
  have hAp' : Bears S₁ φ₁ A h p' :=
    GlobalTheory.T.pointCarriesFrameFlags_transfer_between_flag_bundles F ι m X Y₂ Y₁ Eb S₂ φ₂ f₂ S₁ φ₁ f₁ hR₂ hR₁ K q p' hp'.symm A hA' B hB' h h' hAq hBq hBp'
  exact (hR₁.2.2 K (p ≫ f₁) A hA h hh).unique ⟨rfl, hAp⟩ ⟨hp'.trans hp.symm, hAp'⟩
