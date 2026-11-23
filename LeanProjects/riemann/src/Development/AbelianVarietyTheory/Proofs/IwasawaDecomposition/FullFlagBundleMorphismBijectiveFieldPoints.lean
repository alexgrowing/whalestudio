import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoBear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPointCarriesFrameFlagsOwnFrameStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointCarriesFrameFlagsTransferBetweenFlagBundlesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfBearCommonFullFlagStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory.FlagBundle

theorem CoBear₂ : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ g : Y₁.X ⟶ Y₂.X, g ≫ f₂ = f₁ → (∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X), CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p (p ≫ g)) → ∀ (K : Type) [Field K], Function.Bijective (fun p : Sp K ⟶ Y₁.X => p ≫ g) := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ g hg hco K _
  have hcomp : ∀ p : Sp K ⟶ Y₁.X, p ≫ f₁ = (p ≫ g) ≫ f₂ := by
    intro p; rw [Category.assoc, hg]
  constructor
  · intro p p' hpp'
    simp only at hpp'
    have h1 := hco K p
    have h2 := hco K p'
    rw [← hpp'] at h2
    exact GlobalTheory.T.eq_of_bear_common_fullFlag F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ K p p' (p ≫ g) (hcomp p)
      (by rw [hcomp p', hpp']) h1 h2
  · intro w
    obtain ⟨A, hA, h, hh, hw⟩ := GlobalTheory.T.exists_pointCarriesFrameFlags_own_frame F ι m X Y₂ Eb S₂ φ₂ f₂ hR₂ K w
    obtain ⟨p, ⟨hpx, hpA⟩, -⟩ := hR₁.2.2 K (w ≫ f₂) A hA h hh
    obtain ⟨B, hB, h', -, hpB, hqB⟩ := hco K p
    have hA' : A ∈ Eb.S ((p ≫ f₁) (IsLocalRing.closedPoint K)) := by rw [hpx]; exact hA
    have hqA : Bears S₂ φ₂ A h (p ≫ g) :=
      GlobalTheory.T.pointCarriesFrameFlags_transfer_between_flag_bundles F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ K p (p ≫ g) (hcomp p) A hA' B hB h h'
        hpA hpB hqB
    obtain ⟨q, -, hq⟩ := hR₂.2.2 K (w ≫ f₂) A hA h hh
    refine ⟨p, ?_⟩
    simp only
    rw [hq (p ≫ g) ⟨by rw [← hcomp p, hpx], hqA⟩, hq w ⟨rfl, hw⟩]

end GlobalTheory.FlagBundle
