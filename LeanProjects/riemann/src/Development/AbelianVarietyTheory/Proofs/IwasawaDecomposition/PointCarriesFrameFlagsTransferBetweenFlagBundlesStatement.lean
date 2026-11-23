import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointCarriesFrameFlagsTransferBetweenFlagBundles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoBear
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointCarriesFrameFlags_transfer_between_flag_bundles : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X) (q : Sp K ⟶ Y₂.X), p ≫ f₁ = q ≫ f₂ → ∀ A ∈ Eb.S ((p ≫ f₁) (IsLocalRing.closedPoint K)), ∀ B ∈ Eb.S ((p ≫ f₁) (IsLocalRing.closedPoint K)), ∀ h h' : Mat m K, Bears S₁ φ₁ A h p → Bears S₁ φ₁ B h' p → Bears S₂ φ₂ B h' q → Bears S₂ φ₂ A h q := by
  first | exact @GlobalTheory.FlagBundle.Bears.transfer | exact GlobalTheory.FlagBundle.Bears.transfer | (intros; apply GlobalTheory.FlagBundle.Bears.transfer <;> assumption)
