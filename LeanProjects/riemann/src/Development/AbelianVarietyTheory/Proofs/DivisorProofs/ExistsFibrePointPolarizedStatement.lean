import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibrePointPolarized
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibre_point_polarized : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (y : Sp ℂ ⟶ F.X) (P₁ : Out.PolAV (Sp ℂ)) (α : P₁.A.left ⟶ F.univ.A.left) (α₂ : (G2 P₁.A).left ⟶ (G2 F.univ.A).left) (K : Type) [Field K] [IsAlgClosed K] (ι : K →+* ℂ) (P₀ : Out.PolAV (Sp K)) (φ₀ : P₁.A.left ⟶ P₀.A.left), 3 ≤ n → Odd n → IsGrpPullback P₁.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ P₁.A P₁.L) (F.univ.P.pull α₂) → IsPolFibre ι P₀ P₁ φ₀ → ∃ y₀ : Sp K ⟶ F.X, spMap ι ≫ y₀ = y := by
  first | exact @GlobalTheory.SiegDescend.exists_point_over_subfield | exact GlobalTheory.SiegDescend.exists_point_over_subfield | (intros; apply GlobalTheory.SiegDescend.exists_point_over_subfield <;> assumption)
