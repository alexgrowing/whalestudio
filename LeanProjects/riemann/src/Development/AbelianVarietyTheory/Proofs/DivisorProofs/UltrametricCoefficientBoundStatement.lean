import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UltrametricCoefficientBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLeOfClosedPoint
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.QCoh GlobalTheory.ChainPts GlobalTheory.ChainPts.PullHT
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ultrametric_coefficient_bound : ∀ {X : Scheme.{0}} {F : X.Modules} {r : ℕ} (d : Bool) {V V₁ V' : X.Opens} {e : Fin r → Γ(F, V)} {e₁ : Fin r → Γ(F, V₁)} {s : Fin r → Γ(F, V')} (he : GlobalTheory.VB.IsFrame e) (he₁ : GlobalTheory.VB.IsFrame e₁) (hs : GlobalTheory.VB.IsFrame s) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (w : Sp ↥(intO C) ⟶ X), ⊤ ≤ w ⁻¹ᵁ V → ⊤ ≤ w ⁻¹ᵁ V₁ → ∀ cf : Fin r → C, (∀ l, ‖∑ i, cf i * valF (spMap (intO C).subtype ≫ w) _ (coef d he hs l i)‖ ≤ 1) ↔ ∀ l, ‖∑ i, cf i * valF (spMap (intO C).subtype ≫ w) _ (coef d he₁ hs l i)‖ ≤ 1 := by
  first | exact @GlobalTheory.ChainPts.FrameNorm.norm_le_one_iff | exact GlobalTheory.ChainPts.FrameNorm.norm_le_one_iff | (intros; apply GlobalTheory.ChainPts.FrameNorm.norm_le_one_iff <;> assumption)
