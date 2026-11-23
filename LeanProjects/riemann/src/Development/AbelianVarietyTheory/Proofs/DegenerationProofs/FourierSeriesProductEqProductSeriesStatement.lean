import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FourierSeriesProductEqProductSeries
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierSeries_product_eq_product_series : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k k' : ℕ) (g : GtPtF u.D.toPre (PadicAlgCl p)) (w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b) (w' : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k' g.b) (w'' : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) (k + k') g.b), 1 ≤ k → 1 ≤ k' → w.IsGen → w'.IsGen → w''.IsGen → ∃ κ : PadicAlgCl p, κ ≠ 0 ∧ ∀ (σ : u.U.toUnifPre.SecGF (PadicAlgCl p) k) (σ' : u.U.toUnifPre.SecGF (PadicAlgCl p) k') (σ'' : u.U.toUnifPre.SecGF (PadicAlgCl p) (k + k')) s s' s'', u.U.toUnifPre.ExpandsG (PadicAlgCl p) k σ s → u.U.toUnifPre.ExpandsG (PadicAlgCl p) k' σ' s' → u.U.toUnifPre.ExpandsG (PadicAlgCl p) (k + k') σ'' s'' → (∀ j, (show Γ((UnifPre.GF (G := u.G) (PadicAlgCl p)).left, (LB.LinComb u.U.LG.L (K := Fin 1) (fun _ => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => ((k : ℕ) : ℤ))).U j) from σ''.f j) = σ.f j * (show Γ((UnifPre.GF (G := u.G) (PadicAlgCl p)).left, (LB.LinComb u.U.LG.L (K := Fin 1) (fun _ => UnifPre.gFK (G := u.G) (PadicAlgCl p)) (fun _ => ((k : ℕ) : ℤ))).U j) from σ'.f j)) → ∀ x x', HasSum (fun χ => GlobalTheory.UT.coef s g w χ) x → HasSum (fun χ => GlobalTheory.UT.coef s' g w' χ) x' → HasSum (fun χ => GlobalTheory.UT.coef s'' g w'' χ) (κ * x * x') := by
  first | exact @GlobalTheory.ZH.SeriesProd.main | exact GlobalTheory.ZH.SeriesProd.main | (intros; apply GlobalTheory.ZH.SeriesProd.main <;> assumption)
