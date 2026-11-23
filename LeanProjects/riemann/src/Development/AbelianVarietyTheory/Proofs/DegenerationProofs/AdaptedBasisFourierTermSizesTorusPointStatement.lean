import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdaptedBasisFourierTermSizesTorusPoint
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
theorem _root_.GlobalTheory.T.adapted_basis_fourier_term_sizes_torusPoint : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 4 ≤ k → ∀ (J : Type) [Fintype J] (σ : J → (u.H k).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB k α), u.Basis l k σ cls f → ∀ s : J → Fam u.D.toPre (PadicAlgCl p) k, (∀ i, FamOf u.D.toPre _ (f i) (s i)) → ∀ (g : GtPtF u.D.toPre (PadicAlgCl p)) (ν : u.D.toPre.X → ℝ) (w : GlobalTheory.UT.Frm u.D.toPre (PadicAlgCl p) k g.b), u.GtN g ν → w.IsGen → ∃ κ : ℝ, 0 < κ ∧ ∀ α, (∀ i, GlobalTheory.UT.coef (s i) g w α ≠ 0 → ∃ m, α = cls i + k • m) ∧ (∀ i, ‖GlobalTheory.UT.coef (s i) g w α‖ ≤ κ * Real.exp (-((l.q α - l.q (cls i)) / k + ν α))) ∧ ∃ i, ‖GlobalTheory.UT.coef (s i) g w α‖ = κ * Real.exp (-((l.q α - l.q (cls i)) / k + ν α)) := by
  first | exact @GlobalTheory.TermSize.term_sizes | exact GlobalTheory.TermSize.term_sizes | (intros; apply GlobalTheory.TermSize.term_sizes <;> assumption)
