import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductDegDataSecondFactorInclProjAdjoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productDegData_secondFactor_incl_proj_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D₁ D₂ : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (i₂ : D₂.toPre.P.A ⟶ D.toPre.P.A) (j₂ : D₂.toPre.X →+ D.toPre.X), i₂ ≫ p₁ = toUnit _ ≫ η[D₁.toPre.P.A] → i₂ ≫ p₂ = 𝟙 _ → (∀ y, q₁ (j₂ y) = 0) → (∀ y, q₂ (j₂ y) = y) → Adj (pol D₂) (pol D) i₂ p₂ j₂ q₂ := by
  first | exact @GlobalTheory.MumSumSnd.adj_snd | exact GlobalTheory.MumSumSnd.adj_snd | (intros; apply GlobalTheory.MumSumSnd.adj_snd <;> assumption)
