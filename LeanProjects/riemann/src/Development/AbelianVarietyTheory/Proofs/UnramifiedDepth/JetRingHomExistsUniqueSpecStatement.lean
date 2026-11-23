import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.JetRingHomExistsUniqueSpec
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetRing_hom_exists_unique_spec : ∀ (V Ω A : Type) [CommRing V] [CommRing Ω] [CommRing A] [Algebra Ω A] (β : V →+* Ω) (κ : Type) [Fintype κ] [DecidableEq κ] (m : ℕ), (∀ a : κ → A, Ideal.span (Set.range a) ^ (m + 1) = ⊥ → ∃! ψ : Jet V κ m →+* A, (∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) ∧ ∀ i, ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = a i) ∧ ∀ ψ : Jet V κ m →+* A, (∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) → Ideal.span (Set.range fun i => ψ (Ideal.Quotient.mk _ (MvPolynomial.X i))) ^ (m + 1) = ⊥ ∧ (∀ i, IsNilpotent (ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)))) ∧ ∀ f : MvPowerSeries κ V, ψ (psJet m f) = nEval (MvPowerSeries.map β f) (fun i => ψ (Ideal.Quotient.mk _ (MvPolynomial.X i))) := by
  first | exact @GlobalTheory.AlphaPair.JetEv.jet_hom_spec | exact GlobalTheory.AlphaPair.JetEv.jet_hom_spec | (intros; apply GlobalTheory.AlphaPair.JetEv.jet_hom_spec <;> assumption)
