import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicPointAffineApprox
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrAtNonneg
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_point_affine_approx : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (la : AllWt.Weight S.Dw) (f : (Φ.C k).Y.Fn), f ∈ (Φ.C k).Y.H0 ((Φ.C k).Lw la) → ∀ (p : ℕ) [Fact p.Prime] (x : Sp ℂ_[p] ⟶ (Φ.C k).Y.X) (δ : ℝ), 0 < δ → ∃ (U : (Φ.C k).Y.X.Opens) (hU : IsAffineOpen U) (ε : Γ((Φ.C k).Y.X, U) →+* ℂ_[p]), x = spMap ε ≫ hU.fromSpec ∧ ∃ (t : Finset Γ((Φ.C k).Y.X, U)) (η : ℝ), 0 < η ∧ ∀ ε' : Γ((Φ.C k).Y.X, U) →+* ℂ_[p], (∀ h ∈ t, ‖ε' h - ε h‖ < η) → drAt Φ k la p x f - δ < drAt Φ k la p (spMap ε' ≫ hU.fromSpec) f := by
  first | exact @GlobalTheory.CovHt.Link.SemiCont.drAt_lowerSemicont | exact GlobalTheory.CovHt.Link.SemiCont.drAt_lowerSemicont | (intros; apply GlobalTheory.CovHt.Link.SemiCont.drAt_lowerSemicont <;> assumption)
