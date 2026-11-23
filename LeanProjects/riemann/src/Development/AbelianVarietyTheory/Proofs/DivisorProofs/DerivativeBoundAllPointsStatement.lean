import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeBoundAllPoints
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrAtNonneg
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_bound_all_points : Hypotheses2 → HypothesesH → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (la : AllWt.Weight S.Dw) (f : (Φ.C k).Y.Fn), f ∈ (Φ.C k).Y.H0 ((Φ.C k).Lw la) → ∀ (p : ℕ) [Fact p.Prime] (B : ℝ), 0 < B → (∀ (ι : AlgebraicClosure D.what₂.LL →+* ℂ_[p]) (y : AlgPt (Φ.C k).Y), drAt Φ k la p (spMap ι ≫ y.1) f ≤ B) → ∀ x : Sp ℂ_[p] ⟶ (Φ.C k).Y.X, drAt Φ k la p x f ≤ B := by
  first | exact @GlobalTheory.CovHt.Link.DenseBound.drAt_le_of_algPt | exact GlobalTheory.CovHt.Link.DenseBound.drAt_le_of_algPt | (intros; apply GlobalTheory.CovHt.Link.DenseBound.drAt_le_of_algPt <;> assumption)
