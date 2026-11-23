import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationSymmetry
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_conjugation_symmetry : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (σ σ' : D.what₂.LL →+* ℂ) (n : Pad.Letter S.Dw → ℤ) (p : Pts (Φ.C k).Y σ) (p' : Pts (Φ.C k).Y σ') (a : (Φ.C k).Y.Fnˣ), p'.1 = spMap (starRingEnd ℂ) ≫ p.1 → p ∈ Var.eqnSet σ (divOf (Φ.C k) n) a → (∀ R, Var.Met.h (metsOf x Φ k R σ' n) a p' = Var.Met.h (metsOf x Φ k R σ n) a p) ∧ Var.Met.h (refMet x Φ k σ' n) a p' = Var.Met.h (refMet x Φ k σ n) a p ∧ rFlag x Φ k σ' p' = rFlag x Φ k σ p := by
  first | exact @GlobalTheory.ShFam.mets_conj | exact GlobalTheory.ShFam.mets_conj | (intros; apply GlobalTheory.ShFam.mets_conj <;> assumption)
