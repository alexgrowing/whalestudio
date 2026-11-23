import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteNormLeExpWeightGap
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QDivBdQ
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_norm_le_exp_weight_gap : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (L : CmList A) (x : ToroidalCompactificationData s) (P : Mean4O.PolOf x Φ) (B : ℝ) (u : AllWt.Weight S.Dw) (r : ℚ), 0 < r → ∀ (k : s.Comp) (τ : ℕ), 1 ≤ τ → ∀ f ∈ (mbarOf P B (wtR L u) r k).secs τ, ∀ v e y, finN Φ k (τ • u) v e y f ≤ (mbarOf P B (wtR L u) r k).nrmFin v τ f e y * Real.exp (τ * ∑ z : DV.Rt D.what₂.Tau N, |wtR L u z.1 z.2 - r * P.dir z.1 z.2| * |lgOf (Φ.C k) (rootSym S.Dw (fun _ => false) none (DV.tauEmb D z.1) z.2) v e y - lgOf (Φ.C k) (rootSym S.Dw (ArIn.ind (setB κ B)) none (DV.tauEmb D z.1) z.2) v e y|) * (bdQ P k).nrmFin v 1 1 e y ^ ((τ : ℝ) * r) := by
  first | exact @GlobalTheory.CovHt.Link.FrameLog.finN_le | exact GlobalTheory.CovHt.Link.FrameLog.finN_le | (intros; apply GlobalTheory.CovHt.Link.FrameLog.finN_le <;> assumption)
