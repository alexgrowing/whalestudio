import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricFlagCompactificationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricSmoothOffBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricSmoothOfHodgeStatement
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory

theorem metsOf_smooth : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (Φ : s.Flag) (k : s.Comp) (σ : D.what₂.LL →+* ℂ) (n : Pad.Letter S.Dw → ℤ), (∀ R : ℝ, 2 ≤ R → (cxSt D.what₂.LL).mSmooth _ σ _ (metsOf x Φ k (some R) σ n)) ∧ (cxSt D.what₂.LL).mSmooth _ σ _ (refMet x Φ k σ n) ∧ Var.Met.SmoothOn (metsOf x Φ k none σ n) {p | (Φ.C k).π (Var.base p) ∉ genBd s.T.Z} := by
  intro D A N j S κ s x Φ k σ n
  exact ⟨fun R hR => (GlobalTheory.T.eigen_metric_flag_compactification _ _ _ _ _ _ _ _ _ _ _ (Φ.C k) σ _ _ isOpen_univ
      (GlobalTheory.T.eigen_metric_smooth_of_hodge D A N j S κ s x _ R hR (GlobalTheory.T.hodge_metric_smooth_off_boundary D A N j S κ s x _)) n).2,
    (GlobalTheory.T.eigen_metric_flag_compactification _ _ _ _ _ _ _ _ _ _ _ (Φ.C k) σ _ _ isOpen_univ (x.smoothOn_eigMet _) n).2,
    (GlobalTheory.T.eigen_metric_flag_compactification _ _ _ _ _ _ _ _ _ _ _ (Φ.C k) σ _ _ (isOpen_not_liesIn _) (GlobalTheory.T.hodge_metric_smooth_off_boundary D A N j S κ s x _) n).2⟩

end GlobalTheory
