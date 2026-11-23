import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousLinPow
import Development.AutomorphicArithmetic.LocalEmbeddings.RootSymSupport
open GlobalTheory MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.SwapTrue
open scoped Classical
theorem _root_.GlobalTheory.T.geometric_function_flag_degree : Hypotheses2 → HypothesesH → OnObj fun D O A _ _ _ => ∀ B : ℝ, 2 ≤ B → ∀ R : ℝ, 2 ≤ R → ∀ (c : O.s.Comp) (W : BunModel O (GlobalTheory.FlagAr.setB O.Y B) R c) (Ψ : MvPolynomial (Σ a : D.what₂.Tau × Bool, Fin (rkB D.what₂.Tau O.N O.j a)) ℝ →ₗ[ℝ] ℝ), IsGeoFun (fun z : Σ a : D.what₂.Tau × Bool, Fin (rkB D.what₂.Tau O.N O.j a) => VMetric.grLB (W.fl z.1) z.2 ((W.H z.1).pull W.π W.w)) (O.var c).dim Ψ → ∀ Q, Ψ Q = W.V.ν * A.w c * degFl D.what₂.Tau O.N (rename (blockEquiv D.what₂.Tau O.N O.j O.indef.2.le) Q) := by
  intro hP hH D O hC _ A T H h B hB R hR c W Ψ hΨ Q
  have hw : A.w = (O.s.cx O.L O.B O.fl).volC := h.aux.w
  rw [hw]
  exact GlobalTheory.BcRead.geo_eq hP hH O hC _ hR c W Ψ hΨ Q
