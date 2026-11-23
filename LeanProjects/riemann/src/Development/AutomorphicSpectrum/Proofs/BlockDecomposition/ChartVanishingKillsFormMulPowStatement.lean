import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartVanishingKillsFormMulPow
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_vanishing_kills_form_mul_pow : ∀ {R : Type} [CommRing R] {N : ℕ} {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) [QuasiCompact φ] (n : ℕ)
    (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n) (k : Fin (N + 1)),
    (φ.app (GlobalTheory.ProjSpace.chart R N k)).hom
      (GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n f hf) = 0 →
    ∃ (m : ℕ) (h : (X k ^ m * f : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (m + n)),
      KillsForm φ (m + n) (X k ^ m * f) h := by
  first | exact @GlobalTheory.CompanionTheory.GE.exists_killsForm_X_pow_mul | exact GlobalTheory.CompanionTheory.GE.exists_killsForm_X_pow_mul | (intros; apply GlobalTheory.CompanionTheory.GE.exists_killsForm_X_pow_mul <;> assumption)
