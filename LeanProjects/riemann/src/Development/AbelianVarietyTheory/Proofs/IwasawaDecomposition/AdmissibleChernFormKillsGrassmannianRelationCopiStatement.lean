import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleChernFormKillsGrassmannianRelationCopi
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RenVar
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adm_apply_mul_ren_eq_zero_of_mem_J : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ), GlobalTheory.Schubert.admitted H Dw Θ → ∀ (τ : GlobalTheory.AllWt.Psi H) (j : MvPolynomial (Bool × ℕ) ℝ), j ∈ GlobalTheory.GrassTop.J Dw.p Dw.q → ∀ r : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, Θ (r * GlobalTheory.GrassTop.ren τ j) = 0 := by
  first | exact @GlobalTheory.GrassTop.admissibleChernForm_kills_grassmannianRelationCopies | exact GlobalTheory.GrassTop.admissibleChernForm_kills_grassmannianRelationCopies | (intros; apply GlobalTheory.GrassTop.admissibleChernForm_kills_grassmannianRelationCopies <;> assumption)
