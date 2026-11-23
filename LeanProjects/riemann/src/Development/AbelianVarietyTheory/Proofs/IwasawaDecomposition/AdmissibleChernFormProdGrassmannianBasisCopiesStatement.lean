import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleChernFormProdGrassmannianBasisCopies
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RenVar
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleChernForm_prod_grassmannianBasisCopies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ), (∀ τ, g τ ∈ GlobalTheory.GrassTop.basis Dw.p Dw.q) → ∀ Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ, GlobalTheory.Schubert.admitted H Dw Θ → Θ (∏ τ, GlobalTheory.GrassTop.ren τ (g τ)) = (if ∀ τ, g τ = X (true, Dw.p) ^ Dw.q then (-1 : ℝ) ^ (Dw.p * Dw.q * Fintype.card (GlobalTheory.AllWt.Psi H)) else 0) * Θ (GlobalTheory.LieBase.pointPoly H Dw) := by
  first | exact @GlobalTheory.GrassTopProd.adm_apply_prod_ren_eq_ite_mul_pointPoly | exact GlobalTheory.GrassTopProd.adm_apply_prod_ren_eq_ite_mul_pointPoly | (intros; apply GlobalTheory.GrassTopProd.adm_apply_prod_ren_eq_ite_mul_pointPoly <;> assumption)
