import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InverseGramEigenvaluesSumHs
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HsConjTranspose
open Matrix
open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag GlobalTheory.CompanionTheory.UGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverse_gram_eigenvalues_sum_hs : ∀ (n : ℕ) (ε : Fin n → Bool) (g : S7.UJ ε) (hT : ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹).IsHermitian), (∀ i, 0 < hT.eigenvalues i) ∧ ∑ i, hT.eigenvalues i = Formalism.REAL.hs (S7.toM g) := by
  first | exact @GlobalTheory.CompanionTheory.UGeo.specpos_inv_eigenvalues | exact GlobalTheory.CompanionTheory.UGeo.specpos_inv_eigenvalues | (intros; apply GlobalTheory.CompanionTheory.UGeo.specpos_inv_eigenvalues <;> assumption)
