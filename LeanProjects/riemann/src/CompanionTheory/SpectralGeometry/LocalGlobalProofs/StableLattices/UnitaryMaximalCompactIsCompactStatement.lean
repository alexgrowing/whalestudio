import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UnitaryMaximalCompactIsCompact
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HsConjTranspose
open Matrix
open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag GlobalTheory.CompanionTheory.UGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_maximal_compact_is_compact : ∀ (n : ℕ) (ε : Fin n → Bool), IsCompact ((S7.KG ε : Subgroup (S7.UJ ε)) : Set (S7.UJ ε)) := by
  first | exact @GlobalTheory.CompanionTheory.UGeo.isCompact_KG_set | exact GlobalTheory.CompanionTheory.UGeo.isCompact_KG_set | (intros; apply GlobalTheory.CompanionTheory.UGeo.isCompact_KG_set <;> assumption)
