import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedOfLpDimLeOneOfUnitEigenvaluesStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowTie

open GlobalTheory.WeilDeligne

theorem tempered_of_rank_le_one (D : D7) (T : WDTie D.nd D.naut) (h1 : RankOneUnitary T)
    (a : ℕ) (π : D.naut.CG a) (ha : a ≤ 1) (w : PlE D.host) : D.naut.tempered (D.naut.locG π w) := by
  rw [T.tempered]
  have hd : (T.e w (D.naut.locG π w)).lpDim = a := by rw [T.dim, D.naut.locG_dim]
  refine GlobalTheory.T.tempered_of_lpDim_le_one_of_unit_eigenvalues _ _ _ _ _ _ (hd.le.trans ha) fun φ hφ α hα => ?_
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl
  · have hc := WD.card_eig (T.e w (D.naut.locG π w)) φ
    rw [hd, Multiset.card_eq_zero] at hc
    rw [hc] at hα
    exact absurd hα (Multiset.notMem_zero α)
  · refine h1 π w φ.1 (deg_eq_one_iff.mp hφ) α ?_
    rw [WDTie.eig, WD.inePol_of_mem _ φ.2]
    exact hα

theorem tempered_all_ranks : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), GlobalTheory.RowTie.RankOneUnitary T → (∀ (a : ℕ) (π : D.naut.CG a), 2 ≤ a → D.naut.csd π → D.naut.ralg π → ∀ w, D.naut.tempered (D.naut.locG π w)) → GlobalTheory.RowCopy.TempCSD D ∧ GlobalTheory.ThetaExh.Tempered D.nd D.naut := by
  intro D T h1 h2
  have key : GlobalTheory.ThetaExh.Tempered D.nd D.naut := by
    intro a π hc hr w
    rcases Nat.lt_or_ge a 2 with ha | ha
    · exact tempered_of_rank_le_one D T h1 a π (by omega) w
    · exact h2 a π ha hc hr w
  exact ⟨fun a π _ hc hr w => key a π hc hr w, key⟩

end GlobalTheory.RowTie
