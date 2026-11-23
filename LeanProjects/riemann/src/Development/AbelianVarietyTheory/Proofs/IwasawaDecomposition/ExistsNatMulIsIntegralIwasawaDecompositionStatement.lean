import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatMulIsIntegralIwasawaDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nat_smul_mem_lattice' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (v : Fin N → E), ∃ d : ℕ, 0 < d ∧ (d : E) • v ∈ X.Λ := by
  first | exact @GlobalTheory.UnipKill.exists_nat_smul_mem_lattice | exact GlobalTheory.UnipKill.exists_nat_smul_mem_lattice | (intros; apply GlobalTheory.UnipKill.exists_nat_smul_mem_lattice <;> assumption)
