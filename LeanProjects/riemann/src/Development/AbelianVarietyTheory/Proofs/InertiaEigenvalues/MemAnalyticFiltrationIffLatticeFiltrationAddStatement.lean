import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemAnalyticFiltrationIffLatticeFiltrationAdd
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImagePolynomialAction
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_analytic_filtration_iff_lattice_filtration_add : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (i : ℤ) (x : Vec K a ι), x ∈ (P.ext (Rpi O K l e) ⊓ shiftE l e i (P.Mext (Rpi O K l e))) ⊔ shiftE l e 1 (P.ext (Rpi O K l e)) ↔ ∃ y ∈ P.filL i, x - y ∈ shiftE l e 1 (P.ext (Rpi O K l e)) := by
  first | exact @GlobalTheory.BK.PhiMod.mem_analytic_filtration_iff | exact GlobalTheory.BK.PhiMod.mem_analytic_filtration_iff | (intros; apply GlobalTheory.BK.PhiMod.mem_analytic_filtration_iff <;> assumption)
