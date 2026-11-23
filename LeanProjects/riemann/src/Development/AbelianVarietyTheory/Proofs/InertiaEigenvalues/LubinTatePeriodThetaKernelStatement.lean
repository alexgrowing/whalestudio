import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTatePeriodThetaKernel
import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.AinfK GroundTheory.LocalField.FormalGroup GlobalTheory.AcrisK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_period_theta_kernel : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l), LTData K χ π z →
    ∀ ω : AK K, ω ≠ 0 → thetaK K ω = 0 → frobq K ω = inO K π * ω + ω ^ resCard K →
      (∀ (g : ↥(GK K)) (a : ↥(OL K)) (φ : PowerSeries ↥(OL K)), (a : ↥K.1) = (χ g : ↥K.1) → IsLTEndo K π a φ →
        ∀ n : ℕ, gal K g ω - ∑ j ∈ Finset.range n, inO K (PowerSeries.coeff j φ) * ω ^ j ∈ RingHom.ker (thetaK K) ^ n) →
      ω ∉ RingHom.ker (thetaK K) ^ 2 := by
  first | exact @GlobalTheory.LTPeriodKerSq.main | exact GlobalTheory.LTPeriodKerSq.main | (intros; apply GlobalTheory.LTPeriodKerSq.main <;> assumption)
