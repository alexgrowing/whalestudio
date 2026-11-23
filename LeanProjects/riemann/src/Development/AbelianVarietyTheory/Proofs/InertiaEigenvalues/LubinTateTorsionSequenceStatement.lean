import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateTorsionSequence
import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_torsion_sequence : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l), LTData K χ π z →
    ∃ (hπ : Irreducible π) (hF : IsLubinTateSeries π (ltSeries K π)) (v : ℕ → OC l), v 0 = 0 ∧ v 1 ≠ 0 ∧
      (∀ n, intToOC K π * v (n + 1) + v (n + 1) ^ l ^ fK K = v n) ∧
      ∀ g : ↥(GK K), ∃ a : ↥(OL K), (a : ↥K.1) = (χ g : ↥K.1) ∧ ∀ n,
        HasSum (fun i => ((intToOC K (PowerSeries.coeff i (lubinTateHom hπ hF hF a).toPowerSeries) * v n ^ i : OC l) : ℂ_[l]))
          ((Per.σO (g : GQ l) (v n) : OC l) : ℂ_[l]) := by
  first | exact @GlobalTheory.PZ.ltData_read_OC | exact GlobalTheory.PZ.ltData_read_OC | (intros; apply GlobalTheory.PZ.ltData_read_OC <;> assumption)
