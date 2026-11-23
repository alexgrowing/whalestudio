import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateEndomorphismUnique
import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.AinfK GroundTheory.LocalField.FormalGroup GlobalTheory.AcrisK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_endomorphism_unique : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) [Finite (IsLocalRing.ResidueField ↥(OL K))] (π : ↥(OL K)) (hπ : Irreducible π),
    ∃ hf : IsLubinTateSeries π (ltSeries K π),
      ∀ (a : ↥(OL K)) (φ : PowerSeries ↥(OL K)), IsLTEndo K π a φ ↔ φ = (lubinTateHom hπ hf hf a).toPowerSeries := by
  first | exact @GlobalTheory.PZ.isLTEndo_iff_eq_lubinTateHom | exact GlobalTheory.PZ.isLTEndo_iff_eq_lubinTateHom | (intros; apply GlobalTheory.PZ.isLTEndo_iff_eq_lubinTateHom <;> assumption)
