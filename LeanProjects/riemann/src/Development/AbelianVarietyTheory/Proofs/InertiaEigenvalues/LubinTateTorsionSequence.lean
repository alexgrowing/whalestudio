import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLeOneOfLt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowEqOfRoot
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

theorem GlobalTheory.PZ.ltData_read_OC : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l), LTData K χ π z →
    ∃ (hπ : Irreducible π) (hF : IsLubinTateSeries π (ltSeries K π)) (v : ℕ → OC l), v 0 = 0 ∧ v 1 ≠ 0 ∧
      (∀ n, intToOC K π * v (n + 1) + v (n + 1) ^ l ^ fK K = v n) ∧
      ∀ g : ↥(GK K), ∃ a : ↥(OL K), (a : ↥K.1) = (χ g : ↥K.1) ∧ ∀ n,
        HasSum (fun i => ((intToOC K (PowerSeries.coeff i (lubinTateHom hπ hF hF a).toPowerSeries) * v n ^ i : OC l) : ℂ_[l]))
          ((Per.σO (g : GQ l) (v n) : OC l) : ℂ_[l]) := by
  intro l _ K χ π z h
  haveI : Finite (IsLocalRing.ResidueField ↥(OL K)) :=
    Nat.finite_of_card_ne_zero (by rw [GlobalTheory.AinfK.card_res K]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  have hrel := h.2.2.2.1
  obtain ⟨hπ, hF, v, hv, -, h0, h1, hg⟩ := GlobalTheory.PZ.ltData_tilt_hyps l K χ π z h
  refine ⟨hπ, hF, v, h0, h1, fun n => ?_, fun g => ?_⟩
  · apply Subtype.ext
    have e := congrArg (algebraMap (Om l) ℂ_[l]) (hrel n)
    rw [map_add, map_mul, map_pow, ← hv, ← hv] at e
    have hq : resCard K = l ^ fK K := rfl
    rw [← hq]
    exact e
  · obtain ⟨a, ha, -⟩ := h.2.2.2.2 g
    exact ⟨a, ha, hg g a ha⟩
