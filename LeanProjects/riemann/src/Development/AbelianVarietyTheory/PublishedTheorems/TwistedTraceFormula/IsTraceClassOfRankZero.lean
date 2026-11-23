import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstantOneNotCuspidalOfIsotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyRecordOfLocStage

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.Cusp GlobalTheory.Orb GlobalTheory.AdelicU GlobalTheory.SplitWeil GlobalTheory.Cusp.Model GlobalTheory.CuspDecay.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspSpectrum.Model

theorem exists_measure (D : D7) (V : HSp D) :
    ∃ μ : Measure (GA D V), μ.IsHaarMeasure ∧ μ.IsMulRightInvariant :=
  ⟨Measure.haar, inferInstance, AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V _ inferInstance⟩

theorem exists_ne_zero : ∃ (D : D7) (V : HSp D) (μ : Measure (GA D V)) (_ : μ.IsHaarMeasure)
    (_ : μ.IsMulRightInvariant), V.rank = 1 ∧ ∃ f ∈ CcGA V, RcuspOp V μ f ≠ 0 := by
  obtain ⟨D⟩ := Mem.nonempty_record_of_locStage
  obtain ⟨μ, _, _⟩ := exists_measure D (line D)
  obtain ⟨v, hv, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (L2cusp_ne_bot μ (wittIndex_line D))
  obtain ⟨f, hf, h⟩ := exists_RcuspOp_ne_zero (v := ⟨v, hv⟩) fun e => h0 (congrArg Subtype.val e)
  exact ⟨D, line D, μ, ‹_›, ‹_›, rfl, f, hf, fun e => h (by rw [e]; rfl)⟩

theorem exists_isotropic : ∃ (D : D7) (V : HSp D) (μ : Measure (GA D V)) (_ : μ.IsHaarMeasure)
    (_ : μ.IsMulRightInvariant), wittIndex V = 1 ∧ L2cusp V μ ≠ ⊤ ∧ ∃ f ∈ CcGA V, f 1 = 1 := by
  obtain ⟨D⟩ := Mem.nonempty_record_of_locStage
  obtain ⟨μ, _, _⟩ := exists_measure D (plane D)
  obtain ⟨φ, hφ, -, h1, -⟩ := exists_bump_ccAd (J := (plane D).gram) (isCMExt_host D) univ_mem
  exact ⟨D, plane D, μ, ‹_›, ‹_›, wittIndex_plane D, L2cusp_plane_ne_top μ, _, hφ, by simp [h1]⟩

variable {D : D7} {V : HSp D} {μ : Measure (GA D V)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem RcuspOp_one {v : L2cusp V μ} (hv : (v : DividedPowerChartLift V μ) = constantOneDividedPowerChartLift V μ) {f : GA D V → ℂ} (hf : f ∈ CcGA V) :
    RcuspOp V μ f v = (∫ g, f g ∂μ) • v := by
  have h1 : ∀ g, Rcusp V μ g v = v := fun g => Subtype.ext (by
    change RG V μ g (v : DividedPowerChartLift V μ) = _
    rw [hv]
    exact right_translate_toL2 (memL2_const (Γ := GQ V) (μ := μ) 1) g)
  rw [(isRepOp_RcuspOp hf v).2]
  simp only [h1]
  exact integral_smul_const f v

theorem isTraceClass_of_rank_zero (h : V.rank = 0) (f : GA D V → ℂ) : IsTraceClass (RcuspOp V μ f) := by
  have : IsEmpty (Fin V.rank) := h ▸ inferInstanceAs (IsEmpty (Fin 0))
  have hs : Subsingleton (GA D V) := ⟨fun a b => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩
  have hq : Subsingleton (Quot (GQ V)) := ⟨fun a b => by
    rw [← mk_sec a, ← mk_sec b, Subsingleton.elim (sec _ a) (sec _ b)]⟩
  have : FiniteDimensional ℂ (DividedPowerChartLift V μ) := by
    refine Module.Finite.of_surjective (LinearMap.toSpanSingleton ℂ _ (constantOneDividedPowerChartLift V μ)) fun F => ?_
    refine ⟨F (mk _ 1), Lp.ext ?_⟩
    filter_upwards [Lp.coeFn_smul (F (mk _ 1)) (constantOneDividedPowerChartLift V μ), (memL2_const (Γ := GQ V) (μ := μ) 1).coeFn_toL2] with q a b
    rw [LinearMap.toSpanSingleton_apply, a, Pi.smul_apply, show constantOneDividedPowerChartLift V μ q = _ from b, Subsingleton.elim q (mk _ 1)]
    simp [AutomorphicL2Unitary.descend]
  exact isTraceClass_of_finiteDimensional _

end GlobalTheory.CuspSpectrum.Model

end
