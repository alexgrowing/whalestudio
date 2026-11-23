import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHasFlag

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.FlagPush

open GlobalTheory.FlagMeas

theorem simplex_meas (a : ℕ) : MeasurableSet (simplexH a) := by
  have h : simplexH a = (⋂ i : Fin a, ⋂ k : Fin a, {τ : Fin a → ℝ | i < k → τ i < τ k}) ∩
      ⋂ i : Fin a, ({τ : Fin a → ℝ | 0 < τ i} ∩ {τ | τ i < 1 / 2}) := by
    ext τ
    simp only [simplexH, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun ⟨h1, h2⟩ => ⟨fun i k hik => h1 hik, fun i => h2 i⟩,
      fun ⟨h1, h2⟩ => ⟨fun i k hik => h1 i k hik, fun i => h2 i⟩⟩
  rw [h]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun k => ?_)
    (MeasurableSet.iInter fun i => (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
      (measurableSet_lt (measurable_pi_apply i) measurable_const))
  by_cases hik : i < k
  · simpa [hik] using measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply k)
  · simp [hik]

theorem dens_meas (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) : Measurable (FlagMeas.dens n f j) := by
  show Measurable fun τ => FlagMeas.dens n f j τ
  simp only [FlagMeas.dens, layerProd, id]
  fun_prop

theorem mem_simplex {I : AutInst} {x : I.GA} {a : ℕ} {j : Fin a → ℕ} {τ : Fin a → ℝ}
    (h : HasType I x j τ) : τ ∈ simplexH a := by
  obtain ⟨S, ⟨-, -, -, hmono, hτ, -⟩, -⟩ := h
  exact ⟨hmono, fun i => ⟨(hτ i).1, (hτ i).2.1⟩⟩

theorem lintegral_type_le : GlobalTheory.FlagMeas.FlagMeasureBound → ∀ (B : RowsAut) (p q : ℕ), SigIs B p q → 2 * q + 2 ≤ B.I.n → ∀ (a : ℕ) (j : Fin a → ℕ), 1 ≤ a → (∀ i, 1 ≤ j i) → ∑ i, j i ≤ q → ∀ (G : (Fin a → ℝ) → ENNReal) (Φ : B.I.GA → ENNReal), Measurable G → (∀ x τ, HasType B.I x j τ → Φ x ≤ G τ) → ∫⁻ x in {x | ∃ τ, HasType B.I x j τ} ∩ B.fund, Φ x ∂(B.I.muA B.μf) ≤ B.I.muA B.μf B.fund * ENNReal.ofReal (GlobalTheory.FlagMeas.kapBd B.I.E p q j) * ∫⁻ τ in GlobalTheory.FlagMeas.simplexH a, G τ * ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ) := by
  intro hFMB B p q hSig hn a j ha hj hsum G Φ hG hΦ
  have := B.haar
  have := B.sf
  obtain ⟨s, hs, hT, hsτ⟩ := GlobalTheory.FlagMeas.type_measurable B.I a j
  set T : Set B.I.GA := {x | ∃ τ, HasType B.I x j τ} with hTdef
  set μ := B.I.muA B.μf with hμ
  set K : ENNReal := μ B.fund * ENNReal.ofReal (GlobalTheory.FlagMeas.kapBd B.I.E p q j) with hK
  set ρ : Measure (Fin a → ℝ) := (volume.restrict (GlobalTheory.FlagMeas.simplexH a)).withDensity
    (fun τ => ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ)) with hρ
  have hd : Measurable (fun τ => ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ)) :=
    (dens_meas B.I.n B.I.f j).ennreal_ofReal

  have h1 : ∫⁻ x in T ∩ B.fund, Φ x ∂μ ≤ ∫⁻ x in T ∩ B.fund, G (s x) ∂μ := by
    rw [← Measure.restrict_restrict hT]
    refine lintegral_mono_ae ?_
    refine (ae_restrict_iff' hT).2 (Filter.Eventually.of_forall ?_)
    rintro x ⟨τ, hx⟩
    rw [hsτ x τ hx]
    exact hΦ x τ hx

  have h2 : Measure.map s (μ.restrict (T ∩ B.fund)) ≤ K • ρ := by
    rw [Measure.le_iff]
    intro A hA
    rw [Measure.map_apply hs hA, Measure.restrict_apply (hs hA), Measure.smul_apply, smul_eq_mul,
      hρ, withDensity_apply _ hA, Measure.restrict_restrict hA]
    have hsub : s ⁻¹' A ∩ (T ∩ B.fund) ⊆
        GlobalTheory.FlagMeas.typeSet B.I j (A ∩ GlobalTheory.FlagMeas.simplexH a) ∩ B.fund := by
      rintro x ⟨hxA, ⟨τ, hx⟩, hxf⟩
      refine ⟨⟨τ, ⟨?_, mem_simplex hx⟩, hx⟩, hxf⟩
      have hxs : s x = τ := hsτ x τ hx
      rw [← hxs]
      exact hxA
    obtain ⟨-, h0, htop, hle⟩ := hFMB B.I B.μf B.fund B.fund_spec p q hSig hn a j ha hj hsum
      (A ∩ GlobalTheory.FlagMeas.simplexH a) (hA.inter (simplex_meas a)) Set.inter_subset_right
    calc μ (s ⁻¹' A ∩ (T ∩ B.fund))
        ≤ μ (GlobalTheory.FlagMeas.typeSet B.I j (A ∩ GlobalTheory.FlagMeas.simplexH a) ∩ B.fund) := measure_mono hsub
      _ ≤ ENNReal.ofReal (GlobalTheory.FlagMeas.kapBd B.I.E p q j) *
            (∫⁻ τ in A ∩ GlobalTheory.FlagMeas.simplexH a, ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ)) *
            μ B.fund := (ENNReal.div_le_iff h0.ne' htop.ne).1 hle
      _ = K * ∫⁻ τ in A ∩ GlobalTheory.FlagMeas.simplexH a, ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ) := by
          rw [hK]; ring
  calc ∫⁻ x in T ∩ B.fund, Φ x ∂μ ≤ ∫⁻ x in T ∩ B.fund, G (s x) ∂μ := h1
    _ = ∫⁻ τ, G τ ∂(Measure.map s (μ.restrict (T ∩ B.fund))) := (lintegral_map hG hs).symm
    _ ≤ ∫⁻ τ, G τ ∂(K • ρ) := lintegral_mono' h2 le_rfl
    _ = K * ∫⁻ τ in GlobalTheory.FlagMeas.simplexH a, G τ * ENNReal.ofReal (GlobalTheory.FlagMeas.dens B.I.n B.I.f j τ) := by
        rw [lintegral_smul_measure, hρ, lintegral_withDensity_eq_lintegral_mul _ hd hG, smul_eq_mul]
        congr 1
        exact lintegral_congr fun τ => mul_comm _ _

end GlobalTheory.FlagPush
