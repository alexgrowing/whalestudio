import Mathlib
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.AmapsShExists
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ContractionMapsAtRepresentatives
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryMeasureDatumProductMeasureEqOfSameVectors
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormAdjointCompIsometryEquiv

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.CutBP2

namespace GlobalTheory.WigSh

theorem par_gap_right (P : M.Par) (hP : P.OK) :
    ∀ i ∈ Finset.Icc 1 (P.k - 1), ∃ N : ℕ, P.u' i - P.u' (i + 1) = (N : ℝ) + 1 := by
  intro i hi
  have hi' := Finset.mem_Icc.mp hi
  obtain ⟨a, ha⟩ := hP.int_u' i (Finset.mem_Icc.mpr ⟨hi'.1, by omega⟩)
  obtain ⟨c, hc⟩ := hP.int_u' (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hg := hP.gap i hi
  unfold M.Par.lo M.Par.hi at hg
  have h1 := le_max_right (P.u (i + 1)) (P.u' (i + 1))
  have h2 := min_le_right (P.u i) (P.u' i)
  have h3 : ((1 : ℤ) : ℝ) ≤ ((a - c : ℤ) : ℝ) := by push_cast; linarith
  have h4 : (1 : ℤ) ≤ a - c := by exact_mod_cast h3
  obtain ⟨N, hN⟩ : ∃ N : ℕ, a - c - 1 = (N : ℤ) := ⟨(a - c - 1).toNat, by omega⟩
  refine ⟨N, ?_⟩
  have h5 : ((a - c - 1 : ℤ) : ℝ) = ((N : ℤ) : ℝ) := by rw [hN]
  push_cast at h5
  linarith

theorem amapsShExists : GlobalTheory.WigSh.AmapsShExists := by
  obtain ⟨c₃, hc⟩ := GlobalTheory.WigSh.contraction_maps_at_representatives
  refine ⟨c₃, ?_⟩
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm l n₀ b hpz hpz' hmz hmz' hpπ hmπ
    hpν hpm hmν hmm hl hlk hn hb hnb h1b hup hum
  have h0 := p.hT 0 (Nat.zero_le _)
  have h1 := pp.hT 0 (Nat.zero_le _)
  have h2 := pm.hT 0 (Nat.zero_le _)
  have hp : Q.IsType P.k P.r p.T.base.z' pp.T.base.π' up' := hpz' ▸ pp.hP.2.2.2.2.2.2
  have hm : Q.IsType P.k P.r p.T.base.z' pm.T.base.π' um' := hmz' ▸ pm.hP.2.2.2.2.2.2
  have hμp : pp.T.base.μSS = p.T.base.μSS :=
    GlobalTheory.unitaryMeasureDatum_productMeasure_eq_of_same_vectors Wp Wq Wqp P.k P.r p.T.base pp.T.base hpz hpz' h0.1 h0.2.1 h1.1 h1.2.1
      (h1.2.2.trans h0.2.2.symm)
  have hμm : pm.T.base.μSS = p.T.base.μSS :=
    GlobalTheory.unitaryMeasureDatum_productMeasure_eq_of_same_vectors Wp Wq Wqm P.k P.r p.T.base pm.T.base hmz hmz' h0.1 h0.2.1 h2.1 h2.2.1
      (h2.2.2.trans h0.2.2.symm)
  obtain ⟨Ap', Am', hAp, hAm, hlow⟩ := GlobalTheory.WigSh.exists_wigMap_pair_of_isType Wq Wqp Wqm P.k P.r p.T.base.z'
    p.T.base.π' pp.T.base.π' pm.T.base.π' P.u' up' um' l n₀ b p.T.base.z'_mem p.T.base.T'_pos
    p.hP.2.2.2.2.2.2 (par_gap_right P p.hP.1) hl hlk hn hb hnb h1b hp hm hup hum
  obtain ⟨Ap, Am, ApPt, AmPt, hPp, hPm, hrep, -, hfac, he, hbp, hbm⟩ :=
    hc Wp Wq Wqp Wqm P.k P.r p.T.base pp.T.base pm.T.base p.ν' p.m₀ n₀ b Ap' Am' hpz hpz' hpπ hμp hmz hmz' hmπ hμm
      p.hF hAp hAm hlow
  refine ⟨Ap, Am, ApPt, AmPt, hPp, hPm, hrep, ?_⟩
  intro A₀ f hA₀ hf
  obtain ⟨hfp, hfm⟩ := hfac A₀ f hA₀ hf
  refine ⟨?_, ?_, he, hbp, hbm⟩
  · intro γ hγ hG
    have h := hfp γ hγ hG
    unfold KB.Pl.V
    rw [hpν, hpm]
    exact h
  · intro γ hγ hG
    have h := hfm γ hγ hG
    unfold KB.Pl.V
    rw [hmν, hmm]
    exact h

end GlobalTheory.WigSh
