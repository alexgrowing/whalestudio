import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeDeepQ
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLevelGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.NatSmulMulEq
import Formalism.FlagUnipotentLattices.CuspThresholdBound

noncomputable section

namespace Formalism.MainNotions.BridgeVolRatio

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates Formalism.MainNotions.BridgeDeepQ
open scoped ENNReal TensorProduct

def GaugeVolumeBoundVar (X : CData) (C0 : ℝ) : Prop :=
  X.I.vol X.μf X.fund / ((X.μf X.I.Kset).toReal * X.I.gaugeU) ≤ cn_Y X ^ (C0 * (X.I.n : ℝ) ^ 2 * (X.I.f : ℝ))

theorem one_le_rd (I : AutInst) : 1 ≤ I.rd := by
  unfold AutInst.rd
  have hd : (1 : ℝ) ≤ |(NumberField.discr I.E : ℝ)| := by
    have h0 : NumberField.discr I.E ≠ 0 := NumberField.discr_ne_zero I.E
    have : (1 : ℤ) ≤ |NumberField.discr I.E| := Int.one_le_abs h0
    exact_mod_cast this
  exact Real.one_le_rpow hd (by positivity)

theorem one_le_f (I : AutInst) : 1 ≤ I.f := Module.finrank_pos

theorem kg_pos_fin (X : CData) (hH : X.μf.IsHaarMeasure) {g : ℕ} (hg : 1 ≤ g) :
    0 < X.μf (X.I.Kg g) ∧ X.μf X.I.Kset < ∞ := by
  have hopen : IsOpen (X.I.Kg g) := X.I.topf_open g hg
  have hne : (X.I.Kg g).Nonempty := ⟨1, by
    refine ⟨?_, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
    · show ((1 : X.I.Gf) : GL (Fin X.I.n) (X.I.E ⊗[X.I.F] Af X.I.F)) ∈ Formalism.UG.stabGL X.I.Lf
      rw [OneMemClass.coe_one]
      exact (Formalism.UG.stabGL X.I.Lf).one_mem
    · simp [AutInst.fmat]⟩
  refine ⟨hopen.measure_pos X.μf hne, ?_⟩
  exact (PI.WAU.Cpt.isCompact_Kset X.I).measure_lt_top

theorem kg_sub (I : AutInst) (g : ℕ) : I.Kg g ⊆ I.Kset := fun _ hx => hx.1

theorem vol_ratio_of_gauge_volume (hGD : ∀ (n : ℕ) (ε : Fin n → Bool), Gauge.GaugeDens ε) {C0 : ℝ} (X : CData) {n₀ : ℕ} {A : ℝ}
    (hn₀ : 1 ≤ n₀) (hX : X.HypB n₀ A) (hV : GaugeVolumeBoundVar X C0) : VolRatio X (C0 + 2) := by
  obtain ⟨hset, hcount, -⟩ := hX
  have hH : X.μf.IsHaarMeasure := hcount.2.2.2.1
  have hn : 1 ≤ X.I.n := le_trans hn₀ hset.1
  have hb : (2 : ℝ) ≤ X.b := hset.2.2.1
  have hg : 1 ≤ X.g := hset.2.2.2.2.2.2.2.1
  obtain ⟨hpos, hfin⟩ := kg_pos_fin X hH hg
  have hKg_fin : X.μf (X.I.Kg X.g) < ∞ := lt_of_le_of_lt (measure_mono (kg_sub X.I X.g)) hfin
  have hK_pos : 0 < X.μf X.I.Kset := lt_of_lt_of_le hpos (measure_mono (kg_sub X.I X.g))
  set μK := (X.μf X.I.Kset).toReal with hμK
  set μKg := (X.μf (X.I.Kg X.g)).toReal with hμKg
  have hμK0 : 0 < μK := ENNReal.toReal_pos hK_pos.ne' hfin.ne
  have hμKg0 : 0 < μKg := ENNReal.toReal_pos hpos.ne' hKg_fin.ne
  have hU : 0 < X.I.gaugeU := Finset.prod_pos fun v _ => (hGD _ (X.I.ε v)).2

  have hidx : μK ≤ ((X.g : ℝ) ^ (2 * X.I.n ^ 2 * X.I.f)) * μKg := by
    have h := Formalism.MainNotions.BridgeLevelGen.levelIdx X.I X.μf hg
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hKg_fin.ne) h
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h2
    simpa [hμK, hμKg] using h2
  have hvolK : (μKg / μK)⁻¹ ≤ (X.g : ℝ) ^ (2 * X.I.n ^ 2 * X.I.f) := by
    rw [inv_div, div_le_iff₀ hμKg0]; exact hidx
  have hlev := Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts.volLevel C0 X.I.n X.I.f X.I.rd (X.g : ℝ) X.b
    (X.I.vol X.μf X.fund / (μK * X.I.gaugeU)) (μKg / μK) hn (one_le_f X.I) (one_le_rd X.I)
    (by exact_mod_cast hg) hb (div_pos hμKg0 hμK0) hV hvolK
  refine ⟨mul_pos hμKg0 hU, ?_⟩
  have e : X.I.vol X.μf X.fund / X.I.volKg X.μf X.g =
      X.I.vol X.μf X.fund / (μK * X.I.gaugeU) / (μKg / μK) := by
    unfold AutInst.volKg
    rw [← hμKg]
    field_simp
  rw [e]
  exact hlev

end Formalism.MainNotions.BridgeVolRatio

end
