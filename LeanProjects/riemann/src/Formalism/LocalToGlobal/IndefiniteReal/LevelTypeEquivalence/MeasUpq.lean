import Formalism.LocalRingCardinality.SpanPowerMembership.HaarDensityNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarScaling.MapEqSelfOfIterate
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodGA
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MinfLev
import Formalism.LocalToGlobal.IndefiniteReal.HaarTransfer.MinfUniqueP

noncomputable section

open MeasureTheory Filter Topology Formalism.BasicNotions

namespace Formalism.IndefR.Eqv.MU

def epsPQ (p q : ℕ) : Fin (p + q) → Bool := fun i => (finSumFinEquiv.symm i).isLeft

def phiPQ (p q : ℕ) : UpqT p q ≃ₜ* Formalism.REAL.UJ (epsPQ p q) :=
  PI.UnitaryGroupMassFormula.CdHaarScale.Main.phi finSumFinEquiv (fun i => by simp [epsPQ]) (fun j => by simp [epsPQ])

instance instSCUpq (p q : ℕ) : SecondCountableTopology (UpqT p q) :=
  (phiPQ p q).toHomeomorph.secondCountableTopology

instance instTGUpq (p q : ℕ) : IsTopologicalGroup (UpqT p q) :=
  inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq p q))

instance instBorelUpq (p q : ℕ) : BorelSpace (UpqT p q) := ⟨rfl⟩

instance instT2SpaceIndefiniteUnitary (p q : ℕ) : T2Space (UpqT p q) := inferInstanceAs (T2Space (Formalism.UG.Upq p q))

theorem upq_rightInv (p q : ℕ) (μ : Measure (UpqT p q)) (hμ : μ.IsHaarMeasure) : μ.IsMulRightInvariant :=
  Leaf.Proofs.transferStatement_holds (Formalism.REAL.UJ (epsPQ p q)) (UpqT p q) (phiPQ p q).symm
    (fun ν hν => uJ_rightInv (epsPQ p q) ν hν) μ hμ

theorem map_conj_upq {p q : ℕ} (m : Measure (UpqT p q)) [m.IsHaarMeasure] (u : UpqT p q) :
    m.map (fun c => u⁻¹ * c * u) = m := by
  have hR := upq_rightInv p q m inferInstance
  have e : (fun c : UpqT p q => u⁻¹ * c * u) = (fun c => c * u) ∘ (fun c => u⁻¹ * c) := rfl
  rw [e, ← Measure.map_map (measurable_mul_const u) (measurable_const_mul u⁻¹),
    Measure.IsMulLeftInvariant.map_mul_left_eq_self (μ := m) u⁻¹, hR.map_mul_right_eq_self]

theorem omegaLeb_unique {p q : ℕ} {lam lam' : Measure (lieU p q)} (h : IsOmegaLeb lam) (h' : IsOmegaLeb lam') :
    lam' = lam := by
  have := h.1
  have := h'.1
  set a := Measure.addHaarScalarFactor lam' lam
  have hs : lam' = (a : ENNReal) • lam := by
    rw [← ENNReal.smul_def]; exact Measure.isAddLeftInvariant_eq_smul lam' lam
  have e2 := h'.2
  rw [hs, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul, h.2] at e2
  have hpos : 0 < (volume : Measure ((Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) → ℂ)) (Metric.ball 0 1) :=
    Metric.isOpen_ball.measure_pos _ ⟨0, Metric.mem_ball_self one_pos⟩
  have hfin : (volume : Measure ((Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) → ℂ)) (Metric.ball 0 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have e3 := congrArg (fun ν : Measure ((Fin p ⊕ Fin q) × (Fin p ⊕ Fin q) → ℂ) => ν (Metric.ball 0 1)) e2
  simp only [Measure.smul_apply, smul_eq_mul] at e3
  have e4 : (a : ENNReal) * a = 1 := (ENNReal.mul_left_inj hpos.ne' hfin).mp (e3.trans (one_mul _).symm)
  have e5 : a = 1 := by
    have h2 : a ^ 2 = 1 := by
      rw [sq]; exact_mod_cast e4
    exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).mp h2
  rw [hs, e5, ENNReal.coe_one, one_smul]

theorem isMinf_unique {p q : ℕ} {m m' : Measure (UpqT p q)} (h : Lev.IsMinf m) (h' : Lev.IsMinf m') : m' = m := by
  obtain ⟨hm, lam, hlam, hl⟩ := h
  obtain ⟨hm', lam', hlam', hl'⟩ := h'
  rw [omegaLeb_unique hlam hlam'] at hl'
  set k := Measure.haarScalarFactor m' m
  have hs : m' = (k : ENNReal) • m := by
    rw [← ENNReal.smul_def]; exact Measure.isMulLeftInvariant_eq_smul m' m
  have h2 := ENNReal.Tendsto.const_mul hl (Or.inr (ENNReal.coe_ne_top (r := k)))
  have h3 : Tendsto (fun r : ℝ => m' {g | ∃ X ∈ ballU p q r, UpqT.mat g =
      NormedSpace.exp (X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)} / lam (ballU p q r)) (𝓝[>] 0)
      (𝓝 ((k : ENNReal) * Formalism.L2.Theta.minfDensity (p + q))) := by
    refine h2.congr fun r => ?_
    rw [hs, Measure.smul_apply, smul_eq_mul, mul_div_assoc]
  have e := tendsto_nhds_unique hl' h3
  have hk : (k : ENNReal) = 1 :=
    (ENNReal.mul_left_inj (minfDensity_ne_zero (p + q)) (minfDensity_ne_top (p + q))).mp
      (e.symm.trans (one_mul _).symm)
  rw [hs, hk, one_smul]

theorem isMinf_exists (p q : ℕ) : ∃ m : Measure (UpqT p q), Lev.IsMinf m :=
  Leaf.Proofs.exists_haar_measure_with_density p q _ (minfDensity_ne_zero (p + q)) (minfDensity_ne_top (p + q))

theorem Jpq_zero_left (q : ℕ) : Formalism.UG.Jpq 0 q = -1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · exact i.elim0
  · exact i.elim0
  · exact j.elim0
  · simp [Formalism.UG.Jpq, Matrix.one_apply, Matrix.neg_apply]

instance instCompactUpq0 (q : ℕ) : CompactSpace (UpqT 0 q) := by
  have hc := Formalism.UG.P.isCompact_units_of_unitary (n := Fin 0 ⊕ Fin q)
    (T := {M : Matrix (Fin 0 ⊕ Fin q) (Fin 0 ⊕ Fin q) ℂ | star M * M = 1})
    (isClosed_eq (continuous_star.mul continuous_id) continuous_const) (fun _ h => h)
  have e : (Formalism.UG.Upq 0 q : Set (GL (Fin 0 ⊕ Fin q) ℂ)) =
      {g : GL (Fin 0 ⊕ Fin q) ℂ | (g : Matrix _ _ ℂ) ∈ {M : Matrix (Fin 0 ⊕ Fin q) (Fin 0 ⊕ Fin q) ℂ | star M * M = 1}} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_setOf_eq]
    rw [Formalism.UG.P.mem_Upq_iff, Jpq_zero_left]
    constructor
    · intro h
      have := congrArg Neg.neg h
      simpa [Matrix.mul_neg] using this
    · intro h
      simp [Matrix.mul_neg, h]
  rw [← e] at hc
  exact isCompact_iff_compactSpace.mp hc

theorem prob_exists {p q : ℕ} [CompactSpace (UpqT p q)] :
    ∃ m : Measure (UpqT p q), m.IsHaarMeasure ∧ IsProbabilityMeasure m := by
  refine ⟨(Measure.haar (G := UpqT p q) Set.univ)⁻¹ • Measure.haar, ?_, ?_⟩
  · have h0 : (Measure.haar (G := UpqT p q) Set.univ) ≠ 0 := (Measure.measure_univ_pos.mpr (NeZero.ne _)).ne'
    have ht : (Measure.haar (G := UpqT p q) Set.univ) ≠ ⊤ := measure_ne_top _ _
    exact Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.mpr ht) (ENNReal.inv_ne_top.mpr h0)
  · constructor
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel]
    · exact (Measure.measure_univ_pos.mpr (NeZero.ne _)).ne'
    · exact measure_ne_top _ _

theorem prob_unique {p q : ℕ} {m m' : Measure (UpqT p q)} (h : m.IsHaarMeasure ∧ IsProbabilityMeasure m)
    (h' : m'.IsHaarMeasure ∧ IsProbabilityMeasure m') : m' = m := by
  obtain ⟨hm, hp⟩ := h
  obtain ⟨hm', hp'⟩ := h'
  have hs : m' = (Measure.haarScalarFactor m' m : ENNReal) • m := by
    rw [← ENNReal.smul_def]; exact Measure.isMulLeftInvariant_eq_smul m' m
  have e := congrArg (fun ν : Measure (UpqT p q) => ν Set.univ) hs
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] at e
  rw [hs, ← e, one_smul]

end Formalism.IndefR.Eqv.MU

end
