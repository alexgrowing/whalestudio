import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.BesselSplit
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MomSchurG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundOfCompact
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.HaarCompactGrowth.GrowthSphericalBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReproducingFormulaReduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace Formalism.L2.S.Pv.PeriodG

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.BesselSplit

variable {k r : ℕ}

theorem psiGen_cont (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) :
    Continuous (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => psiGen k r z c g) := by
  unfold psiGen ellA
  refine Continuous.cexp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_finsetSum _ fun a _ => continuous_const.mul ?_))))
  by_cases hP : a.val + 1 < r
  · simp only [hP, dite_true]
    exact continuous_apply_apply _ _
  · simp only [hP, dite_false]
    have hm : Continuous (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => g *ᵥ z) :=
      continuous_id.matrix_mulVec continuous_const
    exact (continuous_apply (eI k r a)).comp hm

theorem norm_psiGen (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ‖psiGen k r z c g‖ = 1 := by
  unfold psiGen
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem inv_eq_of_uh {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  refine Matrix.inv_eq_left_inv ?_
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', WeylGroupFacts.hpk_sq]

section Period

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]

def sWN (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Set (Mt k r × Mt k r) :=
  {p | Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ Nset k r}

theorem measurableSet_sWN (z : Fin (2 * r + k + 1) → ℂ) : MeasurableSet (sWN k r z) :=
  ((Formalism.MainNotions.BridgeCSB.isClosed_UW z).measurableSet.preimage measurable_fst).inter
    ((Formalism.MainNotions.BridgeCSB.isClosed_N).measurableSet.preimage measurable_snd)

theorem ae_sWN {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z) μW)
    (hN : IsHaarOn (Nset k r) μN) : ∀ᵐ p ∂(μW.prod μN), p ∈ sWN k r z := by
  have : SigmaFinite μW := hW.1
  have : SigmaFinite μN := hN.1
  have h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := by rw [ae_iff]; simpa using hW.2.2.1
  have h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r := by rw [ae_iff]; simpa using hN.2.2.1
  have g1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := Measure.QuasiMeasurePreserving.ae
    (Measure.quasiMeasurePreserving_fst) h1
  have g2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := Measure.QuasiMeasurePreserving.ae
    (Measure.quasiMeasurePreserving_snd) h2
  filter_upwards [g1, g2] with p hp1 hp2
  exact ⟨hp1, hp2⟩

theorem beInt_contOn {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (UH (Hpk k r)) σ) {z : Fin (2 * r + k + 1) → ℂ}
    {π : Mat k r → (Vp →L[ℂ] Vp)} (hπc : ContinuousOn π (UWset k r z)) (c : Fin r → ℂ) (v v' : H) :
    ContinuousOn (beInt σ π (psiGen k r z c) v v') (sWN k r z) := by
  have hmul : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 * Matrix.of p.2 : Mat k r)) :=
    Continuous.matrix_mul continuous_fst continuous_snd
  have f1 : ContinuousOn (fun p : Mt k r × Mt k r => σ (Matrix.of p.1 * Matrix.of p.2) v) (sWN k r z) :=
    (hσ.2.2 v).comp hmul.continuousOn (fun p hp => WeylGroupFacts.uh_mul hp.1.1 hp.2.1)
  have f2 : ContinuousOn (fun p : Mt k r × Mt k r => ⟪v', σ (Matrix.of p.1 * Matrix.of p.2) v⟫_ℂ) (sWN k r z) :=
    continuousOn_const.inner f1
  have f3 : Continuous (fun p : Mt k r × Mt k r => star (psiGen k r z c (Matrix.of p.2))) :=
    continuous_star.comp ((psiGen_cont z c).comp continuous_snd)
  have hinvc : Continuous (fun p : Mt k r × Mt k r => (Hpk k r * (Matrix.of p.1)ᴴ * Hpk k r : Mat k r)) :=
    (continuous_const.matrix_mul (continuous_fst.matrix_conjTranspose)).matrix_mul continuous_const
  have f4' : ContinuousOn (fun p : Mt k r × Mt k r => π (Hpk k r * (Matrix.of p.1)ᴴ * Hpk k r)) (sWN k r z) :=
    hπc.comp hinvc.continuousOn (fun p hp => by
      rw [← inv_eq_of_uh hp.1.1]; exact WeylGroupFacts.uw_inv hp.1)
  have f4 : ContinuousOn (fun p : Mt k r × Mt k r => π (Matrix.of p.1)⁻¹) (sWN k r z) :=
    f4'.congr (fun p hp => by simp only; rw [inv_eq_of_uh hp.1.1])
  exact (f2.mul f3.continuousOn).smul f4

end Period

section Period2

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]

theorem periodContG_at {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    {z : Fin (2 * r + k + 1) → ℂ} (c : Fin r → ℂ) {u : Fin k → ℝ} {π : Mat k r → (Vp →L[ℂ] Vp)}
    {μW μN μG νq : Measure (Mt k r)} {h : ℝ} (m : ℕ)
    (hlam : IsHCParam lam) (hσ : IsDSHpk k r ε lam σ) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hπ : IsHCTypeW k r z u π) (hW : IsHaarOn (UWset k r z) μW) (hN : IsHaarOn (Nset k r) μN)
    (hG : IsHaarOn (UH (Hpk k r)) μG) (hq : IsQuotMeas μG (muS μW μN) νq)
    (hgap : GapAtLeast ε lam h) (hm : ReciprocityTheory.ChartRestriction.DS.thrStar ε + m < h) (hmA : Formalism.FourierDecayAlt.ThreeDimData.AG k r < m) :
    (∀ v ∈ smoothVecs (k := k) (r := r) σ, ∀ v' ∈ smoothVecs (k := k) (r := r) σ,
      Integrable (beInt σ π (psiGen k r z c) v v') (μW.prod μN)) ∧
    (∀ v' ∈ smoothVecs (k := k) (r := r) σ,
      IsCWCont (k := k) (r := r) σ (fun v => beOp μW μN σ π (psiGen k r z c) v v')) ∧
    (∀ v ∈ smoothVecs (k := k) (r := r) σ,
      IsCWCont (k := k) (r := r) σ (fun v' => beOp μW μN σ π (psiGen k r z c) v v')) := by
  obtain ⟨C, Ws, hWs, hdec⟩ := ReciprocityTheory.ChartRestriction.DS.DecInf.decSm hlam hgap m hm hσ
  have hσU : IsURepOn (UH (Hpk k r)) σ := Formalism.MainNotions.LowestKTypeMultiplicity.urep_of_DS hσ
  obtain ⟨-, hπiso, hπc⟩ := Formalism.MainNotions.LowestKTypeMultiplicity.rp_repOfHC k r z u Vp π hz hT hπ
  have hgr : Integrable (fun p : Mt k r × Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-(m : ℝ)))
      (μW.prod μN) := Formalism.FourierDecayAlt.P.growth_spherical_bound k r z μW μN μG νq (m : ℝ) hz hT hW hN hG hq hmA
  set S : H → ℝ := fun v => (Ws.map fun w => ‖dsigW (k := k) (r := r) σ w v‖).sum with hS
  have hS0 : ∀ v, 0 ≤ S v := fun v => List.sum_nonneg (by
    intro x hx; obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _)
  have hbd : ∀ v ∈ smoothVecs (k := k) (r := r) σ, ∀ v' ∈ smoothVecs (k := k) (r := r) σ,
      ∀ p ∈ sWN k r z, ‖beInt σ π (psiGen k r z c) v v' p‖ ≤
        C * S v * S v' * Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-(m : ℝ)) := by
    intro v hv v' hv' p hp
    have hg : (Matrix.of p.1 * Matrix.of p.2 : Mat k r) ∈ UH (Hpk k r) := WeylGroupFacts.uh_mul hp.1.1 hp.2.1
    have hgpos : 0 < Formalism.FourierDecayAlt.B.gN (k := k) (r := r) (Matrix.of p.1 * Matrix.of p.2) := Formalism.FourierDecayAlt.P.B6.gN_pos hg
    have h1 := hdec v hv v' hv' _ hg
    have hinv : ((Matrix.of p.1 : Mat k r))⁻¹ ∈ UWset k r z := WeylGroupFacts.uw_inv hp.1
    have hπn : ‖π ((Matrix.of p.1 : Mat k r))⁻¹‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by rw [hπiso _ hinv x, one_mul])
    unfold beInt
    rw [norm_smul, norm_mul, norm_star, norm_psiGen, mul_one]
    have hrp : Formalism.FourierDecayAlt.B.gN (k := k) (r := r) (Matrix.of p.1 * Matrix.of p.2) ^ (-(m : ℝ)) =
        (Formalism.FourierDecayAlt.B.gN (k := k) (r := r) (Matrix.of p.1 * Matrix.of p.2) ^ m)⁻¹ := by
      rw [Real.rpow_neg hgpos.le, Real.rpow_natCast]
    rw [hrp]
    have hgm : 0 < Formalism.FourierDecayAlt.B.gN (k := k) (r := r) (Matrix.of p.1 * Matrix.of p.2) ^ m := pow_pos hgpos m
    have h2 : ‖⟪v', σ (Matrix.of p.1 * Matrix.of p.2) v⟫_ℂ‖ ≤
        C * S v * S v' * (Formalism.FourierDecayAlt.B.gN (k := k) (r := r) (Matrix.of p.1 * Matrix.of p.2) ^ m)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hgm, mul_comm]
      exact h1
    calc ‖⟪v', σ (Matrix.of p.1 * Matrix.of p.2) v⟫_ℂ‖ * ‖π ((Matrix.of p.1 : Mat k r))⁻¹‖
        ≤ ‖⟪v', σ (Matrix.of p.1 * Matrix.of p.2) v⟫_ℂ‖ * 1 := mul_le_mul_of_nonneg_left hπn (norm_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact h2
  have hae := ae_sWN hW hN
  have hint : ∀ v ∈ smoothVecs (k := k) (r := r) σ, ∀ v' ∈ smoothVecs (k := k) (r := r) σ,
      Integrable (beInt σ π (psiGen k r z c) v v') (μW.prod μN) := by
    intro v hv v' hv'
    refine Integrable.mono' (hgr.const_mul (C * S v * S v')) ?_ ?_
    · exact Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.aesm_of_contOn (beInt_contOn hσU hπc c v v') (measurableSet_sWN z) hae
    · filter_upwards [hae] with p hp
      exact hbd v hv v' hv' p hp
  set I := ∫ p, Formalism.FourierDecayAlt.B.gN (k := k) (r := r) (Matrix.of p.1 * Matrix.of p.2) ^ (-(m : ℝ)) ∂(μW.prod μN) with hI
  have hnorm : ∀ v ∈ smoothVecs (k := k) (r := r) σ, ∀ v' ∈ smoothVecs (k := k) (r := r) σ,
      ‖beOp μW μN σ π (psiGen k r z c) v v'‖ ≤ C * S v * S v' * I := by
    intro v hv v' hv'
    unfold beOp
    rw [hI, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hgr.const_mul _) (by filter_upwards [hae] with p hp; exact hbd v hv v' hv' p hp)
  refine ⟨hint, fun v' hv' => ⟨C * S v' * I, Ws, fun w hw X hX => (hWs w hw).2 X hX, fun v hv => ?_⟩,
    fun v hv => ⟨C * S v * I, Ws, fun w hw X hX => (hWs w hw).2 X hX, fun v' hv' => ?_⟩⟩
  · calc ‖beOp μW μN σ π (psiGen k r z c) v v'‖ ≤ C * S v * S v' * I := hnorm v hv v' hv'
      _ = C * S v' * I * S v := by ring
  · calc ‖beOp μW μN σ π (psiGen k r z c) v v'‖ ≤ C * S v * S v' * I := hnorm v hv v' hv'
      _ = C * S v * I * S v' := by ring

end Period2

theorem thrStar_le {n : ℕ} (ε : Fin n → Bool) :
    ReciprocityTheory.ChartRestriction.DS.thrStar ε ≤ (n : ℝ) ^ 3 + 16 * (n : ℝ) ^ 2 + 16 * (n : ℝ) + 8 := by
  unfold ReciprocityTheory.ChartRestriction.DS.thrStar
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have hp : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) ≤ n := by
    have : ReciprocityTheory.ChartRestriction.DS.pOf ε ≤ n := by
      unfold ReciprocityTheory.ChartRestriction.DS.pOf
      exact (Finset.card_le_univ _).trans (Fintype.card_fin n).le
    exact_mod_cast this
  have hq : (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ n := by
    have : ReciprocityTheory.ChartRestriction.DS.qOf ε ≤ n := by
      unfold ReciprocityTheory.ChartRestriction.DS.qOf
      exact (Finset.card_le_univ _).trans (Fintype.card_fin n).le
    exact_mod_cast this
  have hq0 : (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ n := by
    have h0 : ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε := min_le_left _ _
    have h0' : (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε := by exact_mod_cast h0
    linarith
  have hq00 : (0 : ℝ) ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := Nat.cast_nonneg _
  have hs : √(2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)) ≤ n + 1 := by
    calc √(2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)) ≤ √(((n : ℝ) + 1) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = n + 1 := Real.sqrt_sq (by linarith)
  have hpq : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * ReciprocityTheory.ChartRestriction.DS.qOf ε ≤ n * n :=
    mul_le_mul hp hq (Nat.cast_nonneg _) hn
  apply max_le
  · nlinarith [mul_le_mul_of_nonneg_left hpq hn]
  · nlinarith [mul_le_mul_of_nonneg_left hq0 hn]

theorem exponent_ok (k r : ℕ) {h : ℝ} (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (ε : Fin (2 * r + k + 1) → Bool) :
    ∃ m : ℕ, Formalism.FourierDecayAlt.ThreeDimData.AG k r < m ∧ ReciprocityTheory.ChartRestriction.DS.thrStar ε + m < h := by
  obtain ⟨hk, hh, -, -⟩ := hok
  refine ⟨⌊Formalism.FourierDecayAlt.ThreeDimData.AG k r⌋₊ + 1, ?_, ?_⟩
  · push_cast
    exact Nat.lt_floor_add_one _
  · have h1 := thrStar_le ε
    have hAGv : Formalism.FourierDecayAlt.ThreeDimData.AG k r = 4 * ((k : ℝ) + r) * (r + 1) := rfl
    have hAG : (0 : ℝ) ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
      rw [hAGv]
      positivity
    have hfl : (⌊Formalism.FourierDecayAlt.ThreeDimData.AG k r⌋₊ : ℝ) ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := Nat.floor_le hAG
    push_cast at hh h1 ⊢
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hr : (0 : ℝ) ≤ r := r.cast_nonneg
    set x : ℝ := 2 * (r : ℝ) + k + 1 with hx
    have hx2 : 2 ≤ x := by linarith
    have hkr : ((k : ℝ) + r) * (r + 1) ≤ x * x :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have hAGle : Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 4 * (x * x) := by
      rw [hAGv]
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hx2 (by positivity : (0 : ℝ) ≤ x * x),
      mul_le_mul_of_nonneg_left hx2 (by positivity : (0 : ℝ) ≤ x)]

end Formalism.L2.S.Pv.PeriodG
