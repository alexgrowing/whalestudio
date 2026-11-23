import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

variable {k r : ℕ}

def opBase (k r : ℕ) (T' : ℝ) : Fin (2 * r + k + 1) → ℂ := (Real.sqrt T' : ℂ) • wLast k r

def opCo (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : (Fin k → ℂ) × ℂ :=
  (fun i => v (wI k r (Fin.castSucc i)), v (wI k r (Fin.last k)))

def opOrb (k r : ℕ) (T' : ℝ) (x : Mt k r) : (Fin k → ℂ) × ℂ := opCo k r (Matrix.of x *ᵥ opBase k r T')

def opVec (k r : ℕ) (p : (Fin k → ℂ) × ℂ) : Fin (2 * r + k + 1) → ℂ := fun i =>
  if h : r ≤ i.val ∧ i.val < r + k then p.1 ⟨i.val - r, by omega⟩
  else if i.val = r + k then p.2 else 0

def opAct (k r : ℕ) (s : Mat k r) (p : (Fin k → ℂ) × ℂ) : (Fin k → ℂ) × ℂ := opCo k r (s *ᵥ opVec k r p)

def hypS (k : ℕ) (T' : ℝ) : Set ((Fin k → ℂ) × ℂ) :=
  {p | ∑ i, Complex.normSq (p.1 i) - Complex.normSq p.2 = -T'}

def hypPar (k : ℕ) (T' : ℝ) (q : EuclideanSpace ℂ (Fin k) × ℝ) : (Fin k → ℂ) × ℂ :=
  (fun i => q.1 i, (Real.sqrt (‖q.1‖ ^ 2 + T') : ℂ) * Complex.exp (q.2 * Complex.I))

def hypM (k : ℕ) (T' : ℝ) : Measure ((Fin k → ℂ) × ℂ) :=
  (1 / 2 : ℝ≥0∞) • (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))).map (hypPar k T')

abbrev TrE (k : ℕ) := EuclideanSpace ℝ (Option (Fin k × Bool))

def opBeta (k : ℕ) (q : TrE k) (a : Fin k) : ℂ :=
  ((q (some (a, false)) : ℂ) + (q (some (a, true)) : ℂ) * Complex.I) / (Real.sqrt 2 : ℂ)

def opGen (k r : ℕ) (q : TrE k) : Mat k r := fun i j =>
  if hi : r ≤ i.val ∧ i.val < r + k then (if j.val = r + k then opBeta k q ⟨i.val - r, by omega⟩ else 0)
  else if i.val = r + k then
    (if hj : r ≤ j.val ∧ j.val < r + k then star (opBeta k q ⟨j.val - r, by omega⟩)
     else if j.val = r + k then (q none : ℂ) * Complex.I else 0)
  else 0

def opE (k r : ℕ) (T' : ℝ) (ρ : ℝ) : Set ((Fin k → ℂ) × ℂ) :=
  (fun q : TrE k => opCo k r (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T')) '' Metric.ball 0 ρ

def tVol (k : ℕ) (ρ : ℝ) : ℝ := (volume (Metric.ball (0 : TrE k) ρ)).toReal

def HypInv : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' → ∀ s ∈ UWb k r, (hypM k T').map (opAct k r s) = hypM k T'

def OrbRepY : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' → ∀ νg : Measure (Mt k r), IsGaugeOn k r (UWb k r) νg →
    ∀ Q : Measure ((Fin k → ℂ) × ℂ), (∀ s ∈ UWb k r, Q.map (opAct k r s) = Q) → Q (hypS k T')ᶜ = 0 →
      (∀ C, IsCompact C → Q C < ⊤) → ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ Q = c • νg.map (opOrb k r T')

def GaugeK : Prop :=
  ∀ k r : ℕ, 1 ≤ k → ∃ νK : Measure (Mt k r), IsGaugeOn k r (UWset k r (wLast k r)) νK

def TubeLimK : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' → ∀ νg νK : Measure (Mt k r), IsGaugeOn k r (UWb k r) νg →
    IsGaugeOn k r (UWset k r (wLast k r)) νK →
    Tendsto (fun ρ : ℝ => (νg (opOrb k r T' ⁻¹' opE k r T' ρ)).toReal / tVol k ρ) (𝓝[>] 0)
      (𝓝 (νK Set.univ).toReal)

def HypLocal : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' →
    Tendsto (fun ρ : ℝ => (hypM k T' (opE k r T' ρ)).toReal / tVol k ρ) (𝓝[>] 0) (𝓝 (T' ^ k / 2 ^ (k + 1)))

def OpEMeas : Prop :=
  ∀ (k r : ℕ) (T' : ℝ) (ρ : ℝ), MeasurableSet (opE k r T' ρ)

def HypLF : Prop :=
  ∀ (k : ℕ) (T' : ℝ), 0 < T' → hypM k T' (hypS k T')ᶜ = 0 ∧ ∀ C, IsCompact C → hypM k T' C < ⊤

theorem op_volU_pos (j : ℕ) : 0 < volU j :=
  Finset.prod_pos fun i _ => div_pos (pow_pos (by positivity) _) (Nat.cast_pos.mpr (Nat.factorial_pos i))

theorem continuous_opOrb (T' : ℝ) : Continuous (opOrb k r T') := by
  have h : Continuous fun x : PI.RhsWLim.Mt k r => Matrix.of x *ᵥ opBase k r T' :=
    Continuous.matrix_mulVec (by exact continuous_id) continuous_const
  unfold opOrb opCo
  exact (continuous_pi fun i => (continuous_apply (PI.RhsWLim.wI k r (Fin.castSucc i))).comp h).prodMk
    ((continuous_apply (PI.RhsWLim.wI k r (Fin.last k))).comp h)

theorem continuous_hypPar (k : ℕ) (T' : ℝ) : Continuous (hypPar k T') := by
  unfold hypPar
  fun_prop

theorem hypMeas_eq (k : ℕ) (T' : ℝ) {f : (Fin k → ℂ) × ℂ → ℝ≥0∞} (hf : Measurable f) :
    hypMeas k T' f = ∫⁻ p, f p ∂hypM k T' := by
  have hm : Measurable (hypPar k T') := (continuous_hypPar k T').measurable
  unfold hypM hypMeas
  rw [lintegral_smul_measure, smul_eq_mul, lintegral_map hf hm,
    lintegral_prod (fun a => f (hypPar k T' a)) (hf.comp hm).aemeasurable]
  rfl

theorem orbitPush_of (h2 : GaugeVolUk) (hK : GaugeK) (hT : TubeLimK) (hI : HypInv) (hR : OrbRepY)
    (hL : HypLocal) (hE : OpEMeas) (hF : HypLF) : OrbitPush := by
  intro k r T' hk hT' νg hνg f hf
  obtain ⟨νK, hνK⟩ := hK k r hk
  obtain ⟨c, hctop, hc⟩ := hR k r T' hk hT' νg hνg (hypM k T')
    (hI k r T' hk hT') (hF k T' hT').1 (hF k T' hT').2
  have hmeas : Measurable (opOrb k r T') := (continuous_opOrb T').measurable
  have hU : 0 < PI.RhsWLim.volU k := op_volU_pos k
  have hK1 : (νK Set.univ).toReal = PI.RhsWLim.volU k := by
    rw [h2 k r νK hνK, ENNReal.toReal_ofReal hU.le]
  have hlim1 := hT k r T' hk hT' νg νK hνg hνK
  rw [hK1] at hlim1
  have hlim2 := hL k r T' hk hT'
  have heqfun : (fun ρ : ℝ => (hypM k T' (opE k r T' ρ)).toReal / tVol k ρ) =
      fun ρ => c.toReal * ((νg (opOrb k r T' ⁻¹' opE k r T' ρ)).toReal / tVol k ρ) := by
    funext ρ
    rw [hc, Measure.smul_apply, Measure.map_apply hmeas (hE k r T' ρ), smul_eq_mul, ENNReal.toReal_mul,
      mul_div_assoc]
  rw [heqfun] at hlim2
  have hkey : T' ^ k / 2 ^ (k + 1) = c.toReal * PI.RhsWLim.volU k :=
    tendsto_nhds_unique hlim2 (hlim1.const_mul c.toReal)
  have hRHS : hypMeas k T' f = c * ∫⁻ p, f p ∂(νg.map (opOrb k r T')) := by
    rw [hypMeas_eq k T' hf, hc, lintegral_smul_measure, smul_eq_mul]
  show ∫⁻ x, f (opOrb k r T' x) ∂νg = _
  rw [← lintegral_map hf hmeas, hRHS, ← mul_assoc]
  have hX : PI.RhsWLim.volU k * 2 ^ (k + 1) / T' ^ k * c.toReal = 1 := by
    have hT'k : (0 : ℝ) < T' ^ k := pow_pos hT' k
    rw [show PI.RhsWLim.volU k * 2 ^ (k + 1) / T' ^ k * c.toReal =
        2 ^ (k + 1) / T' ^ k * (c.toReal * PI.RhsWLim.volU k) by ring, ← hkey]
    field_simp
  have hcc : c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hctop).symm
  rw [hcc, ← ENNReal.ofReal_mul (div_pos (mul_pos hU (by positivity)) (pow_pos hT' k)).le, hX,
    ENNReal.ofReal_one, one_mul]

end PI.RhsWLim.W
