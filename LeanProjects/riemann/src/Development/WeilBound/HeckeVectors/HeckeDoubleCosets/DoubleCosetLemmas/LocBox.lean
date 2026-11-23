import Development.WeilBound.HeckeVectors.HeckeDoubleCosets.DoubleCosetLemmas.LocMeas

noncomputable section

namespace CompanionTheory.D.Upq.DoubleCosetLemmas

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.LFun GlobalTheory.CompanionTheory.Ipf.Val MeasureTheory
open GlobalTheory.CompanionTheory.QL (bAA bAD bDA bDD chi0 pEl instMeasMat)

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

open Classical in

def gR (y : Cv v) : ℝ := if Valued.v y ≤ 1 then 1 else (absV v y)⁻¹

theorem gR_zero : gR (0 : Cv v) = 1 := by simp [gR]

def wt {a b : ℕ} (y : Matrix (Fin a) (Fin b) (Cv v)) : ℝ := ∏ i, ∏ j, gR (y i j)

def Mono {a b : ℕ} (y : Matrix (Fin a) (Fin b) (Cv v)) : Prop :=
  ∀ i j, y i j ≠ 0 → (∀ j', j' ≠ j → y i j' = 0) ∧ ∀ i', i' ≠ i → y i' j = 0

theorem clopen_le : IsClopen {x : Cv v | Valued.v x ≤ 1} := by
  have := Valued.isClopen_integer (Cv v)
  exact this

variable [MeasurableSpace (Cv v)] [BorelSpace (Cv v)] {μ : Measure (Cv v)}

theorem Pack.line (h : Pack μ) {ι : Type} [Fintype ι] (y : ι → Cv v)
    (hy : ∀ j, y j ≠ 0 → ∀ j', j' ≠ j → y j' = 0) :
    μ {x | Valued.v x ≤ 1 ∧ ∀ j, Valued.v (x * y j) ≤ 1} = ∏ j, ENNReal.ofReal (gR (y j)) := by
  classical
  by_cases h0 : ∀ j, y j = 0
  · simp [h0, gR_zero, h.one]
  push Not at h0
  obtain ⟨j, hj⟩ := h0
  rw [Finset.prod_eq_single j (fun j' _ h' => by simp [hy j hj j' h', gR_zero]) (by simp)]
  have e : {x : Cv v | Valued.v x ≤ 1 ∧ ∀ j, Valued.v (x * y j) ≤ 1} =
      {x | Valued.v x ≤ 1 ∧ Valued.v (x * y j) ≤ 1} := by
    ext x
    refine and_congr_right fun _ => ⟨fun h => h j, fun h j' => ?_⟩
    by_cases h' : j' = j
    · rwa [h']
    · simp [hy j hj j' h']
  rw [e, gR]
  split_ifs with h1
  · rw [ENNReal.ofReal_one, ← h.one]
    congr 1; ext x
    exact ⟨fun h => h.1, fun h => ⟨h, by rw [map_mul]; exact mul_le_one' h h1⟩⟩
  · rw [← mul_one (ENNReal.ofReal _), ← h.one, ← h.scale _ hj _ clopen_le.1.measurableSet]
    congr 1; ext x
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    have h2 : Valued.v x * Valued.v (y j) ≤ 1 := by simpa using h
    exact (le_mul_of_one_le_right' (not_le.1 h1).le).trans h2

def sg (ϖ : Cv v) : ENNReal := ENNReal.ofReal (absV v ϖ⁻¹)⁻¹

end CompanionTheory.D.Upq.DoubleCosetLemmas
