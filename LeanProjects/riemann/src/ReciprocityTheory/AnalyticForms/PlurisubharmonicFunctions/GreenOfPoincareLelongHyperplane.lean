import Mathlib
import ReciprocityTheory.AnalyticForms.MaIntEmpty

namespace ReciprocityTheory.AnForm.A

open MeasureTheory

open scoped ContDiff

noncomputable section

def hypIncl {n : ℕ} (w : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  Fin.cons (0 : ℂ) w

theorem hypIncl_zero {n : ℕ} (w : Fin n → ℂ) : hypIncl w 0 = 0 := rfl

def PoincareLelongData {n : ℕ} (U : Set (Fin (n + 1) → ℂ)) (v : (Fin (n + 1) → ℂ) → ℝ)
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) : Prop :=
  IsOpen U ∧ ContDiff ℝ 3 v ∧ HasCompactSupport v ∧ tsupport v ⊆ U ∧
    ∀ k, ContDiffOn ℝ ∞ (φ k) U

def densV {n : ℕ} (v : (Fin (n + 1) → ℂ) → ℝ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ)
    (z : Fin (n + 1) → ℂ) : ℝ :=
  maDens (D := n + 1) (Fin.cons v φ) z

def densHyp {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (w : Fin n → ℂ) : ℝ :=
  maDens (D := n) (fun k => φ k ∘ hypIncl) w

def PoincareLelongHyperplane : Prop :=
  ∀ (n : ℕ) (U : Set (Fin (n + 1) → ℂ)) (v : (Fin (n + 1) → ℂ) → ℝ)
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ), PoincareLelongData U v φ →
    Integrable (fun z => Real.log ‖z 0‖ * densV v φ z) volume ∧
    Integrable (fun w => v (hypIncl w) * densHyp φ w) volume ∧
    ∫ z, Real.log ‖z 0‖ * densV v φ z = ∫ w, v (hypIncl w) * densHyp φ w

def PoincareLelongUnitPower : Prop :=
  ∀ (n : ℕ) (m : ℤ) (U : Set (Fin (n + 1) → ℂ)) (v : (Fin (n + 1) → ℂ) → ℝ)
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (u : (Fin (n + 1) → ℂ) → ℂ), PoincareLelongData U v φ →
    DifferentiableOn ℂ u U → (∀ z ∈ U, u z ≠ 0) →
    Integrable (fun z => Real.log ‖z 0 ^ m * u z‖ * densV v φ z) volume ∧
    ∫ z, Real.log ‖z 0 ^ m * u z‖ * densV v φ z = (m : ℝ) * ∫ w, v (hypIncl w) * densHyp φ w

def hypInclAt {n : ℕ} (i : Fin (n + 1)) (w : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  Fin.insertNth (α := fun _ => ℂ) i 0 w

def densHypAt {n : ℕ} (i : Fin (n + 1)) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (w : Fin n → ℂ) : ℝ :=
  maDens (D := n) (fun k => φ k ∘ hypInclAt i) w

def PoincareLelongNormalCrossing : Prop :=
  ∀ (n : ℕ) (m : Fin (n + 1) → ℤ) (U : Set (Fin (n + 1) → ℂ)) (v : (Fin (n + 1) → ℂ) → ℝ)
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (u : (Fin (n + 1) → ℂ) → ℂ), PoincareLelongData U v φ →
    DifferentiableOn ℂ u U → (∀ z ∈ U, u z ≠ 0) →
    Integrable (fun z => Real.log ‖u z * ∏ i, z i ^ m i‖ * densV v φ z) volume ∧
    ∫ z, Real.log ‖u z * ∏ i, z i ^ m i‖ * densV v φ z =
      ∑ i, (m i : ℝ) * ∫ w, v (hypInclAt i w) * densHypAt i φ w

theorem hypInclAt_zero {n : ℕ} (w : Fin n → ℂ) : hypInclAt 0 w = hypIncl w := by
  funext j
  simp [hypInclAt, hypIncl, Fin.insertNth_zero']

theorem exists_poincareLelongData {n : ℕ} (U : Set (Fin (n + 1) → ℂ)) (hU : IsOpen U) (z : Fin (n + 1) → ℂ)
    (hz : z ∈ U) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (hφ : ∀ k, ContDiffOn ℝ ∞ (φ k) U) :
    ∃ v : (Fin (n + 1) → ℂ) → ℝ, PoincareLelongData U v φ ∧ v z = 1 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z hz
  let f : ContDiffBump z := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  refine ⟨f, ⟨hU, f.contDiff, f.hasCompactSupport, ?_, hφ⟩,
    f.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))⟩
  rw [f.tsupport_eq]
  exact (Metric.closedBall_subset_ball (by linarith : ε / 2 < ε)).trans hball

theorem green_of_poincareLelongHyperplane (h : PoincareLelongHyperplane) (u : (Fin 1 → ℂ) → ℝ) (hu : ContDiff ℝ 3 u)
    (hcs : HasCompactSupport u) :
    Integrable (fun z : Fin 1 → ℂ => Real.log ‖z 0‖ * ReciprocityTheory.AnForm.maDens ![u] z) ∧
      ∫ z : Fin 1 → ℂ, Real.log ‖z 0‖ * ReciprocityTheory.AnForm.maDens ![u] z = u 0 := by
  obtain ⟨h1, -, h3⟩ := h 0 Set.univ u Fin.elim0
    ⟨isOpen_univ, hu, hcs, Set.subset_univ _, fun k => k.elim0⟩
  have hv : densV u (Fin.elim0 : Fin 0 → (Fin 1 → ℂ) → ℝ) = ReciprocityTheory.AnForm.maDens ![u] := by
    funext z; rfl
  rw [hv] at h1 h3
  refine ⟨h1, ?_⟩
  rw [h3]
  have hw : ∀ w : Fin 0 → ℂ,
      u (hypIncl w) * densHyp (Fin.elim0 : Fin 0 → (Fin 1 → ℂ) → ℝ) w = u 0 := by
    intro w
    have e1 : hypIncl w = 0 := by
      funext j
      refine Fin.cases rfl (fun i => i.elim0) j
    have e2 : densHyp (Fin.elim0 : Fin 0 → (Fin 1 → ℂ) → ℝ) w = 1 := by
      simp [densHyp, ReciprocityTheory.AnForm.maDens, ReciprocityTheory.AnForm.mdisc]
    rw [e1, e2, mul_one]
  simp_rw [hw]
  simp [MeasureTheory.integral_const, MeasureTheory.volume_pi, MeasureTheory.measureReal_def,
    MeasureTheory.Measure.pi_univ]

end

end ReciprocityTheory.AnForm.A
