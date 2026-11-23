import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianInterpolation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero

set_option autoImplicit false

noncomputable section

open Matrix GlobalTheory.HermFrame
open scoped ComplexOrder

namespace GlobalTheory.CurvInterp

section Pure

variable {e m : ℕ}

def punct (σ : Fin m → Option (Fin e)) (ρ : ℝ) : Set (Fin e → ℂ) :=
  {z | z ∈ Metric.ball (0 : Fin e → ℂ) ρ ∧ ∀ i k, σ i = some k → z k ≠ 0}

open scoped Classical in

def modelGram (σ : Fin m → Option (Fin e)) (z : Fin e → ℂ) : Matrix (Fin e) (Fin e) ℂ :=
  diagonal fun k => ((if ∃ i, σ i = some k then 1 / (‖z k‖ ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tOf (z k) ^ 2) else 1 : ℝ) : ℂ)

def dualRev {q : ℕ} (M : Matrix (Fin q) (Fin q) ℂ) : Matrix (Fin q) (Fin q) ℂ :=
  (GlobalTheory.HermFrame.dualGram M).submatrix Fin.rev Fin.rev

def IsBlockModel {ι : Type} [Fintype ι] {μ : ι → ℕ} (ρ : ℝ) (U : Set (Fin e → ℂ))
    (H : ∀ τ, (Fin e → ℂ) → Matrix (Fin (μ τ)) (Fin (μ τ)) ℂ) : Prop :=
  ∃ (n k : ℕ) (hk : k ≤ n) (g rk : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin k → Matrix (Fin g) (Fin g) ℤ) (φ : (Fin e → ℂ) → Fin n → ℂ)
    (Q : ∀ τ, (Fin e → ℂ) → Matrix (Fin (μ τ)) (Fin g) ℂ) (κ : ι → ℝ),
    GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B ∧ DifferentiableOn ℂ φ (Metric.ball 0 ρ) ∧ φ 0 = 0 ∧
    (∀ z ∈ Metric.ball (0 : Fin e → ℂ) ρ, φ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc n 1) ∧
    (∀ τ i l, DifferentiableOn ℂ (fun z => Q τ z i l) (Metric.ball 0 ρ)) ∧
    Fintype.card (Σ τ, Fin (μ τ)) = g ∧ LinearIndependent ℂ (fun p : Σ τ, Fin (μ τ) => Q p.1 0 p.2) ∧ (∀ τ, 0 < κ τ) ∧
    ∀ z ∈ Metric.ball (0 : Fin e → ℂ) ρ, z ∈ U → φ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured hk 1 ∧
      (∀ τ, H τ z = ((κ τ : ℝ) : ℂ) • (Q τ z * (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram hk τ₀ B (φ z))⁻¹ * (Q τ z)ᴴ)) ∧
      ∀ τ τ', τ ≠ τ' → Q τ z * (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram hk τ₀ B (φ z))⁻¹ * (Q τ' z)ᴴ = 0

theorem isOpen_punct (σ : Fin m → Option (Fin e)) (ρ : ℝ) : IsOpen (punct σ ρ) := by
  have : punct σ ρ = Metric.ball 0 ρ ∩ ⋂ i, ⋂ k, {z | σ i = some k → z k ≠ 0} := by
    ext z; simp [punct]
  rw [this]
  refine Metric.isOpen_ball.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => ?_)
  by_cases h : σ i = some k
  · simpa [h] using isOpen_ne_fun (continuous_apply k) continuous_const
  · simp [h]

theorem punct_mono (σ : Fin m → Option (Fin e)) {ρ ρ' : ℝ} (h : ρ ≤ ρ') : punct σ ρ ⊆ punct σ ρ' :=
  fun _ hz => ⟨Metric.ball_subset_ball h hz.1, hz.2⟩

theorem modelGram_posSemidef (σ : Fin m → Option (Fin e)) (z : Fin e → ℂ) : (modelGram σ z).PosSemidef := by
  rw [modelGram, posSemidef_diagonal_iff]
  intro k
  rw [Complex.zero_le_real]
  split_ifs <;> positivity

theorem form_modelGram (σ : Fin m → Option (Fin e)) (z w : Fin e → ℂ) :
    (form (modelGram σ z) w w).re = GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.modelAt σ z w := by
  classical
  rw [form_eq_sum, GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.modelAt, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k (fun l _ hl => by simp [modelGram, diagonal_apply_ne _ hl.symm, diagonal_apply_ne _ hl]) (by simp)]
  have h : ∀ c : ℝ, (w k * (c : ℂ) * (starRingEnd ℂ) (w k)).re = c * ‖w k‖ ^ 2 := fun c => by
    rw [mul_right_comm, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re, mul_comm]
  simp only [modelGram, diagonal_apply_eq]
  split_ifs
  · rw [h]; ring
  · rw [h]; ring

example : IsBlockModel (e := 1) (ι := Unit) (μ := fun _ => 1) 1 {z | z 0 ≠ 0}
    (fun _ z => (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram (le_refl 1) (fun _ => 0) (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℤ)) z)⁻¹) := by
  refine ⟨1, 1, le_rfl, 1, 1, fun _ => 0, fun _ => 1, id, fun _ _ => 1, fun _ => 1, ?_, differentiableOn_id, rfl, ?_,
    fun _ _ _ => differentiableOn_const _, by simp, ?_, fun _ => one_pos, fun z hz hU => ⟨⟨?_, fun i => ?_⟩, by simp, by simp⟩⟩
  · refine ⟨le_rfl, fun _ _ => differentiableOn_const _, fun _ _ => isSymm_zero, fun _ => by simpa using PosSemidef.one,
      fun i j k h => ?_, ?_, fun z _ => ?_⟩
    · have := j.2; have := k.2; omega
    · convert (PosDef.one : (1 : Matrix {j : Fin 1 // j.val < 1} {j : Fin 1 // j.val < 1} ℝ).PosDef)
      ext a b
      rw [Subsingleton.elim a b]
      simp
    · have : IsEmpty {j : Fin 1 // 1 ≤ j.val} := ⟨fun j => by have := j.1.2; have := j.2; omega⟩
      convert (PosDef.one : (1 : Matrix {j : Fin 1 // 1 ≤ j.val} {j : Fin 1 // 1 ≤ j.val} ℝ).PosDef)
      exact Subsingleton.elim _ _
  · exact fun z hz k => (norm_le_pi_norm z k).trans_lt (mem_ball_zero_iff.1 hz)
  · have : Subsingleton (Σ _ : Unit, Fin 1) := ⟨fun ⟨_, a⟩ ⟨_, b⟩ => by rw [Subsingleton.elim a b]⟩
    refine (linearIndependent_subsingleton_index_iff _).2 ?_
    rintro ⟨_, i⟩ h
    simpa using congrFun h i
  · exact fun k => (norm_le_pi_norm z k).trans_lt (mem_ball_zero_iff.1 hz)
  · rw [Subsingleton.elim (Fin.castLE _ i) 0]; exact hU

end Pure

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O

def HodgeLocal {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s)
    (σ : κ.c.F →+* ℂ) : Prop :=
  ∀ (e : ℕ) (B : Set (Fin e → ℂ)) (a : (Fin e → ℂ) → CxFr s.T.Z σ), IsOpen B → 0 ∈ B → HolFam B a →
    ContinuousOn (fun z => (a z).1) B → ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball 0 ρ ⊆ B ∧
      IsBlockModel ρ {z | Inner (a z).1} fun τ z => ((x.hodge σ).gram (a z).1 (a z).2 τ)ᵀ

def rootGen {D : D7} (O : Setup D) (c : O.s.Comp)
    (t : ∀ τ : D.host.E →+* ℂ, Fin (O.S.Dw.mult τ) → (O.var c).Fnˣ) (y : DV.Rt D.what₂.Tau O.N) : (O.var c).Fn :=
  (((prodPow t (O.ex y))⁻¹ : (O.var c).Fnˣ) : (O.var c).Fn)

end GlobalTheory.CurvInterp
