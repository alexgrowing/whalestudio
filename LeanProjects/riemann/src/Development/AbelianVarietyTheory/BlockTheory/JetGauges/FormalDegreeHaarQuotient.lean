import Mathlib
import Formalism.PeriodIntegrals.UpqRep
import Formalism.PeriodIntegrals.IsLowUnitH
import Formalism.PeriodIntegrals.BesselMapUniq
import Formalism.FormalDegreeBessel.StatementG
import Formalism.FormalDegreeBessel.StatementDS
import Formalism.FormalDegreeBessel.StatementBF
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.DecreasingNodeGaps

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient

open Formalism.QuantumDeterminants (Mt lmulM Hpk UH Nset UWset Sset inWb Tz)
open PI.BesselMapUniq (psiGen)

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

variable {k r : ℕ}

def IsClosedMatGroup (U : Set (Mat k r)) : Prop :=
  IsClosed U ∧ (1 : Mat k r) ∈ U ∧ (∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) ∧
    ∀ a ∈ U, IsUnit a.det ∧ a⁻¹ ∈ U

def IsHaarOn (U : Set (Mat k r)) (μ : Measure (Mt k r)) : Prop :=
  μ {x | Matrix.of x ∉ U} = 0 ∧ (∀ a ∈ U, μ.map (lmulM a) = μ) ∧
    (∀ C : Set (Mt k r), IsCompact C → (∀ x ∈ C, Matrix.of x ∈ U) → μ C < ⊤) ∧ μ ≠ 0

def IsQuotRep (G : Set (Mat k r)) (μG μS ν : Measure (Mt k r)) : Prop :=
  ν {x | Matrix.of x ∉ G} = 0 ∧
    ∀ f : Mt k r → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂μG = ∫⁻ g, (∫⁻ s, f (lmulM (Matrix.of s) g) ∂μS) ∂ν

def leviW (k r : ℕ) (s : Mat k r) : Mat k r := fun i j =>
  if (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then s i j
  else if i = j then 1 else 0

section Twist

variable {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

def twist (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (π : Mat k r → (Wp →L[ℂ] Wp)) (s : Mat k r) : Wp →L[ℂ] Wp :=
  psiGen k r z c ((leviW k r s)⁻¹ * s) • π (leviW k r s)

def twistInv (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (π : Mat k r → (Wp →L[ℂ] Wp)) (s : Mat k r) : Wp →L[ℂ] Wp :=
  (psiGen k r z c ((leviW k r s)⁻¹ * s))⁻¹ • π (leviW k r s)⁻¹

def IsEquivariant (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (π : Mat k r → (Wp →L[ℂ] Wp)) (φ : Mat k r → Wp) : Prop :=
  ∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, ∀ g ∈ UH (Hpk k r),
    φ (h * n * g) = psiGen k r z c n • π h (φ g)

def sectionL2NormSq (ν : Measure (Mt k r)) (φ : Mat k r → Wp) : ℝ≥0∞ :=
  ∫⁻ g, ‖φ (Matrix.of g)‖ₑ ^ 2 ∂ν

def IsSquareIntegrableEquivariant (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (π : Mat k r → (Wp →L[ℂ] Wp)) (ν : Measure (Mt k r)) (φ : Mat k r → Wp) : Prop :=
  IsEquivariant k r z c π φ ∧ AEStronglyMeasurable (fun g : Mt k r => φ (Matrix.of g)) ν ∧
    sectionL2NormSq ν φ < ⊤

end Twist

section Period

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

def coefNormSq (μ : Measure (Mt k r)) (σ : Mat k r → (H →L[ℂ] H)) (w : H) : ℝ≥0∞ :=
  ∫⁻ g, ‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ₑ ^ 2 ∂μ

def IsFormalDegreeAt (μ : Measure (Mt k r)) (σ : Mat k r → (H →L[ℂ] H)) (w : H) (d : ℝ) : Prop :=
  w ≠ 0 ∧ 0 < d ∧ coefNormSq μ σ w = ENNReal.ofReal (‖w‖ ^ 4 / d)

def formalDegreeAt (μ : Measure (Mt k r)) (σ : Mat k r → (H →L[ℂ] H)) (w : H) : ℝ :=
  ‖w‖ ^ 4 / (coefNormSq μ σ w).toReal

def periodIntegrand (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (σ : Mat k r → (H →L[ℂ] H)) (π : Mat k r → (Wp →L[ℂ] Wp)) (w v : H) (s : Mt k r) :
    Wp →L[ℂ] Wp :=
  ⟪v, σ (Matrix.of s) w⟫_ℂ • twistInv k r z c π (Matrix.of s)

def period (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    (σ : Mat k r → (H →L[ℂ] H)) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (w v : H) :
    Wp →L[ℂ] Wp :=
  ∫ s, periodIntegrand k r z c σ π w v s ∂μS

end Period

def BesselPeriodNeZero : Prop :=
  ∀ (k r : ℕ) (hk : 2 ≤ k), Even k →
    ∀ (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (u : Fin k → ℝ),
      Formalism.QuantumDeterminants.IsHCParam (DecreasingNodeGaps.param r k (by omega) v b) →
      DecreasingNodeGaps.Interlaces r k (DecreasingNodeGaps.param r k (by omega) v b) u →
      DecreasingNodeGaps.Parity r k (DecreasingNodeGaps.param r k (by omega) v b) u →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)),
      PI.UpqRep.IsDSHpk k r (DecreasingNodeGaps.sign r k (by omega)) (DecreasingNodeGaps.param r k (by omega) v b) σ →
    ∀ (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (π : Mat k r → (Wp →L[ℂ] Wp)),
      PI.UpqRep.IsHCTypeW k r z u π →
    ∀ (c : Fin r → ℂ), (∀ a, c a ≠ 0) →
    ∀ (μS : Measure (Mt k r)), IsHaarOn (Sset k r z) μS →
    ∀ x : H, PI.UpqRep.IsLowUnitH k r (DecreasingNodeGaps.sign r k (by omega))
        (DecreasingNodeGaps.param r k (by omega) v b) σ x →
      ∃ g ∈ UH (Hpk k r), ∃ y ∈ UH (Hpk k r),
        Integrable (periodIntegrand k r z c σ π (σ g x) (σ y x)) μS ∧
          period k r z c σ π μS (σ g x) (σ y x) ≠ 0

theorem col_of_fix {h : Mat k r} {j : Fin (2 * r + k + 1)}
    (hj : h *ᵥ Formalism.QuantumDeterminants.bvec j = Formalism.QuantumDeterminants.bvec j) (i : Fin (2 * r + k + 1)) :
    h i j = if i = j then 1 else 0 := by
  have := congrFun hj i
  simpa [Formalism.QuantumDeterminants.bvec, Matrix.mulVec_single_one, Pi.single_apply] using this

theorem col_out {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z)
    {j : Fin (2 * r + k + 1)} (hj : ¬ (r ≤ j.val ∧ j.val ≤ r + k)) (i : Fin (2 * r + k + 1)) :
    h i j = if i = j then 1 else 0 := by
  apply col_of_fix
  by_cases h1 : j.val < r
  · have := (hh.2.1 ⟨j.val, h1⟩).1
    simpa [Formalism.QuantumDeterminants.eI] using this
  · have h2 : 2 * r + k - j.val < r := by omega
    have := (hh.2.1 ⟨_, h2⟩).2
    have e : Formalism.QuantumDeterminants.esI k r ⟨_, h2⟩ = j := by
      apply Fin.ext; simp only [Formalism.QuantumDeterminants.esI]; omega
    rwa [e] at this

theorem Hpk_row {i i' : Fin (2 * r + k + 1)} (hi : ¬ (r ≤ i.val ∧ i.val ≤ r + k))
    (e : i.val + i'.val = 2 * r + k) (l : Fin (2 * r + k + 1)) :
    Hpk k r i' l = if l = i then 1 else 0 := by
  unfold Hpk
  have := l.isLt
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem row_out {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z)
    {i : Fin (2 * r + k + 1)} (hi : ¬ (r ≤ i.val ∧ i.val ≤ r + k)) (j : Fin (2 * r + k + 1)) :
    h i j = if i = j then 1 else 0 := by
  have hlt := i.isLt
  let i' : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩
  have e : i.val + i'.val = 2 * r + k := by simp only [i']; omega
  have hi' : ¬ (r ≤ i'.val ∧ i'.val ≤ r + k) := by omega
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  have h1 := congrFun (congrFun hU i') j
  have hrow : ∀ m, (hᴴ * Hpk k r) i' m = Hpk k r i' m := by
    intro m
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, col_out hh hi']
    rw [Finset.sum_eq_single i'] <;> simp +contextual
  rw [Matrix.mul_apply] at h1
  simp only [hrow, Hpk_row hi e] at h1
  simpa [eq_comm] using h1

theorem leviW_mul {z : Fin (2 * r + k + 1) → ℂ} {h n : Mat k r} (hh : h ∈ UWset k r z)
    (hn : n ∈ Nset k r) : leviW k r (h * n) = h := by
  funext i j
  unfold leviW
  split_ifs with h1 h2
  · rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hn.2.2 j j h1.2.1 h1.2.2 h1.2.1]; simp
    · intro l _ hl
      by_cases hr : r ≤ l.val
      · rw [hn.2.2 l j h1.2.1 h1.2.2 hr]; simp [hl]
      · rw [col_out hh (j := l) (by omega) i, if_neg, zero_mul]
        rintro rfl
        omega
    · simp
  · subst h2
    rw [col_out hh (j := i) (by tauto) i]; simp
  · by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [row_out hh (i := i) (by tauto) j, if_neg h2]
    · rw [col_out hh hj i, if_neg h2]

theorem isUnit_det_of_mem {h : Mat k r} (hh : h ∈ UH (Hpk k r)) (hH : IsUnit (Hpk k r).det) :
    IsUnit h.det := by
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh
  have := congrArg Matrix.det hU
  rw [Matrix.det_mul] at this
  exact isUnit_of_mul_isUnit_right (this ▸ hH)

theorem twist_mul {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) {h n : Mat k r}
    (hh : h ∈ UWset k r z) (hn : n ∈ Nset k r) (hd : IsUnit h.det) :
    twist k r z c π (h * n) = psiGen k r z c n • π h ∧
      twistInv k r z c π (h * n) = (psiGen k r z c n)⁻¹ • π h⁻¹ := by
  simp only [twist, twistInv, leviW_mul hh hn, Matrix.nonsing_inv_mul_cancel_left h n hd, and_self]

theorem measurable_lmulM (a : Mat k r) : Measurable (lmulM a : Mt k r → Mt k r) := by
  apply Continuous.measurable
  exact continuous_const.matrix_mul continuous_id

example : IsHaarOn ({1, -1} : Set (Mat k r))
    (Measure.dirac (Matrix.of.symm (1 : Mat k r) : Mt k r) + Measure.dirac (Matrix.of.symm (-1 : Mat k r) : Mt k r)) := by
  refine ⟨?_, ?_, fun C _ _ => measure_lt_top _ _, ?_⟩
  · rw [Measure.add_apply, Measure.dirac_apply, Measure.dirac_apply,
      Set.indicator_of_notMem, Set.indicator_of_notMem, add_zero]
    · exact fun h => h (Or.inr rfl)
    · exact fun h => h (Or.inl rfl)
  · intro a ha
    rw [Measure.map_add _ _ (measurable_lmulM a), Measure.map_dirac' (measurable_lmulM a),
      Measure.map_dirac' (measurable_lmulM a)]
    have e1 : lmulM a (Matrix.of.symm (1 : Mat k r) : Mt k r) = Matrix.of.symm a := mul_one a
    have e2 : lmulM a (Matrix.of.symm (-1 : Mat k r) : Mt k r) = Matrix.of.symm (-a) := mul_neg_one a
    rw [e1, e2]
    rcases ha with rfl | rfl
    · rfl
    · rw [neg_neg]
      exact add_comm _ _
  · intro h
    have := congrArg (fun m : Measure (Mt k r) => m Set.univ) h
    simp at this

example (G : Set (Mat k r)) (μ : Measure (Mt k r)) (hμ : IsHaarOn G μ) :
    IsQuotRep G μ (Measure.dirac (Matrix.of.symm (1 : Mat k r) : Mt k r)) μ := by
  refine ⟨hμ.1, fun f _ => ?_⟩
  congr 1
  funext g
  rw [lintegral_dirac]
  exact congrArg f (one_mul (Matrix.of g)).symm

end GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient

end
