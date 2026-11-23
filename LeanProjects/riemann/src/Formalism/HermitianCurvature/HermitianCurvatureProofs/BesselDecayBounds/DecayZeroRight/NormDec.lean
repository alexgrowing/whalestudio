import Formalism.HermitianCurvature.HermitianCurvatureProofs.MajorantEstimate
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.SharpRestriction.CuspSpanNormBounds.ExpansionFromLemmaB
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselBoundFamilyOfDoubleCoset

open Matrix
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.InverseNormDecayBounds

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma₄

def NormInvP : Prop :=
  ∀ k r : ℕ, (∀ x ∈ UH (Hpk k r), Formalism.FourierDecayAlt.B.gN x⁻¹ = Formalism.FourierDecayAlt.B.gN x ∧ 1 ≤ Formalism.FourierDecayAlt.B.gN x) ∧
    ∀ x y : Formalism.FourierDecayAlt.B.Mat k r, Formalism.FourierDecayAlt.B.gN (x * y) ≤ Formalism.FourierDecayAlt.B.gN x * Formalism.FourierDecayAlt.B.gN y

theorem normInvP : NormInvP := fun k r => by
  refine ⟨fun x hx => Formalism.FourierDecayAlt.P.norm_of_inverse k r x hx, fun x y => ?_⟩
  letI : SeminormedAddCommGroup (Formalism.FourierDecayAlt.B.Mat k r) := Matrix.frobeniusSeminormedAddCommGroup
  have h : ∀ z : Formalism.FourierDecayAlt.B.Mat k r, Formalism.FourierDecayAlt.B.gN z = ‖z‖ := by
    intro z
    rw [Formalism.FourierDecayAlt.B.gN, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
    simp only [Complex.normSq_eq_norm_sq]
    norm_num
  rw [h, h, h]
  exact Matrix.frobenius_norm_mul x y

variable {k r : ℕ}

theorem gN_rpow_le {x y g : Formalism.FourierDecayAlt.B.Mat k r} (hx : x ∈ UH (Hpk k r)) (hy : y ∈ UH (Hpk k r))
    (hg : g ∈ UH (Hpk k r)) {a : ℝ} (ha : 0 ≤ a) :
    Formalism.FourierDecayAlt.B.gN (y⁻¹ * x * g) ^ (-a) ≤
      (Formalism.FourierDecayAlt.B.gN y * Formalism.FourierDecayAlt.B.gN g) ^ a * Formalism.FourierDecayAlt.B.gN x ^ (-a) := by
  obtain ⟨hinvP, hsub⟩ := normInvP k r
  have hyy : y * y⁻¹ = 1 := Matrix.mul_nonsing_inv y (isUnit_of_uh hy)
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g (isUnit_of_uh hg)
  have hx_eq : x = y * (y⁻¹ * x * g) * g⁻¹ := by
    calc x = (y * y⁻¹) * x * (g * g⁻¹) := by rw [hyy, hgg, Matrix.one_mul, Matrix.mul_one]
      _ = y * (y⁻¹ * x * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
  have h1y := (hinvP y hy).2
  have h1g := (hinvP g hg).2
  have h1x := (hinvP x hx).2
  have hpos : 0 < Formalism.FourierDecayAlt.B.gN y * Formalism.FourierDecayAlt.B.gN g := by positivity
  have hle : Formalism.FourierDecayAlt.B.gN x / (Formalism.FourierDecayAlt.B.gN y * Formalism.FourierDecayAlt.B.gN g) ≤ Formalism.FourierDecayAlt.B.gN (y⁻¹ * x * g) := by
    rw [div_le_iff₀ hpos]
    calc Formalism.FourierDecayAlt.B.gN x = Formalism.FourierDecayAlt.B.gN (y * (y⁻¹ * x * g) * g⁻¹) := by rw [← hx_eq]
      _ ≤ Formalism.FourierDecayAlt.B.gN (y * (y⁻¹ * x * g)) * Formalism.FourierDecayAlt.B.gN g⁻¹ := hsub _ _
      _ ≤ Formalism.FourierDecayAlt.B.gN y * Formalism.FourierDecayAlt.B.gN (y⁻¹ * x * g) * Formalism.FourierDecayAlt.B.gN g⁻¹ :=
          mul_le_mul_of_nonneg_right (hsub _ _) (Real.sqrt_nonneg _)
      _ = Formalism.FourierDecayAlt.B.gN (y⁻¹ * x * g) * (Formalism.FourierDecayAlt.B.gN y * Formalism.FourierDecayAlt.B.gN g) := by
          rw [(hinvP g hg).1]
          ring
  have hA : 0 < Formalism.FourierDecayAlt.B.gN x := by linarith
  calc Formalism.FourierDecayAlt.B.gN (y⁻¹ * x * g) ^ (-a)
      ≤ (Formalism.FourierDecayAlt.B.gN x / (Formalism.FourierDecayAlt.B.gN y * Formalism.FourierDecayAlt.B.gN g)) ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos (div_pos hA hpos) hle (neg_nonpos.mpr ha)
    _ = (Formalism.FourierDecayAlt.B.gN y * Formalism.FourierDecayAlt.B.gN g) ^ a * Formalism.FourierDecayAlt.B.gN x ^ (-a) := by
        rw [Real.div_rpow hA.le hpos.le, Real.rpow_neg hpos.le, div_inv_eq_mul, mul_comm]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def DecBd (σ : Formalism.FourierDecayAlt.B.Mat k r → (H →L[ℂ] H)) (a : ℝ) (u' u : H) : Prop :=
  ∃ C : ℝ, ∀ x ∈ UH (Hpk k r), ‖⟪u', σ x u⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN x ^ (-a)

theorem decBd_zero_right (σ : Formalism.FourierDecayAlt.B.Mat k r → (H →L[ℂ] H)) (a : ℝ) (u' : H) : DecBd σ a u' 0 := ⟨0, fun x _ => by simp⟩

theorem decBd_zero_left (σ : Formalism.FourierDecayAlt.B.Mat k r → (H →L[ℂ] H)) (a : ℝ) (u : H) : DecBd σ a 0 u := ⟨0, fun x _ => by simp⟩

theorem decBd_add_right {σ : Formalism.FourierDecayAlt.B.Mat k r → (H →L[ℂ] H)} {a : ℝ} {u' u1 u2 : H}
    (h1 : DecBd σ a u' u1) (h2 : DecBd σ a u' u2) : DecBd σ a u' (u1 + u2) := by
  obtain ⟨C1, h1⟩ := h1
  obtain ⟨C2, h2⟩ := h2
  refine ⟨C1 + C2, fun x hx => ?_⟩
  rw [map_add, inner_add_right, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (h1 x hx) (h2 x hx))

theorem decBd_add_left {σ : Formalism.FourierDecayAlt.B.Mat k r → (H →L[ℂ] H)} {a : ℝ} {u1 u2 u : H}
    (h1 : DecBd σ a u1 u) (h2 : DecBd σ a u2 u) : DecBd σ a (u1 + u2) u := by
  obtain ⟨C1, h1⟩ := h1
  obtain ⟨C2, h2⟩ := h2
  refine ⟨C1 + C2, fun x hx => ?_⟩
  rw [inner_add_left, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (h1 x hx) (h2 x hx))

theorem decBd_smul_right {σ : Formalism.FourierDecayAlt.B.Mat k r → (H →L[ℂ] H)} {a : ℝ} {u' u : H} (c : ℂ)
    (h : DecBd σ a u' u) : DecBd σ a u' (c • u) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨‖c‖ * C, fun x hx => ?_⟩
  rw [map_smul, inner_smul_right, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg _)

theorem decBd_smul_left {σ : Formalism.FourierDecayAlt.B.Mat k r → (H →L[ℂ] H)} {a : ℝ} {u' u : H} (c : ℂ)
    (h : DecBd σ a u' u) : DecBd σ a (c • u') u := by
  obtain ⟨C, hC⟩ := h
  refine ⟨‖c‖ * C, fun x hx => ?_⟩
  rw [inner_smul_left, norm_mul, RCLike.norm_conj, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg _)

def DiagonalMatrixCoefficientPowerDecay (σ : Formalism.FourierDecayAlt.B.Mat k r → (H →L[ℂ] H)) (w0 : H) (a : ℝ) : Prop :=
  ∃ C : ℝ, ∀ x ∈ UH (Hpk k r), ‖⟪w0, σ x w0⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN x ^ (-a)

variable [CompleteSpace H] {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}

theorem decBd_gen {σ : Formalism.FourierDecayAlt.B.Mat k r → (H →L[ℂ] H)} (hσ : IsDSHpk k r ε lam σ) {w0 : H} {a : ℝ}
    (ha : 0 ≤ a) (hD : DiagonalMatrixCoefficientPowerDecay σ w0 a) {y g : Formalism.FourierDecayAlt.B.Mat k r} (hy : y ∈ UH (Hpk k r))
    (hg : g ∈ UH (Hpk k r)) : DecBd σ a (σ y w0) (σ g w0) := by
  obtain ⟨C, hC⟩ := hD
  have hmul := (Formalism.MainNotions.LeviCoordinates.discrete_series_unitary_rep hσ).2.1
  refine ⟨max C 0 * (Formalism.FourierDecayAlt.B.gN y * Formalism.FourierDecayAlt.B.gN g) ^ a, fun x hx => ?_⟩
  have hyi := uh_inv hy
  have hz : y⁻¹ * x * g ∈ UH (Hpk k r) := uh_mul (uh_mul hyi hx) hg
  have heq : ⟪σ y w0, σ x (σ g w0)⟫_ℂ = ⟪w0, σ (y⁻¹ * x * g) w0⟫_ℂ := by
    have hyy : (y⁻¹)⁻¹ = y := Matrix.nonsing_inv_nonsing_inv y (isUnit_of_uh hy)
    have h1 := Formalism.MainNotions.DiscreteSeriesInnerProducts.ds_inv_adj hσ hyi w0 (σ x (σ g w0))
    rw [hyy] at h1
    rw [h1, hmul _ (uh_mul hyi hx) _ hg, hmul _ hyi _ hx]
    rfl
  rw [heq]
  calc ‖⟪w0, σ (y⁻¹ * x * g) w0⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN (y⁻¹ * x * g) ^ (-a) := hC _ hz
    _ ≤ max C 0 * Formalism.FourierDecayAlt.B.gN (y⁻¹ * x * g) ^ (-a) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
    _ ≤ max C 0 * ((Formalism.FourierDecayAlt.B.gN y * Formalism.FourierDecayAlt.B.gN g) ^ a * Formalism.FourierDecayAlt.B.gN x ^ (-a)) :=
        mul_le_mul_of_nonneg_left (gN_rpow_le hx hy hg ha) (le_max_right _ _)
    _ = max C 0 * (Formalism.FourierDecayAlt.B.gN y * Formalism.FourierDecayAlt.B.gN g) ^ a * Formalism.FourierDecayAlt.B.gN x ^ (-a) := by ring

theorem decDD {σ : Formalism.FourierDecayAlt.B.Mat k r → (H →L[ℂ] H)} (hσ : IsDSHpk k r ε lam σ) {w0 : H} {a : ℝ}
    (ha : 0 ≤ a) (hD : DiagonalMatrixCoefficientPowerDecay σ w0 a) :
    ∀ u ∈ DDsp σ w0, ∀ u' ∈ DDsp σ w0, DecBd σ a u' u := by
  intro u hu u' hu'
  unfold DDsp at hu hu'
  induction hu using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨g, hg, rfl⟩ := hv
    induction hu' using Submodule.span_induction with
    | mem v' hv' =>
      obtain ⟨y, hy, rfl⟩ := hv'
      exact decBd_gen hσ ha hD hy hg
    | zero => exact decBd_zero_left σ a _
    | add a1 a2 _ _ h1 h2 => exact decBd_add_left h1 h2
    | smul c a1 _ h1 => exact decBd_smul_left c h1
  | zero => exact decBd_zero_right σ a u'
  | add a1 a2 _ _ h1 h2 => exact decBd_add_right h1 h2
  | smul c a1 _ h1 => exact decBd_smul_right c h1

end Formalism.MainNotions.InverseNormDecayBounds
