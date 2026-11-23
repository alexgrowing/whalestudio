import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RWordRTrAdelic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspFunctionClosedUnderOperations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameHeight

def EntryBd {n : ℕ} (f : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ c : ℝ, ∀ g i j, ‖f g i j‖ ≤ c * (1 + Formalism.REAL.hs g)

variable {n : ℕ} {f : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ}

theorem hs_nonneg (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ Formalism.REAL.hs g := by
  unfold Formalism.REAL.hs; positivity

theorem entryBd_id : EntryBd (fun g : Matrix (Fin n) (Fin n) ℂ => g) := by
  refine ⟨1, fun g i j => ?_⟩
  have h1 : ‖g i j‖ ^ 2 ≤ Formalism.REAL.hs g := by
    unfold Formalism.REAL.hs
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖g i j‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ‖g i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  nlinarith [sq_nonneg (‖g i j‖ - 1), hs_nonneg g]

theorem EntryBd.conjTranspose (h : EntryBd f) : EntryBd fun g => (f g)ᴴ := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun g i j => by simpa [conjTranspose_apply] using hc g j i⟩

theorem EntryBd.const_mul (h : EntryBd f) (P : Matrix (Fin n) (Fin n) ℂ) : EntryBd fun g => P * f g := by
  obtain ⟨c, hc⟩ := h
  refine ⟨(∑ i, ∑ k, ‖P i k‖) * |c|, fun g i j => ?_⟩
  have h0 := hs_nonneg g
  show ‖(P * f g) i j‖ ≤ _
  rw [Matrix.mul_apply]
  calc _ ≤ ∑ k, ‖P i k‖ * (|c| * (1 + Formalism.REAL.hs g)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left ((hc g k j).trans
          (mul_le_mul_of_nonneg_right (le_abs_self c) (by linarith))) (norm_nonneg _)
    _ = (∑ k, ‖P i k‖) * (|c| * (1 + Formalism.REAL.hs g)) := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ k, ‖P i k‖) * (|c| * (1 + Formalism.REAL.hs g)) :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun i => ∑ k, ‖P i k‖)
          (fun _ _ => by positivity) (Finset.mem_univ i)) (by positivity)
    _ = _ := by ring

theorem EntryBd.mul_const (h : EntryBd f) (P : Matrix (Fin n) (Fin n) ℂ) : EntryBd fun g => f g * P := by
  simpa using (h.conjTranspose.const_mul Pᴴ).conjTranspose

theorem frame_mem {D : D7} {V : HSp D} (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau)
    {k : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hk : k ∈ Formalism.MainNotions.S.UJset (A.ε τ)) :
    (A.fr τ)⁻¹ * k * A.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
  have h1 : A.fr τ * (A.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ))
  have hk' : kᴴ * Formalism.REAL.Jm (A.ε τ) * k = Formalism.REAL.Jm (A.ε τ) := hk
  have h3 : ((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  show _ᴴ * _ * _ = _
  rw [← A.fr_gram τ]
  calc _ = (A.fr τ)ᴴ * (kᴴ * (((A.fr τ)⁻¹)ᴴ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) * k) *
        A.fr τ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1, h3, Matrix.mul_one, Matrix.mul_one, hk']

theorem height_elt_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau), ∃ (C : ℝ) (m : ℕ), ∀ g ∈ Formalism.MainNotions.S.UJset (A.ε τ), GlobalTheory.Grow.height V (A.elt θ τ g) ≤ C * (1 + Formalism.REAL.hs g) ^ m := by
  intro D θ hθ V A τ
  obtain ⟨d, hd⟩ := GlobalTheory.Grow.height_le_normInf_pow V hθ
  have b1 := (entryBd_id.const_mul (A.fr τ)⁻¹).mul_const (A.fr τ)
  obtain ⟨c2, h2⟩ := (b1.conjTranspose.const_mul (gramAt D V τ)⁻¹).mul_const (gramAt D V τ)
  obtain ⟨c1, h1⟩ := b1
  refine ⟨(∑ _ρ : D.what₂.Tau, ∑ _i : Fin V.rank, ∑ _j : Fin V.rank, (|c1| + |c2| + 2)) ^ d, d, fun g hg => ?_⟩
  have hu := frame_mem A τ hg
  have s1 := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hu
  have s2 := GlobalTheory.PointAtPlaceHom.isAtTau_inv V τ hu s1
  have h0 := hs_nonneg g
  refine (hd _ s1.1).trans ?_
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by unfold normInf; positivity) ?_ d
  unfold normInf
  simp only [Finset.sum_mul]
  refine Finset.sum_le_sum fun ρ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have a1 := mul_nonneg (abs_nonneg c1) h0
  have a2 := mul_nonneg (abs_nonneg c2) h0
  by_cases e : ρ = τ
  · subst e
    rw [s1.2.1, s2.2.1]
    have e1 := (h1 g i j).trans (mul_le_mul_of_nonneg_right (le_abs_self c1) (by linarith))
    have e2 := (h2 g i j).trans (mul_le_mul_of_nonneg_right (le_abs_self c2) (by linarith))
    nlinarith
  · rw [s1.2.2 ρ e, s2.2.2 ρ e]
    have : ‖(1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) i j‖ ≤ 1 := by
      rw [Matrix.one_apply]; split_ifs <;> simp
    nlinarith [abs_nonneg c1, abs_nonneg c2]

end GlobalTheory.FrameHeight
