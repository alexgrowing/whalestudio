import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.Groups
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.HaarUniq
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.HaarMap
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

namespace SchurBAux

open Formalism.QuantumDeterminants

theorem conj_cancel {k r : ℕ} {P : Mat k r} (hd : IsUnit P.det) (g : Mat k r) :
    P⁻¹ * (P * g * P⁻¹) * P = g := by
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.nonsing_inv_mul _ hd,
    Matrix.mul_one]

theorem conj_cancel' {k r : ℕ} {P : Mat k r} (hd : IsUnit P.det) (g : Mat k r) :
    P * (P⁻¹ * g * P) * P⁻¹ = g := by
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd, Matrix.mul_nonsing_inv _ hd,
    Matrix.mul_one]

theorem conj_mul {k r : ℕ} {P : Mat k r} (hd : IsUnit P.det) (a b : Mat k r) :
    P * (a * b) * P⁻¹ = (P * a * P⁻¹) * (P * b * P⁻¹) := by
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd]

theorem conj_inUJ {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    {a : Mat k r} (ha : a ∈ UH (Hpk k r)) : Formalism.REAL.inUJ ε (P * a * P⁻¹) := by
  obtain ⟨hPu, hPe⟩ := hP
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hq1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have hq2 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hq1, Matrix.conjTranspose_one]
  show (P * a * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * a * P⁻¹) = Formalism.REAL.Jm ε
  calc (P * a * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * a * P⁻¹)
      = (P⁻¹)ᴴ * (aᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * a) * P⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hPe, ha']
    _ = ((P⁻¹)ᴴ * Pᴴ) * Formalism.REAL.Jm ε * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hq1, hq2, Matrix.one_mul, Matrix.mul_one]

theorem cont_conj {k r : ℕ} (A B : Mat k r) :
    Continuous (fun x : Mt k r => ((A * Matrix.of x * B : Mat k r) : Mt k r)) := by
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem measEmb {k r : ℕ} (ε : Fin (2 * r + k + 1) → Bool) {P : Mat k r} (hd : IsUnit P.det) :
    MeasurableEmbedding (α := Formalism.REAL.UJ ε) (β := Mt k r) (fun g => ((P⁻¹ * Formalism.MainNotions.S.umat g * P : Mat k r) : Mt k r)) := by
  let e : Mt k r ≃ₜ Mt k r :=
    { toFun := fun x => ((P⁻¹ * Matrix.of x * P : Mat k r) : Mt k r)
      invFun := fun x => ((P * Matrix.of x * P⁻¹ : Mat k r) : Mt k r)
      left_inv := fun x => conj_cancel' hd (Matrix.of x)
      right_inv := fun x => conj_cancel hd (Matrix.of x)
      continuous_toFun := cont_conj _ _
      continuous_invFun := cont_conj _ _ }
  have h1 : Topology.IsClosedEmbedding (fun g : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.umat g : Mt k r)) :=
    (Formalism.REAL.isClosedEmbeddingMatrix _ ε).1
  exact (e.isClosedEmbedding.comp h1).measurableEmbedding

end SchurBAux

open Formalism.QuantumDeterminants SchurBAux

theorem schurB : SchurBStatement := by
  intro k r ε lam H _ _ _ σ μG hDSH hH
  obtain ⟨P, ⟨hCay, _⟩, hDS⟩ := hDSH
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hCay.1
  obtain ⟨σ', hσ'⟩ : ∃ σ' : Mat k r → (H →L[ℂ] H), σ' = fun g => σ (P⁻¹ * g * P) := ⟨_, rfl⟩
  rw [← hσ'] at hDS
  have hrep : ∀ g, σ g = σ' (P * g * P⁻¹) := by
    intro g; rw [hσ']; exact (congrArg σ (conj_cancel hd g)).symm
  have uj : ∀ a ∈ UH (Hpk k r), P * a * P⁻¹ ∈ Formalism.MainNotions.S.UJset ε := fun a ha => conj_inUJ hCay ha
  obtain ⟨⟨h1, hmul⟩, hiso, hcont⟩ := hDS.2.2.1
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [hrep, Matrix.mul_one, Matrix.mul_nonsing_inv _ hd]; exact h1
  · intro a ha b hb
    rw [hrep (a * b), hrep a, hrep b, conj_mul hd]
    exact hmul _ (uj a ha) _ (uj b hb)
  · intro g hg v
    rw [hrep]; exact hiso _ (uj g hg) v
  · intro v
    have hc : Continuous (fun g : Mat k r => P * g * P⁻¹) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    refine ((hcont v).comp hc.continuousOn (fun g hg => uj g hg)).congr ?_
    intro g _
    show σ g v = σ' (P * g * P⁻¹) v
    rw [← hrep]
  · obtain ⟨d, hd0, hF⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS lam σ' hDS
    have hmap := haarMap k r ε P hCay
    obtain ⟨c, hc, hμ⟩ := haarUniq2 k r _ _ μG (closedSubgroups k r 0).1 hmap hH
    have hemb := measEmb ε hd
    refine ⟨d / (c : ℝ), div_pos hd0 (by exact_mod_cast hc), fun v w v' w' => ?_⟩
    subst hσ'
    have hint := (hF v w v' w').1
    have hval := (hF v w v' w').2
    rw [hμ]
    refine ⟨((hemb.integrable_map_iff (g := fun x : Mt k r => ⟪w, σ (Matrix.of x) v⟫_ℂ * star ⟪w', σ (Matrix.of x) v'⟫_ℂ)).mpr hint).smul_measure_nnreal, ?_⟩
    calc _ = c • (⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) := by
          rw [integral_smul_nnreal_measure, hemb.integral_map]; exact congrArg (c • ·) hval
      _ = _ := by
          rw [NNReal.smul_def, Complex.real_smul]; push_cast; rw [div_div_eq_mul_div]; ring

end ReciprocityTheory.ChartRestriction.DS.Lap
