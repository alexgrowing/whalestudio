import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeCoordinateRatioBoundedStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem unip_mul_diag_cone : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (t : ℝ), 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → r j / r i ≤ C ∧ ∀ z : BlockIx a j → Cinf E, ∃ z' : BlockIx a j → Cinf E, ‖z'‖ ≤ C * (r j / r i) * ‖z‖ ∧ ∀ τ : ℝ, unip (τ • z) * d = d * unip (τ • z') := by
  intro E _ _ _ a t ht i j hij
  obtain ⟨C0, hC0, hb⟩ := GlobalTheory.T.cone_coordinate_ratio_bounded a t ht
  refine ⟨C0 * C0 + C0, by positivity, ?_⟩
  intro r d hr hcone hd
  have hij' : i ≤ j := by rw [Fin.le_def]; omega
  have hji : r j / r i ≤ C0 := hb r hr hcone i j hij'
  have hji0 : 0 ≤ r j / r i := (div_pos (hr j) (hr i)).le
  refine ⟨by nlinarith, fun z => ?_⟩
  refine ⟨fun p => (r p.1.2 / r p.1.1) • z p, ?_, ?_⟩
  · have hX : 0 ≤ (C0 * C0 + C0) * (r j / r i) := by positivity
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun p => ?_
    have hk : p.1.1 ≤ i := by rw [Fin.le_def]; have := p.2.1; omega
    have hl : j ≤ p.1.2 := by rw [Fin.le_def]; exact p.2.2
    have h1 : r p.1.2 / r j ≤ C0 := hb r hr hcone j p.1.2 hl
    have h3 : r i / r p.1.1 ≤ C0 := hb r hr hcone p.1.1 i hk
    have hpos : 0 < r p.1.2 / r p.1.1 := div_pos (hr _) (hr _)
    have heq : r p.1.2 / r p.1.1 = (r p.1.2 / r j) * (r j / r i) * (r i / r p.1.1) := by
      have := hr j; have := hr i; have := hr p.1.1
      field_simp
    have hbd : r p.1.2 / r p.1.1 ≤ (C0 * C0 + C0) * (r j / r i) := by
      rw [heq]
      have e1 : 0 ≤ r p.1.2 / r j := (div_pos (hr _) (hr _)).le
      have e3 : 0 ≤ r i / r p.1.1 := (div_pos (hr _) (hr _)).le
      calc r p.1.2 / r j * (r j / r i) * (r i / r p.1.1) ≤ C0 * (r j / r i) * C0 := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right h1 hji0) h3 e3 (by positivity)
        _ ≤ (C0 * C0 + C0) * (r j / r i) := by nlinarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    exact mul_le_mul hbd (norm_le_pi_norm z p) (norm_nonneg _) hX
  · intro τ
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hd]
    change (1 + nilM (τ • z)) * _ = _ * (1 + nilM (τ • fun p => (r p.1.2 / r p.1.1) • z p))
    ext k l w
    rw [add_mul, mul_add, one_mul, mul_one, Matrix.add_apply, Matrix.add_apply, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    congr 1
    simp only [nilM, Matrix.of_apply]
    split_ifs with h
    · simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul, add_right_inj]
      have := hr k
      have hk0 : (r k : ℂ) ≠ 0 := by exact_mod_cast this.ne'
      push_cast
      field_simp
    · simp

end GlobalTheory
