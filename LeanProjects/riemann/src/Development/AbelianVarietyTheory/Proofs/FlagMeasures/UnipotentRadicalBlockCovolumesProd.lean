import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN.Covol

theorem sum_UTr_fst (r : ℕ) (u : Fin r → ℝ) :
    ∑ p : UTr r, u p.1.1 = ∑ a : Fin r, ((r - 1 - (a : ℕ) : ℕ) : ℝ) * u a := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun x : Fin r × Fin r => x.1 < x.2)) (by simp)
    (fun x => u x.1)]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_filter]
  dsimp only
  rw [Finset.sum_const, nsmul_eq_mul, ← Fin.card_Ioi]
  congr 3
  ext b; simp

theorem sum_UTr_snd (r : ℕ) (v : Fin r → ℝ) :
    ∑ p : UTr r, v p.1.2 = ∑ b : Fin r, ((b : ℕ) : ℝ) * v b := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun x : Fin r × Fin r => x.1 < x.2)) (by simp)
    (fun x => v x.2)]
  rw [Finset.sum_filter, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_filter]
  dsimp only
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [← Fin.card_Iio b]; congr 1; ext a; simp

theorem sum_UTr (r : ℕ) (u v : Fin r → ℝ) :
    ∑ p : UTr r, (u p.1.1 + v p.1.2) =
      ∑ a : Fin r, (((r - 1 - (a : ℕ) : ℕ) : ℝ) * u a + ((a : ℕ) : ℝ) * v a) := by
  rw [Finset.sum_add_distrib, sum_UTr_fst, sum_UTr_snd, ← Finset.sum_add_distrib]

theorem sum_fin_quad (r : ℕ) (c₀ c₁ c₂ : ℝ) :
    ∑ a : Fin r, (c₀ + c₁ * ((a : ℕ) : ℝ) + c₂ * ((a : ℕ) : ℝ) ^ 2) =
      c₀ * r + c₁ * (r * (r - 1) / 2) + c₂ * ((r - 1) * r * (2 * r - 1) / 6) := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => c₀ + c₁ * (i : ℝ) + c₂ * (i : ℝ) ^ 2) r]
  induction r with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

end GlobalTheory.SnMass.VolN.Covol

namespace GlobalTheory.SnMass.VolN

open Covol in

theorem covol_blocks_prod : ∀ (d : ℝ) (f k r : ℕ) (s : Fin r → ℝ), 0 < d → (∀ a, 0 < s a) → (2 : ℝ) ^ (f * (r * (r - 1) + r * (k + 1))) * ((∏ p : UTr r, (2⁻¹ : ℝ) ^ f * d ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) + 2 * ((r - p.1.2.val : ℕ) : ℝ)) * (s p.1.1 / s p.1.2) ^ (2 * f)) * (∏ a : Fin r, ((2⁻¹ : ℝ) ^ f * d ^ (1 - 2 * ((r - a.val : ℕ) : ℝ)) * s a ^ (2 * f)) ^ (k + 1)) * (∏ p : UTr r, (2⁻¹ : ℝ) ^ f * d ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) - 2 * ((r - p.1.2.val : ℕ) : ℝ)) * (s p.1.1 * s p.1.2) ^ (2 * f)) * ∏ a : Fin r, d ^ (1 / 2 - 2 * ((r - a.val : ℕ) : ℝ)) * (s a ^ 2) ^ f) = d ^ (-(((k : ℝ) + 1) * (r : ℝ) ^ 2) - 4 * ((r : ℝ) ^ 3 - r) / 3 - 3 * (r : ℝ) / 2) * (∏ a : Fin r, s a ^ (4 * (r - (a : ℕ)) + 2 * k)) ^ f := by
  intro d f k r s hd hs
  obtain ⟨δ, rfl⟩ : ∃ δ, d = Real.exp δ := ⟨Real.log d, (Real.exp_log hd).symm⟩
  obtain ⟨σ, rfl⟩ : ∃ σ : Fin r → ℝ, s = fun a => Real.exp (σ a) :=
    ⟨fun a => Real.log (s a), funext fun a => (Real.exp_log (hs a)).symm⟩
  beta_reduce
  have h2i : (2⁻¹ : ℝ) = Real.exp (-Real.log 2) := by rw [Real.exp_neg, Real.exp_log two_pos]
  have e1 : ∀ p : UTr r, (2⁻¹ : ℝ) ^ f * Real.exp δ ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) +
      2 * ((r - p.1.2.val : ℕ) : ℝ)) * (Real.exp (σ p.1.1) / Real.exp (σ p.1.2)) ^ (2 * f) =
      Real.exp ((-(f : ℝ) * Real.log 2 + δ * (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ)) + 2 * f * σ p.1.1) +
        (2 * δ * ((r - p.1.2.val : ℕ) : ℝ) - 2 * f * σ p.1.2)) := by
    intro p
    rw [h2i]
    simp only [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_sub, ← Real.exp_add]
    congr 1; push_cast; ring
  have e3 : ∀ p : UTr r, (2⁻¹ : ℝ) ^ f * Real.exp δ ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) -
      2 * ((r - p.1.2.val : ℕ) : ℝ)) * (Real.exp (σ p.1.1) * Real.exp (σ p.1.2)) ^ (2 * f) =
      Real.exp ((-(f : ℝ) * Real.log 2 + δ * (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ)) + 2 * f * σ p.1.1) +
        (-(2 * δ * ((r - p.1.2.val : ℕ) : ℝ)) + 2 * f * σ p.1.2)) := by
    intro p
    rw [h2i]
    simp only [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  have e2 : ∀ a : Fin r, ((2⁻¹ : ℝ) ^ f * Real.exp δ ^ (1 - 2 * ((r - a.val : ℕ) : ℝ)) *
      Real.exp (σ a) ^ (2 * f)) ^ (k + 1) =
      Real.exp (((k : ℝ) + 1) * (-(f : ℝ) * Real.log 2 + δ * (1 - 2 * ((r - a.val : ℕ) : ℝ)) + 2 * f * σ a)) := by
    intro a
    rw [h2i]
    simp only [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  have e4 : ∀ a : Fin r, Real.exp δ ^ (1 / 2 - 2 * ((r - a.val : ℕ) : ℝ)) * (Real.exp (σ a) ^ 2) ^ f =
      Real.exp (δ * (1 / 2 - 2 * ((r - a.val : ℕ) : ℝ)) + 2 * f * σ a) := by
    intro a
    simp only [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1; push_cast; ring
  have e5 : ∀ a : Fin r, Real.exp (σ a) ^ (4 * (r - (a : ℕ)) + 2 * k) =
      Real.exp (((4 * (r - (a : ℕ)) + 2 * k : ℕ) : ℝ) * σ a) := fun a => (Real.exp_nat_mul _ _).symm
  rw [Finset.prod_congr rfl (fun p _ => e1 p), Finset.prod_congr rfl (fun a _ => e2 a),
    Finset.prod_congr rfl (fun p _ => e3 p), Finset.prod_congr rfl (fun a _ => e4 a),
    Finset.prod_congr rfl (fun a _ => e5 a)]
  have hu1 := sum_UTr r
    (fun a => -(f : ℝ) * Real.log 2 + δ * (1 - 2 * ((r - a.val : ℕ) : ℝ)) + 2 * f * σ a)
    (fun b => 2 * δ * ((r - b.val : ℕ) : ℝ) - 2 * f * σ b)
  have hu3 := sum_UTr r
    (fun a => -(f : ℝ) * Real.log 2 + δ * (1 - 2 * ((r - a.val : ℕ) : ℝ)) + 2 * f * σ a)
    (fun b => -(2 * δ * ((r - b.val : ℕ) : ℝ)) + 2 * f * σ b)
  beta_reduce at hu1 hu3
  rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_sum, ← Real.exp_sum, ← Real.exp_sum, hu1, hu3]
  rw [show (2 : ℝ) ^ (f * (r * (r - 1) + r * (k + 1))) =
      Real.exp (((f * (r * (r - 1) + r * (k + 1)) : ℕ) : ℝ) * Real.log 2) by
    rw [Real.exp_nat_mul, Real.exp_log two_pos]]
  simp only [← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
  rw [Real.exp_eq_exp]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← sub_eq_zero, show ∀ x y z w : ℝ, x + y - (z + w) = (y - w) + (x - z) from fun _ _ _ _ => by ring,
    ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (g := fun a : Fin r =>
      (δ * (2 * ((r : ℝ) - 1) * (1 - 2 * r) + ((k : ℝ) + 1) * (1 - 2 * r) + 1 / 2 - 2 * r) -
        Real.log 2 * f * (2 * r + k - 1)) +
      (δ * (8 * r + 2 * k - 2) + 2 * f * Real.log 2) * ((a : ℕ) : ℝ) + (-4 * δ) * ((a : ℕ) : ℝ) ^ 2) ?hc,
    sum_fin_quad]
  · have hN : ((f * (r * (r - 1) + r * (k + 1)) : ℕ) : ℝ) = f * (r * ((r : ℝ) - 1) + r * (k + 1)) := by
      rcases r with _ | n
      · simp
      · push_cast [Nat.add_sub_cancel]; ring
    rw [hN]; ring
  · intro a _
    have ha := a.isLt
    have h1 : ((r - (a : ℕ) : ℕ) : ℝ) = r - (a : ℕ) := by rw [Nat.cast_sub ha.le]
    have h2 : ((r - 1 - (a : ℕ) : ℕ) : ℝ) = r - 1 - (a : ℕ) := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
    have h3 : ((4 * (r - (a : ℕ)) + 2 * k : ℕ) : ℝ) = 4 * ((r : ℝ) - (a : ℕ)) + 2 * k := by
      push_cast [Nat.cast_sub ha.le]; ring
    rw [h3, h2, h1]; ring

end GlobalTheory.SnMass.VolN
