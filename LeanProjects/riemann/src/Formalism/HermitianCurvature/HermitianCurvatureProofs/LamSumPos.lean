import Formalism.HermitianCurvature.HermitianCurvatureProofs.RhypNodes

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem firstSt_inj {w : List C.Letter} : ∀ ys : List ℝ, Function.Injective (KB.firstSt (w := w) ys)
  | [] => fun _ _ h => h
  | _ :: ys => fun e e' h => firstSt_inj ys (Fin.cons_right_injective (α := fun _ => Fin 2) (0 : Fin 2) h)

theorem lam_sum_eq {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) :
    ∑ n : Fin K → Fin (d + 1), |∏ b, F7.lagCo (grid b) (n b)| = ∏ b, ∑ i, |F7.lagCo (grid b) i| := by
  rw [Fintype.prod_sum]
  exact Finset.sum_congr rfl fun n _ => Finset.abs_prod _ _

theorem lam_sum_pos {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (hinj : ∀ b, Function.Injective (grid b)) :
    0 < ∑ n : Fin K → Fin (d + 1), |∏ b, F7.lagCo (grid b) (n b)| := by
  rw [lam_sum_eq]
  refine Finset.prod_pos fun b _ => ?_
  exact lt_of_lt_of_le (abs_pos.2 (PBD.lagCo_ne_zero _ (hinj b) 0))
    (Finset.single_le_sum (f := fun i => |F7.lagCo (grid b) i|) (fun i _ => abs_nonneg _) (Finset.mem_univ 0))

theorem thGrid_eq {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (n : Fin K → Fin (d + 1)) :
    F7.thGrid grid n = |∏ b, F7.lagCo (grid b) (n b)| / ∑ m : Fin K → Fin (d + 1), |∏ b, F7.lagCo (grid b) (m b)| := by
  unfold F7.thGrid
  rw [Finset.prod_div_distrib, lam_sum_eq, Finset.abs_prod]

theorem lam_sum_le {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (B : ℝ)
    (hb : ∀ b, ∑ i, |F7.lagCo (grid b) i| ≤ B) :
    ∑ n : Fin K → Fin (d + 1), |∏ b, F7.lagCo (grid b) (n b)| ≤ B ^ K := by
  rw [lam_sum_eq]
  calc ∏ b, ∑ i, |F7.lagCo (grid b) i| ≤ ∏ _b : Fin K, B :=
        Finset.prod_le_prod (fun b _ => Finset.sum_nonneg fun i _ => abs_nonneg _) fun b _ => hb b
    _ = B ^ K := by simp

theorem zpow_sq_eq (x : ℝ) (hx : 0 < x) (ν : ℤ) : (x ^ ν) ^ 2 = x⁻¹ ^ (-(2 * ν)) := by
  rw [inv_zpow', neg_neg, ← zpow_natCast, ← zpow_mul, mul_comm]
  norm_num

section psd

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {α : Type}

theorem psd_dsum {Ea R : Type} [Fintype Ea] [Fintype R] (Y : Finset α) (d : Ea → R → ℝ) (hd : ∀ e ρ, 0 ≤ d e ρ)
    (V : Ea → R → α → H) : TB.PSDOn Y (fun P Q => ∑ e, ∑ ρ, (d e ρ : ℂ) * gramH (V e ρ) P Q) := by
  have h := loe_sum (Finset.univ : Finset Ea) (Y := Y) (A := fun _ _ _ => (0 : ℂ))
    (B := fun e P Q => ∑ ρ, (d e ρ : ℂ) * gramH (V e ρ) P Q) fun e _ => by
      have := loe_sum (Finset.univ : Finset R) (Y := Y) (A := fun _ _ _ => (0 : ℂ))
        (B := fun ρ P Q => (d e ρ : ℂ) * gramH (V e ρ) P Q) fun ρ _ => by
          have := loe_smul (d e ρ) (hd e ρ) (loe_zero_of_psd (psd_gramH Y (V e ρ)))
          exact loe_congr (fun x _ y _ => by ring) (fun x _ y _ => rfl) this
      exact loe_congr (fun x _ y _ => by simp) (fun x _ y _ => rfl) this
  exact psd_of_loe_zero (loe_congr (fun x _ y _ => by simp) (fun x _ y _ => rfl) h)

theorem psd_mixω {N : Type} [Fintype N] (Y : Finset α) (ω : α → ℝ) (θ κ : N → ℝ) (hθ : ∀ n, 0 ≤ θ n)
    (hκ : ∀ n, 0 ≤ κ n) (Kn : N → α → α → ℂ) (hK : ∀ n, TB.PSDOn Y (Kn n)) :
    TB.PSDOn Y (fun P Q => ∑ n, (θ n : ℂ) * ((ω P : ℂ) * (ω Q : ℂ) * ((κ n : ℂ) * Kn n P Q))) := by
  have h := loe_sum (Finset.univ : Finset N) (Y := Y) (A := fun _ _ _ => (0 : ℂ))
    (B := fun n P Q => (θ n : ℂ) * ((ω P : ℂ) * (ω Q : ℂ) * ((κ n : ℂ) * Kn n P Q))) fun n _ => by
      have h1 := loe_diag ω (loe_smul (θ n * κ n) (mul_nonneg (hθ n) (hκ n)) (loe_zero_of_psd (hK n)))
      exact loe_congr (fun x _ y _ => by simp) (fun x _ y _ => by push_cast; ring) h1
  exact psd_of_loe_zero (loe_congr (fun x _ y _ => by simp) (fun x _ y _ => rfl) h)

end psd

theorem mix_alg {N : Type} [Fintype N] (ω1 ω2 ka X L : ℝ) (lam Pn : N → ℝ) (Kn : N → ℂ) (hL : L ≠ 0)
    (hP : ∀ n, Pn n ≠ 0) :
    (ω1 : ℂ) * (ω2 : ℂ) * ((ka : ℂ) * ((X : ℂ) * ∑ n, ((|lam n| / Pn n : ℝ) : ℂ) * Kn n)) =
      ((X * L : ℝ) : ℂ) * ∑ n, ((|lam n| / L : ℝ) : ℂ) * ((ω1 : ℂ) * (ω2 : ℂ) * (((ka / Pn n : ℝ) : ℂ) * Kn n)) := by
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have h1 := hP n
  push_cast
  field_simp

end

end Formalism.FourierDecayAlt.P.PBL
