import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCC

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Finset

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ltSigma (r : ℕ) : LsNc5.LtPair r ≃ Σ a : Fin r, Fin a.val where
  toFun p := ⟨p.1.2, ⟨p.1.1.val, p.2⟩⟩
  invFun q := ⟨(⟨q.2.val, lt_trans q.2.isLt q.1.isLt⟩, q.1), q.2.isLt⟩
  left_inv p := by rcases p with ⟨⟨b, a⟩, h⟩; rfl
  right_inv q := by rcases q with ⟨a, b⟩; rfl

theorem sum_lt (r : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ p : LsNc5.LtPair r, g p.1.1.val p.1.2.val = ∑ a ∈ range r, ∑ b ∈ range a, g b a := by
  rw [Fintype.sum_equiv (ltSigma r) (fun p => g p.1.1.val p.1.2.val) (fun q => g q.2.val q.1.val) (fun _ => rfl),
    Fintype.sum_sigma]
  rw [← Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ range a, g b a) r]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Fin.sum_univ_eq_sum_range (fun b => g b a.val) a.val

theorem sum_id_real (a : ℕ) : ∑ b ∈ range a, (b : ℝ) = a * (a - 1) / 2 := by
  induction a with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem card_lt (r : ℕ) : (Fintype.card (LsNc5.LtPair r) : ℝ) = r * (r - 1) / 2 := by
  have h := sum_lt r (fun _ _ => 1)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Finset.card_univ] at h
  rw [h]
  exact sum_id_real r

theorem card_lt_nat (r : ℕ) : Fintype.card (LsNc5.LtPair r) = r * (r - 1) / 2 := by
  have h2 : 2 ∣ r * (r - 1) := (Nat.even_mul_pred_self r).two_dvd
  have : ((r * (r - 1) / 2 : ℕ) : ℝ) = r * (r - 1) / 2 := by
    rw [Nat.cast_div h2 (by norm_num)]
    rcases Nat.eq_zero_or_pos r with h0 | hp
    · rw [h0]; simp
    · rw [Nat.cast_mul, Nat.cast_sub hp]; push_cast; ring
  exact_mod_cast (card_lt r).trans this.symm

theorem sumX (n : ℕ) : ∑ a ∈ range n, ∑ b ∈ range a, ((1 : ℝ) - 2 * ((a : ℝ) - b)) =
    -((n - 1) * n * (2 * n - 1) / 6) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, sum_id_real]
    push_cast; ring

theorem sumK (R : ℝ) (n : ℕ) : ∑ a ∈ range n, ∑ b ∈ range a, ((1 : ℝ) - 2 * (R - b) - 2 * (R - a)) =
    3 * ((n - 1) * n * (2 * n - 1) / 6) - 4 * R * (n * (n - 1) / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : ∑ b ∈ range n, ((1 : ℝ) - 2 * (R - b) - 2 * (R - n)) =
        ∑ b ∈ range n, ((1 - 4 * R + 2 * (n : ℝ)) + 2 * (b : ℝ)) :=
      Finset.sum_congr rfl fun b _ => by ring
    rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum, sum_id_real]
    push_cast; ring

theorem sumR (R K : ℝ) (n : ℕ) : ∑ b ∈ range n, ((K + 1) * (1 - 2 * (R - b))) = (K + 1) * (n - 2 * R * n + n * (n - 1)) := by
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, sum_id_real]
  push_cast; ring

theorem sumD (R : ℝ) (n : ℕ) : ∑ a ∈ range n, ((1 / 2 : ℝ) - 2 * (R - a)) = n / 2 - 2 * R * n + n * (n - 1) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, sum_id_real]
  push_cast; ring

theorem prod_const_rpow {ι : Type*} (s : Finset ι) {c d : ℝ} (hd : 0 < d) (e : ι → ℝ) :
    ∏ x ∈ s, (c * d ^ e x) = c ^ s.card * d ^ (∑ x ∈ s, e x) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Real.rpow_sum_of_pos hd]

theorem half_succ (R : ℕ) : R * (R - 1) / 2 + R = R * (R + 1) / 2 := by
  rcases Nat.eq_zero_or_pos R with h0 | hp
  · subst h0; simp
  · obtain ⟨m, rfl⟩ : ∃ m, R = m + 1 := ⟨R - 1, by omega⟩
    rw [Nat.add_sub_cancel, show (m + 1) * (m + 1 + 1) = (m + 1) * m + (m + 1) * 2 by ring,
      Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]

theorem final_alg (t d : ℝ) (hd : 0 < d) (F R K : ℕ) (A B C E : ℝ)
    (h : A + B + C + E = LsNc5.covolumeExponent R K) :
    ((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * d ^ A * ((t ^ F * (2 : ℝ)⁻¹ ^ (F * (K + 1))) ^ R * d ^ B) *
        (((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * d ^ C * d ^ E) =
      t ^ (R * F) * (2 : ℝ) ^ (-((F * (R * K + R * (R - 1) / 2) : ℕ) : ℝ)) * d ^ LsNc5.covolumeExponent R K /
        (2 : ℝ) ^ (F * (R * (R + 1) / 2)) := by
  have hd' : d ^ A * d ^ B * d ^ C * d ^ E = d ^ LsNc5.covolumeExponent R K := by
    rw [← h, Real.rpow_add hd, Real.rpow_add hd, Real.rpow_add hd]
  have h2 : ((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * ((2 : ℝ)⁻¹ ^ (F * (K + 1))) ^ R * ((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) =
      (2 : ℝ) ^ (-((F * (R * K + R * (R - 1) / 2) : ℕ) : ℝ)) / (2 : ℝ) ^ (F * (R * (R + 1) / 2)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, div_eq_mul_inv, ← inv_pow, ← inv_pow, ← pow_add,
      ← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← half_succ]
    congr 1
    ring
  calc ((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * d ^ A * ((t ^ F * (2 : ℝ)⁻¹ ^ (F * (K + 1))) ^ R * d ^ B) *
        (((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * d ^ C * d ^ E)
      = t ^ (R * F) * (((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2) * ((2 : ℝ)⁻¹ ^ (F * (K + 1))) ^ R *
          ((2 : ℝ)⁻¹ ^ F) ^ (R * (R - 1) / 2)) * (d ^ A * d ^ B * d ^ C * d ^ E) := by ring
    _ = _ := by rw [h2, hd']; ring

theorem cVal_prod {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    ∏ p, cVal X u p = LsNc5.covolN X u / LsNc5.twoU X := by
  have hd0 : 0 < |(NumberField.discr X.B.I.F : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero X.B.I.F)
  have hT : 0 < Tw (D := D) u := Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos u
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [cVal]
  rw [prod_const_rpow _ hd0, prod_const_rpow _ hd0, prod_const_rpow _ hd0, ← Real.rpow_sum_of_pos hd0]
  have eX := sum_lt D.R.rS (fun b a => (1 : ℝ) - 2 * ((a : ℝ) - b))
  have eK := sum_lt D.R.rS (fun b a => (1 : ℝ) - 2 * ((D.R.rS : ℝ) - b) - 2 * ((D.R.rS : ℝ) - a))
  have eR : ∑ b : Fin D.R.rS, (((D.R.k : ℝ) + 1) * (1 - 2 * ((D.R.rS : ℝ) - (b : ℕ)))) =
      ∑ b ∈ range D.R.rS, (((D.R.k : ℝ) + 1) * (1 - 2 * ((D.R.rS : ℝ) - b))) :=
    Fin.sum_univ_eq_sum_range (fun b => ((D.R.k : ℝ) + 1) * (1 - 2 * ((D.R.rS : ℝ) - b))) D.R.rS
  have eD : ∑ a : Fin D.R.rS, ((1 / 2 : ℝ) - 2 * ((D.R.rS : ℝ) - (a : ℕ))) =
      ∑ a ∈ range D.R.rS, ((1 / 2 : ℝ) - 2 * ((D.R.rS : ℝ) - a)) :=
    Fin.sum_univ_eq_sum_range (fun a => (1 / 2 : ℝ) - 2 * ((D.R.rS : ℝ) - a)) D.R.rS
  simp only [Finset.card_univ]
  rw [eX, eK, eR, eD, sumX, sumK, sumR, sumD, card_lt_nat, Fintype.card_fin]
  unfold LsNc5.covolN LsNc5.twoU
  exact final_alg _ _ hd0 _ _ _ _ _ _ _ (by unfold LsNc5.covolumeExponent; ring)

end Formalism.L2.SG.Pf.NcReal.JX
