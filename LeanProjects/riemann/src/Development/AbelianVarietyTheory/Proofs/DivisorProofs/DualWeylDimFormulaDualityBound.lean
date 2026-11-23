import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
import Formalism.PolynomialDimension.WeylDim
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.PbSmithLam
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.WeylDimShift

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.WeylDimBound

theorem dim_eq_weylDim (n : ℕ) (la : Fin n → ℕ) (hla : Antitone la) :
    (GlobalTheory.DualWeyl.dim la : ℚ) = Formalism.CountingSumsFrames.weylDim n (fun i => (la i : ℤ)) :=
  Formalism.MainNotions.flipOneThree.Pf.pb_finrank ℂ n la hla

theorem dim_dual (n : ℕ) (la : Fin n → ℕ) (hla : Antitone la) (s : ℕ) (hs : ∀ i, la i ≤ s) :
    GlobalTheory.DualWeyl.dim (fun i => s - la (Fin.rev i)) = GlobalTheory.DualWeyl.dim la := by
  have hanti : Antitone (fun i : Fin n => s - la (Fin.rev i)) := by
    intro i j hij
    have := hla (Fin.rev_le_rev.mpr hij)
    dsimp only
    omega
  have h1 := dim_eq_weylDim n _ hanti
  have h2 := dim_eq_weylDim n la hla
  have h3 : Formalism.CountingSumsFrames.weylDim n (fun i => (((s - la (Fin.rev i) : ℕ)) : ℤ)) =
      Formalism.CountingSumsFrames.weylDim n (fun i => (la i : ℤ)) := by
    have e : (fun i : Fin n => (((s - la (Fin.rev i) : ℕ)) : ℤ)) =
        fun i => -((fun k => (la k : ℤ)) i.rev) + (s : ℤ) := by
      funext i
      rw [Nat.cast_sub (hs _)]
      ring
    rw [e, Formalism.MainNotions.Pf14.weylDim_shift n (fun i => -((fun k => (la k : ℤ)) i.rev)) (s : ℤ)]
    exact Formalism.MainNotions.Pf14.weylDim_dual n (fun k => (la k : ℤ))
  exact_mod_cast h1.trans (h3.trans h2.symm)

theorem sum_card_lt (n : ℕ) : ∑ i : Fin n, (Finset.univ.filter fun j : Fin n => i < j).card = n.choose 2 := by
  have h1 : ∀ i : Fin n, (Finset.univ.filter fun j : Fin n => i < j).card = n - 1 - i := by
    intro i
    rw [← Fin.card_Ioi]
    congr 1
    ext j
    simp
  simp only [h1]
  rw [Fin.sum_univ_eq_sum_range (fun k => n - 1 - k) n, Finset.sum_range_reflect (fun k => k) n,
    Finset.sum_range_id, Nat.choose_two_right]

theorem prod_ite_lt (n : ℕ) (c : ℝ) :
    ∏ i : Fin n, ∏ j : Fin n, (if i < j then c else 1) = c ^ n.choose 2 := by
  simp only [Finset.prod_ite, Finset.prod_const, one_pow, mul_one]
  rw [Finset.prod_pow_eq_pow_sum, sum_card_lt]

theorem weylDim_le (n : ℕ) (la : Fin n → ℕ) (hla : Antitone la) (w : ℤ) :
    ((Formalism.CountingSumsFrames.weylDim n (fun i => (la i : ℤ)) : ℚ) : ℝ) ≤ ((∑ i, |((la i : ℤ) : ℝ) - w|) + 1) ^ n.choose 2 := by
  set S := ∑ i, |((la i : ℤ) : ℝ) - w| with hS
  have hcast : ((Formalism.CountingSumsFrames.weylDim n (fun i => (la i : ℤ)) : ℚ) : ℝ) = ∏ i : Fin n, ∏ j : Fin n,
      (if i < j then (((la i : ℝ) - la j) + ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) / (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) else 1) := by
    unfold Formalism.CountingSumsFrames.weylDim
    rw [Rat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Rat.cast_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    split_ifs <;> push_cast <;> ring
  have hpair : ∀ i j : Fin n, i ≠ j → |((la i : ℤ) : ℝ) - w| + |((la j : ℤ) : ℝ) - w| ≤ S := by
    intro i j hij
    rw [← Finset.sum_pair (f := fun k => |((la k : ℤ) : ℝ) - w|) hij]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => abs_nonneg _
  rw [hcast, ← prod_ite_lt]
  refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => ?_)
    fun i _ => Finset.prod_le_prod (fun j _ => ?_) fun j _ => ?_
  · split_ifs with hij
    · have hd : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast (Fin.lt_def.mp hij)
      have ha : (la j : ℝ) ≤ la i := by exact_mod_cast hla hij.le
      exact div_nonneg (by linarith) (by linarith)
    · exact zero_le_one
  · split_ifs with hij
    · have hd : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast (Fin.lt_def.mp hij)
      have ha : (la j : ℝ) ≤ la i := by exact_mod_cast hla hij.le
      exact div_nonneg (by linarith) (by linarith)
    · exact zero_le_one
  · split_ifs with hij
    · have hd : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast (Fin.lt_def.mp hij)
      have ha : (la j : ℝ) ≤ la i := by exact_mod_cast hla hij.le
      have hp := hpair i j hij.ne
      have h1 := le_abs_self (((la i : ℤ) : ℝ) - w)
      have h2 := neg_abs_le (((la j : ℤ) : ℝ) - w)
      push_cast at hp h1 h2
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    · exact le_rfl

theorem dim_weyl_dual_bound : ∀ (n : ℕ) (la : Fin n → ℕ), Antitone la →
    (dim la : ℚ) = Formalism.CountingSumsFrames.weylDim n (fun i => (la i : ℤ)) ∧
      (∀ s : ℕ, (∀ i, la i ≤ s) → dim (fun i => s - la (Fin.rev i)) = dim la) ∧
      ∀ w : ℤ, (dim la : ℝ) ≤ ((∑ i, |((la i : ℤ) : ℝ) - w|) + 1) ^ n.choose 2 := by
  intro n la hla
  refine ⟨dim_eq_weylDim n la hla, fun s hs => dim_dual n la hla s hs, fun w => ?_⟩
  have h : (dim la : ℝ) = ((dim la : ℚ) : ℝ) := (Rat.cast_natCast _).symm
  rw [h, dim_eq_weylDim n la hla]
  exact weylDim_le n la hla w

end GlobalTheory.WeylDimBound
