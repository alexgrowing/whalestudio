import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta

private theorem multiset_range_map_eq_sum_singleton (f : ℕ → ℂˣ) (N : ℕ) :
    (Multiset.range N).map f = ∑ j ∈ Finset.range N, ({f j} : Multiset ℂˣ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Multiset.range_succ, Multiset.map_cons, Finset.sum_range_succ, ← ih, add_comm, Multiset.singleton_add]

theorem str_eq_sum (q : ℂˣ) (t : ℤ) :
    str q t = ∑ j ∈ Finset.range t.toNat, ({q ^ (2 * (j : ℤ) - (t - 1))} : Multiset ℂˣ) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace.str]
  exact multiset_range_map_eq_sum_singleton _ _

theorem str_even (q : ℂˣ) (d : ℕ) (t : ℤ) (ht : t = 2 * d) :
    str q t = ∑ k ∈ Finset.range d, ({q ^ (t - 1 - 2 * (k : ℤ)), q ^ (-(t - 1 - 2 * (k : ℤ)))} : Multiset ℂˣ) := by
  rw [str_eq_sum, show t.toNat = d + d by omega, Finset.sum_range_add]
  conv_lhs => arg 2; rw [← Finset.sum_range_reflect]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < d := Finset.mem_range.mp hk
  rw [Multiset.insert_eq_cons, ← Multiset.singleton_add, add_comm]
  congr 3 <;> omega

theorem str_odd (q : ℂˣ) (d : ℕ) (t : ℤ) (ht : t = 2 * d + 1) :
    str q t = ∑ k ∈ Finset.range d, ({q ^ (t - 1 - 2 * (k : ℤ)), q ^ (-(t - 1 - 2 * (k : ℤ)))} : Multiset ℂˣ) + {1} := by
  rw [str_eq_sum, show t.toNat = d + (d + 1) by omega, Finset.sum_range_add, Finset.sum_range_succ']
  conv_lhs => arg 2; arg 1; rw [← Finset.sum_range_reflect]
  rw [← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < d := Finset.mem_range.mp hk
    rw [Multiset.insert_eq_cons, ← Multiset.singleton_add, add_comm]
    congr 3 <;> omega
  · rw [← zpow_zero q]
    congr 2
    omega

theorem lift_key (q : ℂˣ) (n n' : ℕ) (h : n ≤ n') :
    ∑ k ∈ Finset.range (n' / 2 - n / 2),
        ({q ^ ((n' : ℤ) - n - 1 - 2 * (k : ℤ)), q ^ (-((n' : ℤ) - n - 1 - 2 * (k : ℤ)))} : Multiset ℂˣ) +
      Multiset.replicate (n' % 2) ((-1 : ℂˣ) ^ n)⁻¹ =
    Multiset.replicate (n % 2) ((-1 : ℂˣ) ^ n')⁻¹ + str q ((n' : ℤ) - n) := by
  have hsq : ∀ m : ℕ, (-1 : ℂˣ) ^ (2 * m) = 1 := fun m => by rw [pow_mul, neg_one_sq, one_pow]
  rcases Nat.even_or_odd' n with ⟨a, rfl | rfl⟩ <;> rcases Nat.even_or_odd' n' with ⟨b, rfl | rfl⟩
  · rw [str_even q (b - a) _ (by omega), show 2 * b / 2 - 2 * a / 2 = b - a by omega,
      show 2 * b % 2 = 0 by omega, show 2 * a % 2 = 0 by omega]
    simp only [Multiset.replicate_zero, add_zero, zero_add]
  · rw [str_odd q (b - a) _ (by omega), show (2 * b + 1) / 2 - 2 * a / 2 = b - a by omega,
      show (2 * b + 1) % 2 = 1 by omega, show 2 * a % 2 = 0 by omega, hsq, inv_one]
    simp only [Multiset.replicate_zero, Multiset.replicate_one, zero_add]
  · have e0 : ((2 * b : ℕ) : ℤ) - ((2 * a + 1 : ℕ) : ℤ) - 1 - 2 * ((b - a - 1 : ℕ) : ℤ) = 0 := by omega
    rw [str_odd q (b - a - 1) _ (by omega), show 2 * b / 2 - (2 * a + 1) / 2 = b - a - 1 + 1 by omega,
      Finset.sum_range_succ, e0, neg_zero, zpow_zero,
      show 2 * b % 2 = 0 by omega, show (2 * a + 1) % 2 = 1 by omega, hsq, inv_one]
    simp only [Multiset.replicate_zero, Multiset.replicate_one, add_zero, Multiset.insert_eq_cons,
      ← Multiset.singleton_add]
    abel
  · have hodd : ∀ m : ℕ, (-1 : ℂˣ) ^ (2 * m + 1) = -1 := fun m => by rw [pow_succ, hsq, one_mul]
    rw [str_even q (b - a) _ (by omega), show (2 * b + 1) / 2 - (2 * a + 1) / 2 = b - a by omega,
      show (2 * b + 1) % 2 = 1 by omega, show (2 * a + 1) % 2 = 1 by omega, hodd, hodd, add_comm]

private theorem sum_pi_single_one_smul {ι : Type} (s : Finset ι) (f : ι → ℂˣ) :
    ∑ i ∈ s, ({f i} : Multiset ℂˣ) = s.val.map f := by
  rw [Finset.sum_eq_multiset_sum]
  generalize s.val = m
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih => rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.map_cons, Multiset.singleton_add]

open GlobalTheory.LGrp (bcParam) in

theorem bcParam_map_mul (c : ℂˣ) (N : ℕ) (γ : Fin (N / 2) → ℂˣ) :
    (bcParam N γ).map (fun x => c * x) =
      ∑ i, ({c * γ i, c * (γ i)⁻¹} : Multiset ℂˣ) + Multiset.replicate (N % 2) c := by
  have hpair : ∀ i, ({c * γ i, c * (γ i)⁻¹} : Multiset ℂˣ) = {c * γ i} + {c * (γ i)⁻¹} := fun i => by
    rw [Multiset.insert_eq_cons, Multiset.singleton_add]
  simp only [hpair, Finset.sum_add_distrib, sum_pi_single_one_smul, bcParam, Multiset.map_add, Multiset.map_map,
    Multiset.map_replicate, mul_one]
  rfl

theorem neg_one_pow_inv (k : ℕ) : ((-1 : ℂˣ) ^ k)⁻¹ = (-1) ^ k := by rw [← inv_pow, inv_neg_one]

theorem neg_one_pow_mul_self (k : ℕ) : (-1 : ℂˣ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

private theorem pair_inv_mul_eq_of_mul_self_eq_one (s t a : ℂˣ) (hs : s * s = 1) (ht : t * t = 1) :
    ({s⁻¹ * (s * t * a⁻¹), s⁻¹ * (s * t * a⁻¹)⁻¹} : Multiset ℂˣ) = {t⁻¹ * a, t⁻¹ * a⁻¹} := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have e1 : s⁻¹ * (s * t * a⁻¹) = t⁻¹ * a⁻¹ := by rw [mul_assoc, inv_mul_cancel_left, ht']
  have e2 : s⁻¹ * (s * t * a⁻¹)⁻¹ = t⁻¹ * a := by
    simp only [mul_inv, inv_inv]
    rw [hs', ← mul_assoc, ← mul_assoc, hs, one_mul]
  rw [e1, e2, Multiset.pair_comm]

theorem bcParam_liftPar (q : ℂˣ) (n n' : ℕ) (h : n ≤ n') (α : Fin (n / 2) → ℂˣ) :
    (bcParam n' (liftPar q n n' α)).map (fun x => ((-1 : ℂˣ) ^ n)⁻¹ * x) =
      (bcParam n α).map (fun x => ((-1 : ℂˣ) ^ n')⁻¹ * x) + str q ((n' : ℤ) - n) := by
  have hD : n' / 2 - n / 2 + n / 2 = n' / 2 := by omega
  have hs : (-1 : ℂˣ) ^ n * (-1) ^ n = 1 := neg_one_pow_mul_self n
  have hsum : (∑ i : Fin (n' / 2), ({((-1 : ℂˣ) ^ n)⁻¹ * liftPar q n n' α i,
        ((-1 : ℂˣ) ^ n)⁻¹ * (liftPar q n n' α i)⁻¹} : Multiset ℂˣ)) =
      ∑ k ∈ Finset.range (n' / 2 - n / 2),
        ({q ^ ((n' : ℤ) - n - 1 - 2 * (k : ℤ)), q ^ (-((n' : ℤ) - n - 1 - 2 * (k : ℤ)))} : Multiset ℂˣ) +
      ∑ i : Fin (n / 2), ({((-1 : ℂˣ) ^ n')⁻¹ * α i, ((-1 : ℂˣ) ^ n')⁻¹ * (α i)⁻¹} : Multiset ℂˣ) := by
    rw [← Equiv.sum_comp (finCongr hD), Fin.sum_univ_add, ← Fin.sum_univ_eq_sum_range]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hL : liftPar q n n' α (finCongr hD (Fin.castAdd (n / 2) i)) =
          (-1) ^ n * q ^ ((n' : ℤ) - n - 1 - 2 * ((i : ℕ) : ℤ)) := by
        unfold liftPar
        rw [dif_pos (by simp)]
        simp
      rw [hL, mul_inv, inv_mul_cancel_left, neg_one_pow_inv, ← mul_assoc, hs, one_mul, ← _root_.zpow_neg]
    · refine Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_
      have hL : liftPar q n n' α (finCongr hD (Fin.natAdd (n' / 2 - n / 2) j)) =
          (-1) ^ n * (-1) ^ n' * (α (Fin.revPerm j))⁻¹ := by
        unfold liftPar
        rw [dif_neg (by simp), pow_add]
        congr 3
        ext
        simp
        omega
      rw [hL]
      exact pair_inv_mul_eq_of_mul_self_eq_one _ _ _ hs (neg_one_pow_mul_self n')
  rw [bcParam_map_mul, bcParam_map_mul, hsum, add_assoc _ (Multiset.replicate (n % 2) _), ← lift_key q n n' h]
  abel

end GlobalTheory.SphTheta
