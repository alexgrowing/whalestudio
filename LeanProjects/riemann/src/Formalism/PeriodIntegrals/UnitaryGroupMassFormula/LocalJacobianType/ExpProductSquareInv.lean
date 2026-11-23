import Mathlib
import Formalism.PeriodIntegrals.LocJacTyp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitAbs

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacTyp
open scoped Classical

section Count

theorem sum_uidx (r : ℕ) (g : Fin (r + 1) × Fin (r + 1) → ℝ) :
    ∑ q : UIdx r, g q.1 = ∑ i : Fin (r + 1), ∑ j : Fin (r + 1), if i < j then g (i, j) else 0 := by
  rw [← Fintype.sum_prod_type', ← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) (fun p => g p)).symm

theorem card_Ioi' (r : ℕ) (i : Fin (r + 1)) :
    ((Finset.univ.filter fun j : Fin (r + 1) => i < j).card : ℝ) = (r : ℝ) - (i : ℕ) := by
  have h : (Finset.univ.filter fun j : Fin (r + 1) => i < j) = Finset.Ioi i := by ext j; simp
  rw [h, Fin.card_Ioi]
  have := i.is_le
  rw [show r + 1 - 1 - (i : ℕ) = r - (i : ℕ) by omega, Nat.cast_sub this]

theorem card_Iio' (r : ℕ) (j : Fin (r + 1)) :
    ((Finset.univ.filter fun i : Fin (r + 1) => i < j).card : ℝ) = ((j : ℕ) : ℝ) := by
  have h : (Finset.univ.filter fun i : Fin (r + 1) => i < j) = Finset.Iio j := by ext i; simp
  rw [h, Fin.card_Iio]

theorem card_le' (r : ℕ) (i : Fin (r + 1)) :
    ((Finset.univ.filter fun l : Fin r => (i : ℕ) ≤ (l : ℕ)).card : ℝ) = (r : ℝ) - (i : ℕ) := by
  have h : (Finset.univ.filter fun l : Fin r => (i : ℕ) ≤ (l : ℕ)).map Fin.valEmbedding =
      Finset.Ico (i : ℕ) r := by
    ext n
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨l, hl, rfl⟩; exact ⟨hl, l.2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨n, h2⟩, h1, rfl⟩
  rw [← Finset.card_map, h, Nat.card_Ico, Nat.cast_sub i.is_le]

theorem sum_fst (r : ℕ) (f : Fin (r + 1) → ℝ) :
    ∑ q : UIdx r, f q.1.1 = ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * f i := by
  rw [sum_uidx r (fun p => f p.1)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_filter]
  dsimp only
  rw [Finset.sum_const, nsmul_eq_mul, card_Ioi']

theorem sum_snd (r : ℕ) (f : Fin (r + 1) → ℝ) :
    ∑ q : UIdx r, f q.1.2 = ∑ j : Fin (r + 1), ((j : ℕ) : ℝ) * f j := by
  rw [sum_uidx r (fun p => f p.2), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_filter]
  dsimp only
  rw [Finset.sum_const, nsmul_eq_mul, card_Iio']

theorem sum_jac (r : ℕ) (a : Fin (r + 1) → ℝ) :
    ∑ l : Fin r, ∑ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)), a i =
      ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_le']

theorem gauss (r : ℕ) : 2 * ∑ i : Fin (r + 1), ((i : ℕ) : ℝ) = (r : ℝ) * (r + 1) := by
  have h := Finset.sum_range_id_mul_two (r + 1)
  rw [Fin.sum_univ_eq_sum_range (fun n => (n : ℝ)) (r + 1)]
  have h2 : ((∑ i ∈ Finset.range (r + 1), i : ℕ) : ℝ) * 2 = ((r + 1) * (r + 1 - 1) : ℕ) := by
    exact_mod_cast h
  push_cast at h2
  linarith

theorem sum_l_succ (r : ℕ) : ∑ l : Fin r, (((l : ℕ) : ℝ) + 1) = ∑ i : Fin (r + 1), ((i : ℕ) : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range (fun n => (n : ℝ) + 1) r,
    Fin.sum_univ_eq_sum_range (fun n => (n : ℝ)) (r + 1), Finset.sum_range_succ']
  push_cast
  simp

end Count

section Real

open Real

variable (r : ℕ)

theorem exp_product_square_inv (a : Fin (r + 1) → ℝ) :
    ∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((exp (a i) * exp (a j)) ^ 2)⁻¹ =
      exp (-(4 * ((r : ℝ) + 1)) * ∑ i, a i) := by
  simp only [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_sum]
  congr 1
  simp only [Finset.sum_neg_distrib, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem eJ (a : Fin (r + 1) → ℝ) (γ : ℝ) :
    ∏ l : Fin r, (((∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)),
        exp (a i) ^ 2) * (exp γ)⁻¹ ^ ((l : ℕ) + 1)) ^ 2) ^ 2 =
      exp (8 * ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i -
        4 * γ * ∑ l : Fin r, (((l : ℕ) : ℝ) + 1)) := by
  simp only [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_sum]
  congr 1
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, ← sum_jac]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring_nf
  try simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [show ∑ x : Fin r, ((x : ℕ) : ℝ) * γ * 4 = ∑ x : Fin r, γ * ((x : ℕ) : ℝ) * 4 from
    Finset.sum_congr rfl (fun _ _ => by ring)]
  ring

theorem eU (a : Fin (r + 1) → ℝ) (γ : ℝ) :
    ∏ q : UIdx r, (exp γ ^ 2 * (exp (a q.1.1) / exp (a q.1.2)) ^ 4) =
      exp (2 * γ * (Fintype.card (UIdx r) : ℝ) + 4 * ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i -
        4 * ∑ j : Fin (r + 1), ((j : ℕ) : ℝ) * a j) := by
  simp only [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_sub, ← Real.exp_sum]
  congr 1
  rw [← sum_fst r a, ← sum_snd r a]
  simp only [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  ring

theorem eL (a : Fin (r + 1) → ℝ) (γ : ℝ) :
    ∏ l : Fin (r + 1), (exp γ ^ 3 * (exp (a l) ^ 4)⁻¹) =
      exp (3 * ((r : ℝ) + 1) * γ - 4 * ∑ l, a l) := by
  simp only [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_sum]
  congr 1
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem card_uidx : 2 * (Fintype.card (UIdx r) : ℝ) = (r : ℝ) * (r + 1) := by
  have h := sum_fst r (fun _ => (1 : ℝ))
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  rw [h, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have := gauss r
  push_cast
  linarith

end Real

section Final

open Real

theorem arith_real (r : ℕ) (A : Fin (r + 1) → ℝ) (hA : ∀ i, 0 < A i) (G m : ℝ) (hG : 0 < G) :
    m ^ ((r + 1) * (r + 1)) * G ^ (3 * ((r + 1) * (r + 1))) *
        (∏ i : Fin (r + 1), ∏ j : Fin (r + 1), ((A i * A j) ^ 2)⁻¹) *
        ∏ l : Fin r, (((∏ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)),
          A i ^ 2) * G⁻¹ ^ ((l : ℕ) + 1)) ^ 2) ^ 2 =
      (∏ q : UIdx r, (m ^ 2 * G ^ 2 * (A q.1.1 / A q.1.2) ^ 4)) *
        ∏ l : Fin (r + 1), (m * G ^ 3 * (A l ^ 4)⁻¹) := by
  obtain ⟨γ, rfl⟩ : ∃ γ, G = exp γ := ⟨log G, (exp_log hG).symm⟩
  obtain ⟨a, rfl⟩ : ∃ a : Fin (r + 1) → ℝ, A = fun i => exp (a i) :=
    ⟨fun i => log (A i), funext fun i => (exp_log (hA i)).symm⟩
  have hU : ∏ q : UIdx r, (m ^ 2 * exp γ ^ 2 * (exp (a q.1.1) / exp (a q.1.2)) ^ 4) =
      (m ^ 2) ^ Fintype.card (UIdx r) * ∏ q : UIdx r, (exp γ ^ 2 * (exp (a q.1.1) / exp (a q.1.2)) ^ 4) := by
    rw [Finset.prod_congr rfl (fun q _ => mul_assoc _ _ _), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ]
  have hL : ∏ l : Fin (r + 1), (m * exp γ ^ 3 * (exp (a l) ^ 4)⁻¹) =
      m ^ (r + 1) * ∏ l : Fin (r + 1), (exp γ ^ 3 * (exp (a l) ^ 4)⁻¹) := by
    rw [Finset.prod_congr rfl (fun q _ => mul_assoc _ _ _), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  simp only at hU hL ⊢
  rw [hU, hL, exp_product_square_inv, eJ, eU, eL]
  have hK := card_uidx r
  have hN : 2 * Fintype.card (UIdx r) + (r + 1) = (r + 1) * (r + 1) := by
    have : ((2 * Fintype.card (UIdx r) + (r + 1) : ℕ) : ℝ) = (((r + 1) * (r + 1) : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  have hm : (m ^ 2) ^ Fintype.card (UIdx r) * m ^ (r + 1) = m ^ ((r + 1) * (r + 1)) := by
    rw [← pow_mul, ← pow_add, hN]
  have hS := gauss r
  have hS' := sum_l_succ r
  have h1 : ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i + ∑ j : Fin (r + 1), ((j : ℕ) : ℝ) * a j =
      (r : ℝ) * ∑ i, a i := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hE : exp γ ^ (3 * ((r + 1) * (r + 1))) *
      exp (-(4 * ((r : ℝ) + 1)) * ∑ i, a i) *
      exp (8 * ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i - 4 * γ * ∑ l : Fin r, (((l : ℕ) : ℝ) + 1)) =
      exp (2 * γ * (Fintype.card (UIdx r) : ℝ) + 4 * ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i -
        4 * ∑ j : Fin (r + 1), ((j : ℕ) : ℝ) * a j) *
      exp (3 * ((r : ℝ) + 1) * γ - 4 * ∑ l, a l) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    linear_combination (-4 * γ) * hS' + (-2 * γ) * hS + (-γ) * hK + 4 * h1
  rw [← hm]
  calc (m ^ 2) ^ Fintype.card (UIdx r) * m ^ (r + 1) * exp γ ^ (3 * ((r + 1) * (r + 1))) *
        exp (-(4 * ((r : ℝ) + 1)) * ∑ i, a i) *
        exp (8 * ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i - 4 * γ * ∑ l : Fin r, (((l : ℕ) : ℝ) + 1))
      = (m ^ 2) ^ Fintype.card (UIdx r) * m ^ (r + 1) * (exp γ ^ (3 * ((r + 1) * (r + 1))) *
        exp (-(4 * ((r : ℝ) + 1)) * ∑ i, a i) *
        exp (8 * ∑ i : Fin (r + 1), ((r : ℝ) - (i : ℕ)) * a i - 4 * γ * ∑ l : Fin r, (((l : ℕ) : ℝ) + 1))) := by
        ring
    _ = _ := by rw [hE]; ring

end Final

section AbsProd

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

def absVHom : Fv F v →* ℝ where
  toFun := absV v
  map_one' := absV_one v
  map_mul' := absV_mul v

theorem absV_prod {ι : Type} (s : Finset ι) (f : ι → Fv F v) :
    absV v (∏ i ∈ s, f i) = ∏ i ∈ s, absV v (f i) :=
  map_prod (absVHom v) f s

theorem quadraticDifferenceArith : Arith (F := F) v := by
  intro typed g r m ht hg
  unfold jacS
  simp only [if_pos ht, absV_mul, absV_prod, absV_pow, absV_inv]
  exact arith_real r _ (fun i => absV_pos v (alp_ne_zero v r i)) _ m
    (absV_pos v (natCast_ne_zero v hg))

end AbsProd

end PI.UnitaryGroupMassFormula.LocJacTyp
