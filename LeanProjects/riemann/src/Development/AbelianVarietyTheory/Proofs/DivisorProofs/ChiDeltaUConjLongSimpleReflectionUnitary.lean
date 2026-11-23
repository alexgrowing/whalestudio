import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

noncomputable section

namespace GlobalTheory

namespace GKUnitary

theorem diag_conj_weylRep {R : Type} [CommRing R] {n : ℕ} {s : Equiv.Perm (Fin n)} {y t : GL (Fin n) R}
    (hy : IsWeylRep s y) (ht : ∀ i j, i ≠ j → (t : Matrix (Fin n) (Fin n) R) i j = 0) (i : Fin n) :
    ((y⁻¹ * t * y : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i i =
      (t : Matrix (Fin n) (Fin n) R) (s i) (s i) := by
  have h1 : ((y⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i (s i) * (y : Matrix (Fin n) (Fin n) R) (s i) i = 1 := by
    have h := congrFun (congrFun (Units.inv_mul y) i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single (s i)] at h
    · rw [h, Matrix.one_apply_eq]
    · intro b _ hb; rw [hy b i hb, mul_zero]
    · simp
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (s i)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (s i)]
    · calc ((y⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i (s i) * (t : Matrix (Fin n) (Fin n) R) (s i) (s i) *
            (y : Matrix (Fin n) (Fin n) R) (s i) i
          = (t : Matrix (Fin n) (Fin n) R) (s i) (s i) *
            (((y⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i (s i) * (y : Matrix (Fin n) (Fin n) R) (s i) i) := by ring
        _ = _ := by rw [h1, mul_one]
    · intro b _ hb; rw [ht b (s i) hb, mul_zero]
    · simp
  · intro b _ hb; rw [hy b i hb, mul_zero]
  · simp

theorem ordL_congr {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x y : L}
    (h : Valued.v x = Valued.v y) : ordL x = ordL y := by
  have key : ∀ z : L, ordL z = (fun w : WithZero (Multiplicative ℤ) =>
      if h : w = 0 then (0 : ℤ) else -Multiplicative.toAdd (WithZero.unzero h)) (Valued.v z) := fun _ => rfl
  rw [key x, key y, h]

theorem ordL_one' {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] : ordL (1 : L) = 0 :=
  Formalism.UG.P.fIwasawa_ordL_unit 1 1 (by simp) (by simp) (by simp)

theorem chiDeltaU_conj_simpleU_long :
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    IsUnramInv ϖ σ q → ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → Even n →
    ∀ (y : GU σ n), IsWeylRep (simpleU k) (y : GL (Fin n) L) → ∀ (α : Fin (n / 2) → ℂˣ) (t : GU σ n),
    (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) →
    chiDeltaU q (fun i => (α i : ℂ)) (y⁻¹ * t * y) *
        (q : ℂ) ^ (-2 * ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k))) =
      chiDeltaU q (fun i => (actU k α i : ℂ)) t := by
  intro L _ _ ϖ σ q hU n k hk hn y hy α t ht
  obtain ⟨hσ, hσv, -, -, -, hq2, -⟩ := hU
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hs : simpleU k = Equiv.swap (lo k) (lo k).rev := by simp [simpleU, hk]
  have hact : actU k α = Function.update α k (α k)⁻¹ := by simp [actU, hk]
  obtain ⟨m, hm⟩ := hn
  have hkv : k.val + 1 = m := by have := k.2; omega
  have hrev : ((lo k).rev : ℕ) = m := by simp [Fin.val_rev, lo]; omega
  set T : Matrix (Fin n) (Fin n) L := ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hT
  have hdiag : ∀ i, (((y⁻¹ * t * y : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
      T (simpleU k i) (simpleU k i) := by
    intro i
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact diag_conj_weylRep hy ht i

  have hprod : σ (T (lo k).rev (lo k).rev) * T (lo k) (lo k) = 1 := by
    have hu := (GlobalTheory.LGrp.mem_GU_iff σ n (t : GL (Fin n) L)).1 t.2 (lo k) (lo k)
    have h := congrFun (congrFun (Units.inv_mul (t : GL (Fin n) L)) (lo k)) (lo k)
    rw [Matrix.mul_apply, Finset.sum_eq_single (lo k)] at h
    · rw [← hu, h, Matrix.one_apply_eq]
    · intro b _ hb; exact mul_eq_zero_of_right _ (ht b (lo k) hb)
    · simp
  have ha0 : T (lo k) (lo k) ≠ 0 := right_ne_zero_of_mul_eq_one hprod
  have hb0 : σ (T (lo k).rev (lo k).rev) ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  have hord : ordL (T (lo k).rev (lo k).rev) = -ordL (T (lo k) (lo k)) := by
    have h := Formalism.UG.P.fIwasawa_ordL_mul _ _ hb0 ha0
    rw [hprod, ordL_one', ordL_congr (hσv _)] at h
    omega
  unfold chiDeltaU
  rw [← hT]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  have hrest : ∀ i ∈ Finset.univ.erase k,
      (if h : i.val < n then (α i : ℂ) ^ ordL ((((y⁻¹ * t * y : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨i.val, h⟩ ⟨i.val, h⟩) *
        (q : ℂ) ^ (-(ordL ((((y⁻¹ * t * y : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨i.val, h⟩ ⟨i.val, h⟩)) *
          ((n : ℤ) - 1 - 2 * (i.val : ℤ))) else 1) =
      (if h : i.val < n then (actU k α i : ℂ) ^ ordL (T ⟨i.val, h⟩ ⟨i.val, h⟩) *
        (q : ℂ) ^ (-(ordL (T ⟨i.val, h⟩ ⟨i.val, h⟩)) * ((n : ℤ) - 1 - 2 * (i.val : ℤ))) else 1) := by
    intro i hi
    have hik : i ≠ k := Finset.ne_of_mem_erase hi
    have hin : i.val < n := by have := i.2; omega
    rw [dif_pos hin, dif_pos hin, hdiag, hact, Function.update_of_ne hik]
    have hfix : simpleU k ⟨i.val, hin⟩ = ⟨i.val, hin⟩ := by
      rw [hs]
      refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
      · intro h; apply hik; ext; simpa [lo] using congrArg Fin.val h
      · intro h; have := congrArg Fin.val h; rw [hrev] at this; have := i.2; simp at *; omega
    rw [hfix]
  rw [Finset.prod_congr rfl hrest]
  have hkn : k.val < n := by omega
  rw [dif_pos hkn, dif_pos hkn, hdiag, hact]
  beta_reduce
  rw [Function.update_self]
  have hlk : (⟨k.val, hkn⟩ : Fin n) = lo k := rfl
  rw [hlk, hs, Equiv.swap_apply_left, hord]
  have he : ((n : ℤ) - 1 - 2 * (k.val : ℤ)) = 1 := by
    have : (n : ℤ) = m + m := by exact_mod_cast hm
    have h2 : (k.val : ℤ) + 1 = m := by exact_mod_cast hkv
    omega
  rw [he]
  set r := ordL (T (lo k) (lo k))
  have hα : (α k : ℂ) ≠ 0 := (α k).ne_zero
  have hq1 : (q : ℂ) ^ (-(-r) * (1 : ℤ)) * (q : ℂ) ^ (-2 * r) = (q : ℂ) ^ (-r * (1 : ℤ)) := by
    rw [← zpow_add₀ hq]; congr 1; ring
  rw [Units.val_inv_eq_inv_val, inv_zpow', ← hq1]
  ring

end GKUnitary

end GlobalTheory
