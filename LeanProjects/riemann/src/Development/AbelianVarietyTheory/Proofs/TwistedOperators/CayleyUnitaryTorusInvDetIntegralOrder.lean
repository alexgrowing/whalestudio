import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CayleyTorus

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem v_one_add_inv_unif {ϖ : L}
    (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    Valued.v (1 + ϖ⁻¹) = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h1 : Valued.v (ϖ⁻¹) = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [map_inv₀, hv]; rfl
  rw [Valuation.map_add_eq_of_lt_right, h1]
  rw [h1, map_one]; exact WithZero.coe_lt_coe.2 (by decide)

theorem v_one_add_unif {ϖ : L}
    (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    Valued.v (1 + ϖ) = 1 := by
  rw [Valuation.map_add_eq_of_lt_left, map_one]
  rw [hv, map_one]; exact WithZero.coe_lt_coe.2 (by decide)

theorem inv_diagonal_field {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → L) (hf : ∀ i, f i ≠ 0) :
    (Matrix.diagonal f)⁻¹ = Matrix.diagonal (fun i => (f i)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; ext i; exact inv_mul_cancel₀ (hf i)

theorem cayley_torus_inv : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → Valued.v (2 : L) = 1 → ∀ (n' : ℕ) (k : Fin (n' / 2)) (t : GU σ n'), t.1.1 = tMat ϖ n' (n' / 2) (Pi.single k 1) → (1 + (t⁻¹).1.1).det ≠ 0 ∧ (1 + (t⁻¹).1.1)⁻¹ ∈ intMat L (Fin n') (Fin n') ∧ ordL (1 + (t⁻¹).1.1).det = -1 := by
  intro L _ _ ϖ σ q hU h2 n' k t ht
  have hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
    hU.2.2.2.1
  have hϖ : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hv; exact WithZero.zero_ne_coe hv
  set d : Fin n' → L := fun i => if h : i.val < n' / 2 then ϖ ^ ((Pi.single k (1 : ℤ) : Fin (n' / 2) → ℤ) ⟨i.val, h⟩)
    else if h' : n' - n' / 2 ≤ i.val ∧ n' - 1 - i.val < n' / 2 then
      ϖ ^ (-((Pi.single k (1 : ℤ) : Fin (n' / 2) → ℤ) ⟨n' - 1 - i.val, h'.2⟩)) else 1 with hd
  have htd : t.1.1 = Matrix.diagonal d := ht
  have hdne : ∀ i, d i ≠ 0 := by
    intro i; simp only [hd]; split_ifs <;> simp [zpow_ne_zero, hϖ]
  have hinv : (t⁻¹).1.1 = Matrix.diagonal (fun i => (d i)⁻¹) := by
    rw [show (t⁻¹).1.1 = (t.1.1)⁻¹ by simp [Matrix.coe_units_inv], htd, inv_diagonal_field d hdne]
  have hone : 1 + (t⁻¹).1.1 = Matrix.diagonal (fun i => 1 + (d i)⁻¹) := by
    rw [hinv, ← Matrix.diagonal_one, Matrix.diagonal_add]
  have hk : k.val < n' := by omega
  have hval : ∀ i, Valued.v (1 + (d i)⁻¹) =
      if i = ⟨k.val, hk⟩ then ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) else 1 := by
    intro i
    by_cases hi : i.val < n' / 2
    · by_cases hik : (⟨i.val, hi⟩ : Fin (n' / 2)) = k
      · have : d i = ϖ := by simp only [hd, dif_pos hi, hik, Pi.single_eq_same, zpow_one]
        rw [this, v_one_add_inv_unif hv, if_pos (show i = ⟨k.val, hk⟩ from Fin.ext (by have e := congrArg Fin.val hik; simpa using e))]
      · have : d i = 1 := by simp only [hd, dif_pos hi, Pi.single_eq_of_ne hik, zpow_zero]
        rw [this, inv_one, one_add_one_eq_two, h2, if_neg]
        intro e; apply hik; ext; simp [e]
    · rw [if_neg (fun e => hi (by rw [e]; exact k.2))]
      by_cases h' : n' - n' / 2 ≤ i.val ∧ n' - 1 - i.val < n' / 2
      · by_cases hik : (⟨n' - 1 - i.val, h'.2⟩ : Fin (n' / 2)) = k
        · have : d i = ϖ⁻¹ := by simp only [hd, dif_neg hi, dif_pos h', hik, Pi.single_eq_same, _root_.zpow_neg, zpow_one]
          rw [this, inv_inv, v_one_add_unif hv]
        · have : d i = 1 := by simp only [hd, dif_neg hi, dif_pos h', Pi.single_eq_of_ne hik, neg_zero, zpow_zero]
          rw [this, inv_one, one_add_one_eq_two, h2]
      · have : d i = 1 := by simp only [hd, dif_neg hi, dif_neg h']
        rw [this, inv_one, one_add_one_eq_two, h2]
  have hfne : ∀ i, 1 + (d i)⁻¹ ≠ 0 := by
    intro i e
    have := hval i
    rw [e, map_zero] at this
    split_ifs at this with h
    · exact WithZero.zero_ne_coe this
    · exact zero_ne_one this
  have hdet : Valued.v (1 + (t⁻¹).1.1).det =
      ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [hone, Matrix.det_diagonal, map_prod]
    simp_rw [hval]
    rw [Finset.prod_ite_eq']; simp
  refine ⟨?_, ?_, ?_⟩
  · intro e; rw [e, map_zero] at hdet; exact WithZero.zero_ne_coe hdet
  · rw [hone, inv_diagonal_field _ hfne]
    intro i j
    rw [mem_intL, Matrix.diagonal_apply]
    split_ifs with hij
    · rw [map_inv₀, hval i]
      split_ifs
      · rw [← WithZero.coe_inv]; exact WithZero.coe_le_coe.2 (by decide)
      · simp
    · simp
  · have hne : Valued.v (1 + (t⁻¹).1.1).det ≠ 0 := by rw [hdet]; exact WithZero.coe_ne_zero
    have hu : WithZero.unzero hne = Multiplicative.ofAdd (1 : ℤ) :=
      WithZero.coe_inj.mp ((WithZero.coe_unzero hne).trans hdet)
    rw [ordL, dif_neg hne, hu]; rfl

end GlobalTheory.CayleyTorus
