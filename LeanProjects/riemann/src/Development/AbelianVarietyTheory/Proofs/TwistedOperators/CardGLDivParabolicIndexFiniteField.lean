import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

namespace GlobalTheory.Twist.GLIndexLoc

theorem card_GL_real_eq (κ : Type) [Field κ] [Finite κ] (n : ℕ) :
    (Nat.card (GL (Fin n) κ) : ℝ) =
      (Nat.card κ : ℝ) ^ (n ^ 2) * ∏ i ∈ Finset.Ioc 0 n, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) := by
  haveI := Fintype.ofFinite κ
  have hq1 : 1 ≤ Nat.card κ := Nat.one_le_iff_ne_zero.mpr (Nat.card_pos).ne'
  have hq0 : (Nat.card κ : ℝ) ≠ 0 := by positivity
  rw [Matrix.card_GL_field, Nat.cast_prod, ← Nat.card_eq_fintype_card]
  rw [Fin.prod_univ_eq_prod_range (fun i => ((Nat.card κ ^ n - Nat.card κ ^ i : ℕ) : ℝ)) n]
  rw [← Finset.prod_range_reflect]
  have hIoc : Finset.Ioc 0 n = (Finset.range n).map ⟨(· + 1), add_left_injective 1⟩ := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨y, hy, rfl⟩; omega
  rw [hIoc, Finset.prod_map, sq, pow_mul,
    show ((Nat.card κ : ℝ) ^ n) ^ n = ∏ _j ∈ Finset.range n, (Nat.card κ : ℝ) ^ n by simp,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j hj => ?_)
  have hj' : j < n := Finset.mem_range.mp hj
  have hle : Nat.card κ ^ (n - 1 - j) ≤ Nat.card κ ^ n := Nat.pow_le_pow_right hq1 (by omega)
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one]
  congr 1
  have hsplit : (Nat.card κ : ℝ) ^ n = (Nat.card κ : ℝ) ^ (n - 1 - j) * (Nat.card κ : ℝ) ^ (j + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq0), mul_one]

theorem index_loc : ∀ (κ : Type) [Field κ] [Finite κ] (n r t : ℕ), n = r + t → (Nat.card (GL (Fin n) κ) : ℝ) / ((Nat.card (GL (Fin t) κ) : ℝ) * (Nat.card κ : ℝ) ^ (r * t)) * ((Nat.card κ : ℝ) ^ (r ^ 2 + r * t))⁻¹ = ∏ i ∈ Finset.Ioc t n, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) := by
  intro κ _ _ n r t hn
  haveI := Fintype.ofFinite κ
  have hq2 : (2 : ℝ) ≤ Nat.card κ := by
    have := Fintype.one_lt_card (α := κ)
    rw [← Nat.card_eq_fintype_card] at this
    exact_mod_cast this
  have hq0 : (Nat.card κ : ℝ) ≠ 0 := by positivity
  have hP : ∏ i ∈ Finset.Ioc 0 t, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun i hi => ?_)
    have hi1 : 1 ≤ i := (Finset.mem_Ioc.mp hi).1
    have : (2 : ℝ) ≤ (Nat.card κ : ℝ) ^ i :=
      le_trans hq2 (le_self_pow₀ (by linarith) (by omega))
    have : ((Nat.card κ : ℝ) ^ i)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    linarith
  rw [card_GL_real_eq, card_GL_real_eq,
    ← Finset.prod_Ioc_consecutive _ (Nat.zero_le t) (show t ≤ n by omega)]
  have hpow : (Nat.card κ : ℝ) ^ (n ^ 2) =
      (Nat.card κ : ℝ) ^ (t ^ 2) * (Nat.card κ : ℝ) ^ (r * t) * (Nat.card κ : ℝ) ^ (r ^ 2 + r * t) := by
    rw [← pow_add, ← pow_add]; congr 1; subst hn; ring
  rw [hpow]
  generalize ∏ i ∈ Finset.Ioc 0 t, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) = P at hP ⊢
  generalize ∏ i ∈ Finset.Ioc t n, (1 - ((Nat.card κ : ℝ) ^ i)⁻¹) = Q
  have h1 : (Nat.card κ : ℝ) ^ (t ^ 2) ≠ 0 := pow_ne_zero _ hq0
  have h2 : (Nat.card κ : ℝ) ^ (r * t) ≠ 0 := pow_ne_zero _ hq0
  have h3 : (Nat.card κ : ℝ) ^ (r ^ 2 + r * t) ≠ 0 := pow_ne_zero _ hq0
  field_simp

end GlobalTheory.Twist.GLIndexLoc
