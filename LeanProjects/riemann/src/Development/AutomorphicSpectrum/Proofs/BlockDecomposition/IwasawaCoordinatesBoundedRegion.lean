import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal

namespace GlobalTheory.CompanionTheory.LFCoords

open Ad3

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem modulus_add_le_max (x y : F) :
    (modulus (x + y) : ℝ) ≤ max (modulus x : ℝ) (modulus y : ℝ) := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rcases le_total (ord x) (ord y) with h | h
  · have hmem : x + y ∈ valBall F (ord x) :=
      add_mem mem_valBall_ord (valBall_antitone h mem_valBall_ord)
    have h1 := modulus_le_of_mem_valBall hmem
    rw [← modulus_of_ne_zero hx] at h1
    have h1' : (modulus (x + y) : ℝ) ≤ modulus x := by exact_mod_cast h1
    exact h1'.trans (le_max_left _ _)
  · have hmem : x + y ∈ valBall F (ord y) :=
      add_mem (valBall_antitone h mem_valBall_ord) mem_valBall_ord
    have h1 := modulus_le_of_mem_valBall hmem
    rw [← modulus_of_ne_zero hy] at h1
    have h1' : (modulus (x + y) : ℝ) ≤ modulus y := by exact_mod_cast h1
    exact h1'.trans (le_max_right _ _)

theorem modulus_neg_self (x : F) : modulus (-x) = modulus x := by
  by_cases hx : x = 0
  · simp [hx]
  rw [modulus_of_ne_zero hx, modulus_of_ne_zero (neg_ne_zero.mpr hx)]
  simp [ord, Valuation.map_neg]

theorem modulus_le_one_real {x : F} (hx : x ∈ 𝒪[F]) : (modulus x : ℝ) ≤ 1 := by
  exact_mod_cast modulus_le_one_iff.2 hx

theorem modulus_mul_entry_le {κ k : Matrix (Fin 2) (Fin 2) F} (hκ : ∀ i j, κ i j ∈ 𝒪[F]) {B : ℝ}
    (hk : ∀ i j, (modulus (k i j) : ℝ) ≤ B) (i l : Fin 2) : (modulus ((κ * k) i l) : ℝ) ≤ B := by
  have term : ∀ j, (modulus (κ i j * k j l) : ℝ) ≤ B := fun j => by
    rw [modulus_mul, NNReal.coe_mul]
    calc (modulus (κ i j) : ℝ) * modulus (k j l) ≤ 1 * modulus (k j l) :=
          mul_le_mul_of_nonneg_right (modulus_le_one_real (hκ i j)) (NNReal.coe_nonneg _)
      _ ≤ B := by simpa using hk j l
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact (modulus_add_le_max _ _).trans (max_le (term 0) (term 1))

theorem exists_one_le_modulus {κ : GL (Fin 2) F} (hκ : κ ∈ GLnLocal.integralGL F 2) :
    ∃ j, 1 ≤ (modulus ((κ : Matrix (Fin 2) (Fin 2) F) 1 j) : ℝ) := by
  have hinv := ((GLnLocal.mem_integralGL_iff F 2).1 hκ).2
  have e : (κ : Matrix (Fin 2) (Fin 2) F) * ((κ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e11 := congrFun (congrFun e 1) 1
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at e11
  by_contra hcon
  push_neg at hcon
  have term : ∀ j, (modulus ((κ : Matrix (Fin 2) (Fin 2) F) 1 j *
      ((κ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) j 1) : ℝ) < 1 := fun j => by
    rw [modulus_mul, NNReal.coe_mul]
    calc (modulus ((κ : Matrix (Fin 2) (Fin 2) F) 1 j) : ℝ) *
          modulus (((κ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) j 1)
        ≤ (modulus ((κ : Matrix (Fin 2) (Fin 2) F) 1 j) : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (modulus_le_one_real (hinv j 1)) (NNReal.coe_nonneg _)
      _ < 1 := by simpa using hcon j
  have h := modulus_add_le_max ((κ : Matrix (Fin 2) (Fin 2) F) 1 0 *
      ((κ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1)
    ((κ : Matrix (Fin 2) (Fin 2) F) 1 1 * ((κ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1)
  rw [e11, modulus_one, NNReal.coe_one] at h
  exact absurd h (not_le.2 (max_lt (term 0) (term 1)))

theorem modulus_unif_zpow (m : ℤ) :
    (modulus ((unifUnit F ^ m : Fˣ) : F) : ℝ) = (residueCard F : ℝ) ^ (-m) := by
  rw [modulus_of_ne_zero (Units.ne_zero _), ord_unifUnit_zpow, NNReal.coe_zpow, NNReal.coe_natCast]

theorem modulus_unif_zpow_inv (m : ℤ) :
    (modulus (((unifUnit F ^ m)⁻¹ : Fˣ) : F) : ℝ) = (residueCard F : ℝ) ^ m := by
  rw [Units.val_inv_eq_inv_val, modulus_inv, NNReal.coe_inv, modulus_unif_zpow, _root_.zpow_neg, inv_inv]

theorem val_inv_uni_dg (x : F) (a b : Fˣ) :
    (((uni2 x * dg2 a b)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![((a⁻¹ : Fˣ) : F), ((a⁻¹ : Fˣ) : F) * -x; 0, ((b⁻¹ : Fˣ) : F)] := by
  have h : (((uni2 x * dg2 a b)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![((a⁻¹ : Fˣ) : F), 0; 0, ((b⁻¹ : Fˣ) : F)] * !![1, -x; 0, 1] := by
    rw [_root_.mul_inv_rev, Units.val_mul]
    rfl
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem val_uni_dg_mul_last (x : F) (a b : Fˣ) (κ : GL (Fin 2) F) (j : Fin 2) :
    ((uni2 x * dg2 a b * κ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j =
      (b : F) * (κ : Matrix (Fin 2) (Fin 2) F) 1 j := by
  have h : ((uni2 x * dg2 a b * κ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (!![1, x; 0, 1] * !![(a : F), 0; 0, (b : F)]) * (κ : Matrix (Fin 2) (Fin 2) F) := by
    rw [Units.val_mul, Units.val_mul]
    rfl
  rw [h]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

end

theorem coords : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (x : F) (m n L : ℤ) (κ : GL (Fin 2) F) (R : ℝ) (t : Fˣ), κ ∈ GLnLocal.integralGL F 2 → R ≤ (residueCard F : ℝ) ^ L → (Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ)⁻¹ ∈ Ad3.LFS.om R t → m ≤ L ∧ n ≤ L ∧ (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (L - m) ∧ (modulus (t : F) : ℝ) * (residueCard F : ℝ) ^ (-n) ≤ (residueCard F : ℝ) ^ L := by
  intro F _ _ _ _ x m n L κ R t hκ hR hk
  obtain ⟨h1, h2⟩ := hk
  have hq : (1 : ℝ) < residueCard F := by exact_mod_cast one_lt_residueCard (K := F)
  have hq0 : (0 : ℝ) < residueCard F := zero_lt_one.trans hq
  set a : GL (Fin 2) F := uni2 x * dg2 (unifUnit F ^ m) (unifUnit F ^ n) with ha
  have hent := ((GLnLocal.mem_integralGL_iff F 2).1 hκ).1

  have hmul : (κ : Matrix (Fin 2) (Fin 2) F) * (((a * κ)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [← Units.val_mul, _root_.mul_inv_rev, mul_inv_cancel_left]
  have hb : ∀ i l, (modulus (((a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i l) : ℝ) ≤
      (residueCard F : ℝ) ^ L := fun i l => by
    rw [← hmul]
    exact modulus_mul_entry_le hent (fun i j => (h1 i j).trans hR) i l
  have hval : ((a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = _ := val_inv_uni_dg x _ _
  have b00 := hb 0 0
  have b01 := hb 0 1
  have b11 := hb 1 1
  rw [hval] at b00 b01 b11
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at b00 b01 b11
  rw [modulus_unif_zpow_inv] at b00 b11
  rw [modulus_mul, NNReal.coe_mul, modulus_unif_zpow_inv, modulus_neg_self] at b01
  refine ⟨(zpow_le_zpow_iff_right₀ hq).1 b00, (zpow_le_zpow_iff_right₀ hq).1 b11, ?_, ?_⟩
  · rw [zpow_sub₀ hq0.ne', le_div_iff₀ (zpow_pos hq0 m), mul_comm]
    exact b01
  · obtain ⟨j, hj⟩ := exists_one_le_modulus hκ
    have h3 := h2 j
    rw [inv_inv, ha, val_uni_dg_mul_last, modulus_mul, modulus_mul, NNReal.coe_mul, NNReal.coe_mul,
      modulus_unif_zpow] at h3
    have hnn : 0 ≤ (modulus (t : F) : ℝ) * (residueCard F : ℝ) ^ (-n) :=
      mul_nonneg (NNReal.coe_nonneg _) (zpow_pos hq0 _).le
    calc (modulus (t : F) : ℝ) * (residueCard F : ℝ) ^ (-n)
        ≤ (modulus (t : F) : ℝ) * (residueCard F : ℝ) ^ (-n) * modulus ((κ : Matrix (Fin 2) (Fin 2) F) 1 j) :=
          le_mul_of_one_le_right hnn hj
      _ = (modulus (t : F) : ℝ) * ((residueCard F : ℝ) ^ (-n) * modulus ((κ : Matrix (Fin 2) (Fin 2) F) 1 j)) := by ring
      _ ≤ R := h3
      _ ≤ _ := hR

end GlobalTheory.CompanionTheory.LFCoords
