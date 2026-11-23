import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupCosetDecomposition
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.IwasawaShell

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem q_pos : (0 : ℝ) < residueCard F := by
  have h : 1 < residueCard F := one_lt_residueCard
  exact_mod_cast (by omega : 0 < residueCard F)

theorem modulus_unif_zpow (k : ℤ) :
    (modulus (((unifUnit F) ^ k : Fˣ) : F) : ℝ) = (residueCard F : ℝ) ^ (-k) := by
  have hq : (residueCard F : ℝ) ≠ 0 := q_pos.ne'
  have hu : (modulus ((unifUnit F : Fˣ) : F) : ℝ) = (residueCard F : ℝ)⁻¹ := by
    rw [modulus, if_neg (unifUnit F).ne_zero, ord_unifUnit]
    simp
  have hui : (modulus (((unifUnit F)⁻¹ : Fˣ) : F) : ℝ) = (residueCard F : ℝ) := by
    rw [Units.val_inv_eq_inv_val, modulus_inv]
    push_cast
    rw [hu, inv_inv]
  induction k using Int.induction_on with
  | zero => simp [modulus_one]
  | succ i ih =>
    rw [_root_.zpow_add_one, Units.val_mul, modulus_mul, NNReal.coe_mul, ih, hu, neg_add, zpow_add₀ hq, _root_.zpow_neg_one]
  | pred i ih =>
    rw [_root_.zpow_sub_one, Units.val_mul, modulus_mul, NNReal.coe_mul, ih, hui, neg_sub, sub_eq_add_neg, add_comm (1 : ℤ), zpow_add₀ hq, zpow_one]

theorem mem_integer_of_modulus_le (k : ℤ) {x : F}
    (hx : (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ k) :
    (((unifUnit F) ^ k : Fˣ) : F) * x ∈ 𝒪[F] := by
  have hq : (residueCard F : ℝ) ≠ 0 := q_pos.ne'
  rw [← modulus_le_one_iff, ← NNReal.coe_le_coe, modulus_mul, NNReal.coe_mul, NNReal.coe_one,
    modulus_unif_zpow]
  calc (residueCard F : ℝ) ^ (-k) * (modulus x : ℝ)
      ≤ (residueCard F : ℝ) ^ (-k) * (residueCard F : ℝ) ^ k :=
        mul_le_mul_of_nonneg_left hx (zpow_nonneg q_pos.le _)
    _ = 1 := by rw [← zpow_add₀ hq]; simp

theorem uni2_mul_uni2_eq_uni2_add (x y : F) : Ad3.uni2 x * Ad3.uni2 y = Ad3.uni2 (x + y) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ad3.uni2, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem unipotent_integral_mem_compact {y : F} (hy : y ∈ 𝒪[F]) : Ad3.uni2 y ∈ GLnLocal.integralGL F 2 := by
  rw [GLnLocal.mem_integralGL_iff]
  have h0 : (0 : F) ∈ 𝒪[F] := zero_mem _
  have h1 : (1 : F) ∈ 𝒪[F] := one_mem _
  have hn : -y ∈ 𝒪[F] := neg_mem hy
  have hv : ((Ad3.uni2 y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, y; 0, 1] := rfl
  have hi : (((Ad3.uni2 y)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, -y; 0, 1] := rfl
  rw [hv, hi]
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;> simpa using by assumption

theorem unipotent_mul_torus_commute (α β : Fˣ) (x : F) :
    Ad3.uni2 x * Ad3.dg2 α β = Ad3.dg2 α β * Ad3.uni2 ((α : F)⁻¹ * β * x) := by
  have hα : (α : F) ≠ 0 := α.ne_zero
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ad3.uni2, Ad3.dg2, Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

variable (F) in

def Q (j : ℤ) : Set (GL (Fin 2) F) :=
  {g | ∃ y : F, (modulus y : ℝ) ≤ (residueCard F : ℝ) ^ j ∧
    ∃ κ ∈ GLnLocal.integralGL F 2, g = Ad3.uni2 y * κ}

theorem Q_zero_subset : Q F 0 ⊆ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) := by
  rintro g ⟨y, hy, κ, hκ, rfl⟩
  have hy' : y ∈ 𝒪[F] := by
    rw [← modulus_le_one_iff, ← NNReal.coe_le_coe]
    simpa using hy
  exact mul_mem (unipotent_integral_mem_compact hy') hκ

theorem Q_succ_subset {ϖ : Fˣ} {B : Finset F} (h : Ad3.R.Reps ϖ B) (j : ℕ) :
    Q F ((j + 1 : ℕ) : ℤ) ⊆ ⋃ b ∈ B,
      (fun g => Ad3.uni2 (-((((unifUnit F) ^ (-((j + 1 : ℕ) : ℤ)) : Fˣ) : F) * b)) * g) ⁻¹' Q F j := by
  have hq : (residueCard F : ℝ) ≠ 0 := q_pos.ne'
  rintro g ⟨y, hy, κ, hκ, rfl⟩
  set k : ℤ := ((j + 1 : ℕ) : ℤ) with hk
  have hX := mem_integer_of_modulus_le k hy
  set X : F := (((unifUnit F) ^ k : Fˣ) : F) * y with hXdef
  obtain ⟨b, ⟨hb, hb2⟩, -⟩ := h.2.2 X hX
  have hϖ : modulus (ϖ : F) = (residueCard F : NNReal)⁻¹ := by
    rw [modulus, if_neg ϖ.ne_zero, h.1]
    simp
  have h1 := modulus_le_one_iff.mpr hb2
  rw [modulus_mul, Units.val_inv_eq_inv_val, modulus_inv, hϖ, inv_inv] at h1
  have h2 : (residueCard F : ℝ) * (modulus (X - b) : ℝ) ≤ 1 := by exact_mod_cast h1
  simp only [Set.mem_iUnion, Set.mem_preimage]
  refine ⟨b, hb, y - (((unifUnit F) ^ (-k) : Fˣ) : F) * b, ?_, κ, hκ, ?_⟩
  · have e : y - (((unifUnit F) ^ (-k) : Fˣ) : F) * b = (((unifUnit F) ^ (-k) : Fˣ) : F) * (X - b) := by
      rw [mul_sub, hXdef, ← mul_assoc, ← Units.val_mul, ← _root_.zpow_add]
      simp
    rw [e, modulus_mul, NNReal.coe_mul, modulus_unif_zpow, neg_neg, hk]
    push_cast
    rw [zpow_add₀ hq, zpow_one, mul_assoc]
    have hp : (0 : ℝ) ≤ (residueCard F : ℝ) ^ (j : ℤ) := zpow_nonneg q_pos.le _
    calc (residueCard F : ℝ) ^ (j : ℤ) * ((residueCard F : ℝ) * (modulus (X - b) : ℝ))
        ≤ (residueCard F : ℝ) ^ (j : ℤ) * 1 := mul_le_mul_of_nonneg_left h2 hp
      _ = (residueCard F : ℝ) ^ (j : ℤ) := mul_one _
  · rw [← mul_assoc, uni2_mul_uni2_eq_uni2_add]
    congr 2
    ring

theorem measure_Q_le (μ : Measure (GL (Fin 2) F)) [μ.IsMulLeftInvariant] (j : ℕ) :
    μ (Q F j) ≤ (residueCard F : ℝ≥0∞) ^ j * μ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) := by
  obtain ⟨ϖ, B, hB⟩ := GlobalTheory.CompanionTheory.RankinStepC.reps_exists (F := F)
  induction j with
  | zero =>
    simpa using measure_mono (μ := μ) Q_zero_subset
  | succ j ih =>
    calc μ (Q F ((j + 1 : ℕ) : ℤ))
        ≤ μ (⋃ b ∈ B,
            (fun g => Ad3.uni2 (-((((unifUnit F) ^ (-((j + 1 : ℕ) : ℤ)) : Fˣ) : F) * b)) * g) ⁻¹' Q F j) :=
          measure_mono (Q_succ_subset hB j)
      _ ≤ ∑ b ∈ B, μ
            ((fun g => Ad3.uni2 (-((((unifUnit F) ^ (-((j + 1 : ℕ) : ℤ)) : Fˣ) : F) * b)) * g) ⁻¹' Q F j) :=
          measure_biUnion_finset_le _ _
      _ = (residueCard F : ℝ≥0∞) * μ (Q F j) := by
          simp only [measure_preimage_mul, Finset.sum_const, nsmul_eq_mul,
            GlobalTheory.CompanionTheory.RankinStepC.reps_card hB]
      _ ≤ (residueCard F : ℝ≥0∞) *
            ((residueCard F : ℝ≥0∞) ^ j * μ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F))) := by
          gcongr
      _ = (residueCard F : ℝ≥0∞) ^ (j + 1) * μ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) := by
          rw [pow_succ', mul_assoc]

theorem shell_subset (m n L : ℤ) :
    {g : GL (Fin 2) F | ∃ x : F, (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (L - m) ∧
      ∃ κ ∈ GLnLocal.integralGL F 2, g = Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ} ⊆
    (fun g => (Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n))⁻¹ * g) ⁻¹' Q F (L - n) := by
  have hq : (residueCard F : ℝ) ≠ 0 := q_pos.ne'
  rintro g ⟨x, hx, κ, hκ, rfl⟩
  refine ⟨(((unifUnit F ^ m : Fˣ) : F))⁻¹ * ((unifUnit F ^ n : Fˣ) : F) * x, ?_, κ, hκ, ?_⟩
  · rw [modulus_mul, modulus_mul, modulus_inv, NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_inv,
      modulus_unif_zpow, modulus_unif_zpow, ← _root_.zpow_neg, neg_neg, ← zpow_add₀ hq]
    have e : L - n = (m + -n) + (L - m) := by ring
    rw [e, zpow_add₀ hq (m + -n)]
    exact mul_le_mul_of_nonneg_left hx (zpow_nonneg q_pos.le _)
  · rw [unipotent_mul_torus_commute]
    simp [mul_assoc]

theorem shell_open_volume : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (μ : Measure (GL (Fin 2) F)) [μ.IsMulLeftInvariant] (m n L : ℤ), IsOpen {g : GL (Fin 2) F | ∃ x : F, (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (L - m) ∧ ∃ κ ∈ GLnLocal.integralGL F 2, g = Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ} ∧ (n ≤ L → μ {g : GL (Fin 2) F | ∃ x : F, (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (L - m) ∧ ∃ κ ∈ GLnLocal.integralGL F 2, g = Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ} ≤ ENNReal.ofReal ((residueCard F : ℝ) ^ (L - n)) * μ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F))) := by
  intro F _ _ _ _ μ _ m n L
  constructor
  · have e : {g : GL (Fin 2) F | ∃ x : F, (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (L - m) ∧
        ∃ κ ∈ GLnLocal.integralGL F 2, g = Ad3.uni2 x * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ} =
        ⋃ x : {x : F // (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (L - m)},
          (Homeomorph.mulLeft (Ad3.uni2 x.1 * Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n))) ''
            (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, Homeomorph.coe_mulLeft,
        Subtype.exists, SetLike.mem_coe, exists_prop]
      constructor
      · rintro ⟨x, hx, κ, hκ, rfl⟩
        exact ⟨x, hx, κ, hκ, rfl⟩
      · rintro ⟨x, hx, κ, hκ, rfl⟩
        exact ⟨x, hx, κ, hκ, rfl⟩
    rw [e]
    exact isOpen_iUnion fun x =>
      (Homeomorph.mulLeft _).isOpenMap _ (GLnLocal.isOpen_integralGL F 2)
  · intro hnL
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 hnL)
    calc _ ≤ μ ((fun g => (Ad3.dg2 (unifUnit F ^ m) (unifUnit F ^ n))⁻¹ * g) ⁻¹' Q F (L - n)) :=
          measure_mono (shell_subset m n L)
      _ = μ (Q F (L - n)) := measure_preimage_mul μ _ _
      _ = μ (Q F j) := by rw [hj]
      _ ≤ _ := measure_Q_le μ j
      _ = _ := by
          rw [hj, zpow_natCast, ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end GlobalTheory.CompanionTheory.IwasawaShell
