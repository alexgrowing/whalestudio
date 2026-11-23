import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.SmoothedEisensteinCongrOfModEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.SmoothedEisensteinCoeffShiftSecondIndex
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem en_cg {M : ℕ} {g g' : SL(2, ℤ)}
    (h : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) g' =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) g) (i j : Fin 2) :
    en g' i j ≡ en g i j [ZMOD M] := by
  rw [← ZMod.intCast_eq_intCast_iff]
  have := congrArg (fun A : SL(2, ZMod M) => (A : Matrix (Fin 2) (Fin 2) (ZMod M)) i j) h
  exact this

private theorem entries_mul_T_pow (g : SL(2, ℤ)) (b : ℕ) (i : Fin 2) :
    en (g * ModularGroup.T ^ b) i 0 = en g i 0 ∧
      en (g * ModularGroup.T ^ b) i 1 = en g i 1 + (b : ℤ) * en g i 0 := by
  have h := ModularGroup.coe_T_zpow (b : ℤ)
  rw [zpow_natCast] at h
  unfold en
  rw [Matrix.SpecialLinearGroup.coe_mul, h]
  constructor
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring

private theorem cmul_phase {K : Type} [Field K] [CharZero K] (ζ : K) (h0 : ζ ≠ 0) (e : ℤ) (f g f' g' : ℕ → K)
    (hf : ∀ n : ℕ, f' n = ζ ^ (e * (n : ℤ)) * f n) (hg : ∀ n : ℕ, g' n = ζ ^ (e * (n : ℤ)) * g n) (n : ℕ) :
    cmul f' g' n = ζ ^ (e * (n : ℤ)) * cmul f g n := by
  unfold cmul
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [hf, hg, Nat.cast_sub hi', show e * (n : ℤ) = e * (i : ℤ) + e * ((n : ℤ) - (i : ℤ)) by ring,
    zpow_add₀ h0]
  ring

theorem UpperTheory.cmul_smF_invariant_of_congruent_mul_T_pow :
    ∀ {K : Type} [Field K] [CharZero K] (ζ : K) (l L N : ℕ) (x : ZMod N) (c d w M : ℕ) [NeZero M], 0 < N → 0 < l → ζ ^ (N * l ^ L) = 1 → N * l ^ L ∣ M → ∀ (b : ℕ) (g g' : SL(2, ℤ)), Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) g' = Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (g * ModularGroup.T ^ b) → ∀ i : ℕ, cmul (smF (c : ℤ) (w + 1) (N * l ^ L) ζ (en g' 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L)) ((N : ℤ) ^ 2 * en g' 0 1)) (smF (d : ℤ) 1 (N * l ^ L) ζ (en g' 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g' 1 0) ((N : ℤ) * en g' 1 1)) (l ^ L * i) = cmul (smF (c : ℤ) (w + 1) (N * l ^ L) ζ (en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L)) ((N : ℤ) ^ 2 * en g 0 1)) (smF (d : ℤ) 1 (N * l ^ L) ζ (en g 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g 1 0) ((N : ℤ) * en g 1 1)) (l ^ L * i) := by
  intro K _ _ ζ l L N x c d w M _ hN hl hζ hM b g g' h i
  have hpos : 0 < N * l ^ L := Nat.mul_pos hN (pow_pos hl L)
  have h0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hpos.ne'] at hζ
    exact zero_ne_one hζ
  have hc : ∀ i j, en g' i j ≡ en (g * ModularGroup.T ^ b) i j [ZMOD (N * l ^ L : ℕ)] := fun i j =>
    (en_cg h i j).of_dvd (Int.natCast_dvd_natCast.mpr hM)
  have h00 := hc 0 0
  have h01 := hc 0 1
  have h10 := hc 1 0
  have h11 := hc 1 1
  rw [(entries_mul_T_pow g b _).1] at h00 h10
  rw [(entries_mul_T_pow g b _).2] at h01 h11
  have e1 : smF (c : ℤ) (w + 1) (N * l ^ L) ζ
      (en g' 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L)) ((N : ℤ) ^ 2 * en g' 0 1) =
      smF (c : ℤ) (w + 1) (N * l ^ L) ζ
      (en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L)) ((N : ℤ) ^ 2 * en g 0 1 +
        ((N : ℤ) * b) * (en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L))) := by
    refine UpperTheory.smoothedEisenstein_congr_of_modEq _ _ _ ζ hpos hζ (h00.mul_right _) ((h01.mul_left _).trans ?_)
    refine Int.modEq_iff_dvd.2 ⟨b * en g 0 0 * (x.val : ℤ) * (topT l L N : ℤ), ?_⟩
    push_cast
    ring
  have e2 : smF (d : ℤ) 1 (N * l ^ L) ζ
      (en g' 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g' 1 0) ((N : ℤ) * en g' 1 1) =
      smF (d : ℤ) 1 (N * l ^ L) ζ
      (en g 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g 1 0) ((N : ℤ) * en g 1 1 +
        ((N : ℤ) * b) * (en g 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g 1 0)) := by
    refine UpperTheory.smoothedEisenstein_congr_of_modEq _ _ _ ζ hpos hζ (((h00.mul_right _).mul_right _).add h10) ((h11.mul_left _).trans ?_)
    refine Int.modEq_iff_dvd.2 ⟨b * en g 0 0 * (topT l L N : ℤ), ?_⟩
    push_cast
    ring
  rw [e1, e2, cmul_phase ζ h0 ((N : ℤ) * b) _ _ _ _
    (UpperTheory.smoothedEisensteinCoeff_shift_second_index _ _ _ ζ _ _ _ hpos hζ) (UpperTheory.smoothedEisensteinCoeff_shift_second_index _ _ _ ζ _ _ _ hpos hζ)]
  have : ζ ^ ((N : ℤ) * b * ((l ^ L * i : ℕ) : ℤ)) = 1 := by
    rw [show (N : ℤ) * b * ((l ^ L * i : ℕ) : ℤ) = ((N * l ^ L * (b * i) : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, pow_mul, hζ, one_pow]
  rw [this, one_mul]
