import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.SmoothedEisensteinCongrOfModEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.RingHomApplySmoothedEisensteinCoeff
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.gamma0_diamond_action_eq :
    ∀ {K : Type} [Field K] [CharZero K] (ζ : K) (l : ℕ) [Fact l.Prime] (L N : ℕ) [NeZero N] (x : ZMod N) (c d w : ℕ) (a : ℤ) (s : K →+* K) (u : ZMod (l ^ L)), ¬ l ∣ N → ζ ^ (N * l ^ L) = 1 → s (ζ ^ N) = (ζ ^ N) ^ u.val → ∀ g ∈ CongruenceSubgroup.Gamma0 N, ((en g 0 0 : ℤ) : ZMod N) = (a : ZMod N) → ∀ h : GL (Fin 2) (ZMod (l ^ L)), (h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) 0 0 = ((en g 0 0 : ℤ) : ZMod (l ^ L)) → (h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) 0 1 = u * (((N : ℤ) * en g 0 1 : ℤ) : ZMod (l ^ L)) → (N : ZMod (l ^ L)) * (h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) 1 0 = ((en g 1 0 : ℤ) : ZMod (l ^ L)) → (h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) 1 1 = u * ((en g 1 1 : ℤ) : ZMod (l ^ L)) → ∀ r : ℕ, s (cmul (smF (c : ℤ) (w + 1) (N * l ^ L) ζ (en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L)) ((N : ℤ) ^ 2 * en g 0 1)) (smF (d : ℤ) 1 (N * l ^ L) ζ (en g 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g 1 0) ((N : ℤ) * en g 1 1)) r) = cmul (smF (c : ℤ) (w + 1) (N * l ^ L) ζ (rowT N l L h 0 ((x.val : ℤ) * a * (topT l L N : ℤ), 0)).1 (rowT N l L h 0 ((x.val : ℤ) * a * (topT l L N : ℤ), 0)).2) (smF (d : ℤ) 1 (N * l ^ L) ζ (rowT N l L h 1 (a * (topT l L N : ℤ), 0)).1 (rowT N l L h 1 (a * (topT l L N : ℤ), 0)).2) r := by
  intro K _ _ ζ l hl L N _ x c d w a s u hlN hζ hs g hg ha h h00 h01 h10 h11 r
  have hP : 0 < l ^ L := pow_pos hl.out.pos L
  haveI : NeZero (l ^ L) := ⟨hP.ne'⟩
  have hM : 0 < N * l ^ L := Nat.mul_pos (NeZero.pos N) hP
  have h0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hζ
    exact zero_ne_one hζ
  have hz : ∀ k : ℤ, s (ζ ^ ((N : ℤ) * k)) = ζ ^ ((N : ℤ) * (u.val * k)) := by
    intro k
    rw [zpow_mul, map_zpow₀, zpow_natCast, hs, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  have ea : (N : ℤ) ∣ a - en g 0 0 := ((ZMod.intCast_eq_intCast_iff _ _ _).1 ha).dvd
  have eg : (N : ℤ) ∣ en g 1 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact CongruenceSubgroup.Gamma0_mem.1 hg
  have key : ∀ p q : ℤ, ((p : ℤ) : ZMod (l ^ L)) = (q : ZMod (l ^ L)) → (l : ℤ) ^ L ∣ q - p := by
    intro p q hpq
    have := ((ZMod.intCast_eq_intCast_iff _ _ _).1 hpq).dvd
    simpa using this
  have e00 := key (en g 0 0) ((h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) 0 0).val
    (by rw [Int.cast_natCast, ZMod.natCast_zmod_val, h00])
  have e01 := key (u.val * ((N : ℤ) * en g 0 1)) ((h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) 0 1).val
    (by rw [Int.cast_natCast, ZMod.natCast_zmod_val, h01, Int.cast_mul (u.val : ℤ), Int.cast_natCast, ZMod.natCast_zmod_val])
  have e11 := key (u.val * (en g 1 1)) ((h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) 1 1).val
    (by rw [Int.cast_natCast, ZMod.natCast_zmod_val, h11, Int.cast_mul (u.val : ℤ), Int.cast_natCast, ZMod.natCast_zmod_val])
  have e10 := key (en g 1 0) ((N : ℤ) * ((h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) 1 0).val)
    (by rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, h10])
  have hcop : IsCoprime (N : ℤ) ((l : ℤ) ^ L) :=
    (Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hlN).symm).pow_right
  have e10' : (N : ℤ) * (l : ℤ) ^ L ∣ (N : ℤ) * ((h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) 1 0).val - en g 1 0 :=
    hcop.mul_dvd (dvd_sub (dvd_mul_right _ _) eg) e10
  obtain ⟨k, hk⟩ := ea
  obtain ⟨k00, hk00⟩ := e00
  obtain ⟨k01, hk01⟩ := e01
  obtain ⟨k11, hk11⟩ := e11
  obtain ⟨k10, hk10⟩ := e10'
  have c1 : en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L) ≡
      (rowT N l L h 0 ((x.val : ℤ) * a * (topT l L N : ℤ), 0)).1 [ZMOD (N * l ^ L : ℕ)] := by
    refine Int.modEq_iff_dvd.2 ⟨k00 + (x.val : ℤ) * (topT l L N : ℤ) * k, ?_⟩
    simp only [rowT, Nat.cast_mul, Nat.cast_pow]
    linear_combination (N : ℤ) * hk00 + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L * hk
  have c2 : (N : ℤ) * (u.val * ((N : ℤ) * en g 0 1)) ≡
      (rowT N l L h 0 ((x.val : ℤ) * a * (topT l L N : ℤ), 0)).2 [ZMOD (N * l ^ L : ℕ)] := by
    refine Int.modEq_iff_dvd.2 ⟨k01, ?_⟩
    simp only [rowT, Nat.cast_mul, Nat.cast_pow]
    linear_combination (N : ℤ) * hk01
  have c3 : en g 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g 1 0 ≡
      (rowT N l L h 1 (a * (topT l L N : ℤ), 0)).1 [ZMOD (N * l ^ L : ℕ)] := by
    refine Int.modEq_iff_dvd.2 ⟨k10 + (topT l L N : ℤ) * k, ?_⟩
    simp only [rowT, Nat.cast_mul, Nat.cast_pow]
    linear_combination hk10 + (topT l L N : ℤ) * (l : ℤ) ^ L * hk
  have c4 : (N : ℤ) * (u.val * (en g 1 1)) ≡
      (rowT N l L h 1 (a * (topT l L N : ℤ), 0)).2 [ZMOD (N * l ^ L : ℕ)] := by
    refine Int.modEq_iff_dvd.2 ⟨k11, ?_⟩
    simp only [rowT, Nat.cast_mul, Nat.cast_pow]
    linear_combination (N : ℤ) * hk11
  rw [← UpperTheory.smoothedEisenstein_congr_of_modEq (c : ℤ) (w + 1) (N * l ^ L) ζ hM hζ c1 c2, ← UpperTheory.smoothedEisenstein_congr_of_modEq (d : ℤ) 1 (N * l ^ L) ζ hM hζ c3 c4]
  unfold cmul
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hz1 : s (ζ ^ ((N : ℤ) ^ 2 * en g 0 1)) = ζ ^ ((N : ℤ) * (u.val * ((N : ℤ) * en g 0 1))) := by
    rw [← hz, sq, mul_assoc]
  rw [map_mul, UpperTheory.ringHom_apply_smoothedEisensteinCoeff s _ _ _ ζ _ _ _ h0 hz1, UpperTheory.ringHom_apply_smoothedEisensteinCoeff s _ _ _ ζ _ _ _ h0 (hz _)]
