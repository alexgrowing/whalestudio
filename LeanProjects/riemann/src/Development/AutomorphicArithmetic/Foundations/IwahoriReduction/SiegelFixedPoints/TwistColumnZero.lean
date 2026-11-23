import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamOfLSmulIff
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftSLMapMulInvMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueNormalizedCyclotomicTraceStatement
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.MemClosureOfIsIntegral
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.SpecialLinearMulApplyZeroZero
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.OrderOfTranslationMod
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.SmoothedEisensteinCongrOfModEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.RingHomApplySmoothedEisensteinCoeff
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.SmoothedEisensteinRootPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.SmoothedEisensteinCoeffShiftSecondIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.CardFiberReductionEqTotient
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.SumLevelSubgroupModEqSmulSumReps
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.CongruenceActionInvariant
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.TwistedEisensteinPieceTrivialCharacterEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.InZlClosedAddMulAndCyclotomicGaloisStable
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.IsPrimitiveRootEOmAndPowCompatible
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.RepMApplyZtEqPowRedTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.CmulSmFInvariantOfCongruentMulTPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.Gamma0DiamondActionEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.PieceTLevelRaiseEqVp
import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.PieceTDetFiberEqPieceTRootPow
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

noncomputable section
namespace UpperTheory.Kd.L

private def dgU {R : Type} [CommRing R] (u : Rˣ) : GL (Fin 2) R :=
  ⟨!![1, 0; 0, (u : R)], !![1, 0; 0, ((u⁻¹ : Rˣ) : R)], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

private def tw {R : Type} [CommRing R] (h : SL(2, R)) (u : Rˣ) : GL (Fin 2) R :=
  Matrix.SpecialLinearGroup.toGL h * dgU u

private theorem twist_column_zero {R : Type} [CommRing R] (h : SL(2, R)) (u : Rˣ) (i : Fin 2) :
    ((tw h u : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i 0 = h i 0 := by
  fin_cases i <;> simp [tw, dgU, Matrix.mul_apply, Fin.sum_univ_two]

private theorem twist_column_one {R : Type} [CommRing R] (h : SL(2, R)) (u : Rˣ) (i : Fin 2) :
    ((tw h u : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i 1 = (u : R) * h i 1 := by
  fin_cases i <;> simp [tw, dgU, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private abbrev kz {K : Type} [Field K] [CharZero K] (ζ : K) (l L N : ℕ) (x : ZMod N) (c d w : ℕ) (g : SL(2, ℤ)) : ℕ → K :=
  cmul (smF (c : ℤ) (w + 1) (N * l ^ L) ζ (en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L)) ((N : ℤ) ^ 2 * en g 0 1))
    (smF (d : ℤ) 1 (N * l ^ L) ζ (en g 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g 1 0) ((N : ℤ) * en g 1 1))

private abbrev kg {K : Type} [Field K] [CharZero K] (ζ : K) (l L N : ℕ) (c d : ℤ) (w : ℕ) (v v' : ℤ × ℤ)
    (γ : GL (Fin 2) (ZMod (l ^ L))) : ℕ → K :=
  cmul (smF c (w + 1) (N * l ^ L) ζ (rowT N l L γ 0 v).1 (rowT N l L γ 0 v).2)
    (smF d 1 (N * l ^ L) ζ (rowT N l L γ 1 v').1 (rowT N l L γ 1 v').2)

private theorem swap4 {V α β γ δ : Type} [AddCommMonoid V] (A : Finset α) (B : Finset β) (C : Finset γ) (D : Finset δ)
    (f : α → β → γ → δ → V) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ e ∈ D, f a b c e = ∑ e ∈ D, ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, f a b c e := by
  have h1 : ∀ a, ∑ b ∈ B, ∑ c ∈ C, ∑ e ∈ D, f a b c e = ∑ c ∈ C, ∑ e ∈ D, ∑ b ∈ B, f a b c e := fun a => by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ c, ∑ a ∈ A, ∑ e ∈ D, ∑ b ∈ B, f a b c e = ∑ e ∈ D, ∑ a ∈ A, ∑ b ∈ B, f a b c e := fun c => Finset.sum_comm
  simp_rw [h2]
  exact Finset.sum_comm

private theorem sum_key {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime]
    (N : ℕ) [NeZero N] (c d w : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (hP : Par l N c d gm) (x : ZMod N) (a₀ : ℤ) (ha₀ : (a₀ : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N)) (m n : ℕ) (hm : 1 ≤ m)
    (R : Finset SL(2, ZMod (topMu l n m N))) (hR : IsReps N l (topMu l n m N) R) (z : (ZMod (l ^ (m + n)))ˣ)
    (τ : (ZMod (l ^ (m + n)))ˣ → (Ω ≃ₐ[ℚ] Ω))
    (hτ : ∀ a, τ a (zt ε l (m + n)) = zt ε l (m + n) ^ (a : ZMod (l ^ (m + n))).val)
    (μ : ℕ) (hμ : ∀ (Φ : SL(2, ZMod (l ^ (m + n))) → Ω) (Ψ : SL(2, ℤ) → Ω), (∀ g ∈ CongruenceSubgroup.Gamma0 N, ((en g 0 0 : ℤ) : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N) → ∀ h : SL(2, ZMod (l ^ (m + n))), h 0 0 = (en g 0 0 : ℤ) → h 0 1 = ((N : ℤ) * en g 0 1 : ℤ) → (N : ZMod (l ^ (m + n))) * h 1 0 = (en g 1 0 : ℤ) → h 1 1 = (en g 1 1 : ℤ) → Ψ g = Φ h) → ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ Gs N l (topMu l n m N), Ψ (gm r₀ * liftSL _ γ) = μ • ∑ h ∈ Finset.univ.filter (fun h : SL(2, ZMod (l ^ (m + n))) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val), Φ h)
    (i : ℕ) :
    ((topMu l n m N : ℕ) : Ω) * ∑ a ∈ Finset.univ.filter (fun a : (ZMod (l ^ (m + n)))ˣ => (a : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]),
      τ a (∑ y ∈ Finset.univ.filter (fun y => redTop l n m N y = z), ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ R,
        repM (topM l n m (N * N)) y (kz (eOm ε (1 / ((N * l ^ (m + n) : ℕ) : ℚ))) l (m + n) N x c d w (gm r₀ * liftSL _ γ) (l ^ (m + n) * i))) =
    (μ : Ω) * (Nat.totient (N * N) : Ω) * ∑ γ ∈ ((unitSet l (m + n)).filter fun γ : GL (Fin 2) (ZMod (l ^ (m + n))) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))).det.val : ℕ) : ZMod (l ^ m)) = (((z : ZMod (l ^ (m + n))).val : ℕ) : ZMod (l ^ m))),
      kg (eOm ε (1 / ((N * l ^ (m + n) : ℕ) : ℚ))) l (m + n) N (c : ℤ) (d : ℤ) w ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) γ (l ^ (m + n) * i) := by
  have hcop : ¬ l ∣ N := hP.cop
  have hroots := UpperTheory.isPrimitiveRoot_eOm_and_pow_compatible ε l N
  obtain ⟨hpr, hzN, -⟩ := hroots
  set ζ : Ω := eOm ε (1 / ((N * l ^ (m + n) : ℕ) : ℚ)) with hζdef
  have hζN : ζ ^ N = zt ε l (m + n) := hzN (m + n)
  have hζ1 : ζ ^ (N * l ^ (m + n)) = 1 := (hpr (m + n)).pow_eq_one
  have hzt1 : zt ε l (m + n) ^ (l ^ (m + n)) = 1 := by rw [← hζN, ← pow_mul, hζ1]
  set A := Finset.univ.filter (fun a : (ZMod (l ^ (m + n)))ˣ => (a : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]) with hA
  set Fy := Finset.univ.filter (fun y => redTop l n m N y = z) with hFy
  set r : ℕ := l ^ (m + n) * i with hr
  let Ψ : SL(2, ℤ) → Ω := fun g => ∑ a ∈ A, ∑ y ∈ Fy, τ a (repM (topM l n m (N * N)) y (kz ζ l (m + n) N x c d w g r))
  let Φ : SL(2, ZMod (l ^ (m + n))) → Ω := fun h => (Nat.totient (N * N)) • ∑ a ∈ A,
    kg ζ l (m + n) N (c : ℤ) (d : ℤ) w ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) (tw h (a * z)) r
  have hΨ : ∀ g ∈ CongruenceSubgroup.Gamma0 N, ((en g 0 0 : ℤ) : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N) → ∀ h : SL(2, ZMod (l ^ (m + n))), h 0 0 = (en g 0 0 : ℤ) → h 0 1 = ((N : ℤ) * en g 0 1 : ℤ) → (N : ZMod (l ^ (m + n))) * h 1 0 = (en g 1 0 : ℤ) → h 1 1 = (en g 1 1 : ℤ) → Ψ g = Φ h := by
    intro g hg hga h h00 h01 h10 h11
    show ∑ a ∈ A, ∑ y ∈ Fy, _ = (Nat.totient (N * N)) • ∑ a ∈ A, _
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hy : ∀ y ∈ Fy, τ a (repM (topM l n m (N * N)) y (kz ζ l (m + n) N x c d w g r)) =
        kg ζ l (m + n) N (c : ℤ) (d : ℤ) w ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) (tw h (a * z)) r := by
      intro y hy
      have hyz : redTop l n m N y = z := (Finset.mem_filter.1 hy).2
      let s : Ω →+* Ω := (τ a).toRingEquiv.toRingHom.comp (repM (Ω := Ω) (topM l n m (N * N)) y).toRingEquiv.toRingHom
      have hs : s (ζ ^ N) = (ζ ^ N) ^ (((a * z : (ZMod (l ^ (m + n)))ˣ) : ZMod (l ^ (m + n))).val) := by
        rw [hζN]
        show τ a (repM (topM l n m (N * N)) y (zt ε l (m + n))) = _
        rw [UpperTheory.repM_apply_zt_eq_pow_redTop ε l n m N y, hyz, map_pow, hτ a, ← pow_mul, Units.val_mul, ZMod.val_mul,
          ← pow_eq_pow_mod _ hzt1]
      exact UpperTheory.gamma0_diamond_action_eq ζ l (m + n) N x c d w a₀ s
        (((a * z : (ZMod (l ^ (m + n)))ˣ) : ZMod (l ^ (m + n)))) hcop hζ1 hs g hg (hga.trans ha₀.symm) (tw h (a * z))
        (by rw [twist_column_zero, h00]) (by rw [twist_column_one, h01]) (by rw [twist_column_zero, h10]) (by rw [twist_column_one, h11]) r
    rw [Finset.sum_congr rfl hy, Finset.sum_const, hFy, UpperTheory.card_fiber_reduction_eq_totient l n m N hcop z]
  have hcount := hμ Φ Ψ hΨ
  have hT : ∀ γ ∈ R, ∀ b : ℕ, (fun γ => ∑ r₀ : (ZMod l)ˣ, Ψ (gm r₀ * liftSL _ γ)) (γ * Tm (topMu l n m N) b) =
      (fun γ => ∑ r₀ : (ZMod l)ˣ, Ψ (gm r₀ * liftSL _ γ)) γ := by
    intro γ _ b
    refine Finset.sum_congr rfl fun r₀ _ => ?_
    have hk := UpperTheory.cmul_smF_invariant_of_congruent_mul_T_pow ζ l (m + n) N x c d w (topMu l n m N) (NeZero.pos N) (Fact.out : l.Prime).pos hζ1
      ⟨N, by unfold topMu; ring⟩ b (gm r₀ * liftSL _ γ) (gm r₀ * liftSL _ (γ * Tm (topMu l n m N) b))
      (by simp only [map_mul, GlobalTheory.K4.map_liftSL, Tm, mul_assoc]) i
    show ∑ a ∈ A, ∑ y ∈ Fy, _ = ∑ a ∈ A, ∑ y ∈ Fy, _
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun y _ => ?_
    exact congrArg (fun t => τ a (repM (topM l n m (N * N)) y t)) hk
  have hG := UpperTheory.sum_levelSubgroupMod_eq_smul_sum_reps N l (topMu l n m N) R hR Ω (fun γ => ∑ r₀ : (ZMod l)ˣ, Ψ (gm r₀ * liftSL _ γ)) hT
  have htw := UpperTheory.congruence_action_invariant l (m + n) m hm (by omega) z tw twist_column_zero twist_column_one Ω
    (kg ζ l (m + n) N (c : ℤ) (d : ℤ) w ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) · r)
  rw [← htw]
  have hl : ∑ a ∈ A, τ a (∑ y ∈ Fy, ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ R,
        repM (topM l n m (N * N)) y (kz ζ l (m + n) N x c d w (gm r₀ * liftSL _ γ) r)) =
      ∑ γ ∈ R, ∑ r₀ : (ZMod l)ˣ, Ψ (gm r₀ * liftSL _ γ) := by
    simp only [map_sum]
    exact swap4 A Fy Finset.univ R _
  have hΦ : ∑ h ∈ Finset.univ.filter (fun h : SL(2, ZMod (l ^ (m + n))) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val), Φ h =
      (Nat.totient (N * N)) • ∑ h ∈ Finset.univ.filter (fun h : SL(2, ZMod (l ^ (m + n))) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val), ∑ a ∈ A,
        kg ζ l (m + n) N (c : ℤ) (d : ℤ) w ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) (tw h (a * z)) r := by
    rw [Finset.smul_sum]
  rw [hl, ← nsmul_eq_mul, ← hG, Finset.sum_comm, hcount, hΦ]
  simp only [nsmul_eq_mul]
  ring

end UpperTheory.Kd.L

theorem UpperTheory.Kd.L.arith :
    ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (w : ℕ), 1 ≤ w → ∃ κ : ℚ, κ ≠ 0 ∧ ∃ L₀ : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (x : ZMod N) (m n : ℕ), 1 ≤ m → ∀ R, IsReps N l (topMu l n m N) R → ∀ (z : (ZMod (l ^ (m + n)))ˣ), (∀ r : ℚ, InZl ε l (m + n) (Fsum ε l n m N x c d w gm R z r)) ∧ (L₀ ≤ m + n → ∀ (i : ℕ) (F' : Ω), IsNT ε l (m + n) m (Fsum ε l n m N x c d w gm R z (i : ℚ)) F' → ∀ (β : ℕ) (t a : ℤ), (a : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N) → β ≡ (z : ZMod (l ^ (m + n))).val [MOD l ^ m] → (β : ZMod N) = 1 → (l : ℤ) ^ m * t ≡ 1 [ZMOD N] → ∃ E : Ω, InZl ε l m E ∧ F' = (κ : Ω) * (l : Ω) ^ m * toQ (l ^ m) (pieceT N l m m (w + 2) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ) ((x.val : ℤ) * a * t, 0) (a * t, 0) (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β) ((unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i + (l : Ω) ^ n * E) := by
  intro l _ N _ w hw
  obtain ⟨μ, hμ0, hμ⟩ := UpperTheory.Kd.L.count l N
  have hN0 : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hNN : 0 < N * N := Nat.mul_pos (NeZero.pos N) (NeZero.pos N)
  refine ⟨-((N : ℚ) * (Nat.totient (N * N) : ℚ) * (μ : ℚ)), neg_ne_zero.2 (mul_ne_zero (mul_ne_zero hN0
    (Nat.cast_ne_zero.2 (Nat.totient_pos.2 hNN).ne')) (Nat.cast_ne_zero.2 hμ0.ne')), (w + 1) ^ 2 * l, ?_⟩
  intro Ω _ _ _ _ ε c d gm hP x m n hm R hR z
  have hl : l.Prime := Fact.out
  have hNl : N * l ∣ topMu l n m N := by
    have h1 : l ∣ l ^ (m + n) := dvd_pow_self l (by omega)
    obtain ⟨e, he⟩ := h1
    exact ⟨e * N, by unfold topMu; rw [he]; ring⟩
  have hreps := (UpperTheory.Kd.L.reps l N c d gm hP (topMu l n m N) hNl).2
  have hcond : ∀ (r₀ : (ZMod l)ˣ) (γ : SL(2, ZMod (topMu l n m N))), γ ∈ R →
      ¬ (l : ℤ) ∣ en (gm r₀ * liftSL _ γ) 0 0 ∧ ¬ (l : ℤ) ∣ en (gm r₀ * liftSL _ γ) 1 0 :=
    fun r₀ γ hγ => (hreps γ (hR.1 hγ) r₀).2.2.2
  obtain ⟨inat, iadd, imul, igal⟩ := UpperTheory.inZl_closed_add_mul_and_cyclotomic_galois_stable ε l (m + n)
  have hi0 : InZl ε l (m + n) (0 : Ω) := by simpa using inat 0
  have isum : ∀ {α : Type} (s : Finset α) (f : α → Ω), (∀ a ∈ s, InZl ε l (m + n) (f a)) →
      InZl ε l (m + n) (∑ a ∈ s, f a) := fun s f h => Finset.sum_induction f _ iadd hi0 h
  have irep : ∀ (y : (ZMod (topM l n m (N * N)))ˣ) (F : Ω), InZl ε l (m + n) F →
      InZl ε l (m + n) (repM (topM l n m (N * N)) y F) := fun y F h => igal _ _ (UpperTheory.repM_apply_zt_eq_pow_redTop ε l n m N y) F h
  have iN3 : InZl ε l (m + n) ((N : Ω) ^ 3) := by have h := inat (N ^ 3); rwa [Nat.cast_pow] at h
  have hEE : ∀ (r₀ : (ZMod l)ˣ) (γ : SL(2, ZMod (topMu l n m N))), γ ∈ R → ∀ r : ℚ, r.den = 1 →
      InZl ε l (m + n) (EE ε l (m + n) N x c d (gm r₀ * liftSL _ γ) r) := by
    intro r₀ γ hγ r hden
    rcases lt_or_ge r 0 with hr | hr
    · have h0 : EE ε l (m + n) N x c d (gm r₀ * liftSL _ γ) r = 0 := by
        simp [EE, coefQ, not_le.2 hr]
      rw [h0]; exact hi0
    · have h1 : (r.num : ℚ) = r := Rat.coe_int_num_of_den_eq_one hden
      have h2 : 0 ≤ r.num := Rat.num_nonneg.2 hr
      have h3 : r = ((r.num.toNat : ℕ) : ℚ) := by
        calc r = (r.num : ℚ) := h1.symm
          _ = ((r.num.toNat : ℤ) : ℚ) := by rw [Int.toNat_of_nonneg h2]
          _ = _ := by push_cast; rfl
      rw [h3]
      exact (UpperTheory.Kd.L.inzl ε l N c d gm hP x (m + n) n w hw (by omega) _ (hcond r₀ γ hγ).1 (hcond r₀ γ hγ).2 _).1
  constructor
  · intro r
    unfold Fsum
    split_ifs with hden
    · exact imul _ _ iN3 (isum _ _ fun y _ => isum _ _ fun r₀ _ => isum _ _ fun γ hγ =>
        imul _ _ (inat _) (irep y _ (hEE r₀ γ hγ r hden)))
    · exact hi0
  intro hL i F' hNT β t a₀ ha₀ hβ hβN ht
  have hlarge : (w + 1) ^ 2 * l ≤ l ^ (m + n) := hL.trans (Nat.lt_pow_self hl.one_lt).le
  have hex : ∀ (r₀ : (ZMod l)ˣ) (γ : SL(2, ZMod (topMu l n m N))), γ ∈ R → ∃ E : Ω, InZl ε l (m + n) E ∧
      (ex l n w (gm r₀ * liftSL _ γ) : Ω) * EE ε l (m + n) N x c d (gm r₀ * liftSL _ γ) (i : ℚ) =
        (l : Ω) ^ ((m + n) * w) * kz (eOm ε (1 / ((N * l ^ (m + n) : ℕ) : ℚ))) l (m + n) N x c d w (gm r₀ * liftSL _ γ) (l ^ (m + n) * i) +
          (l : Ω) ^ n * E :=
    fun r₀ γ hγ => (UpperTheory.Kd.L.inzl ε l N c d gm hP x (m + n) n w hw (by omega) _ (hcond r₀ γ hγ).1 (hcond r₀ γ hγ).2 i).2 hlarge
  choose! E hE using hex
  set ζ : Ω := eOm ε (1 / ((N * l ^ (m + n) : ℕ) : ℚ)) with hζdef
  set S1 : Ω := ∑ y ∈ Finset.univ.filter (fun y => redTop l n m N y = z), ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ R,
    repM (topM l n m (N * N)) y (kz ζ l (m + n) N x c d w (gm r₀ * liftSL _ γ) (l ^ (m + n) * i)) with hS1
  set S2 : Ω := ∑ y ∈ Finset.univ.filter (fun y => redTop l n m N y = z), ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ R,
    repM (topM l n m (N * N)) y (E r₀ γ) with hS2
  have hF : Fsum ε l n m N x c d w gm R z (i : ℚ) = (N : Ω) ^ 3 * ((l : Ω) ^ ((m + n) * w) * S1 + (l : Ω) ^ n * S2) := by
    unfold Fsum
    rw [if_pos (by simp)]
    congr 1
    simp only [hS1, hS2, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun r₀ _ => Finset.sum_congr rfl fun γ hγ => ?_
    have h1 := (hE r₀ γ hγ).2
    calc (ex l n w (gm r₀ * liftSL _ γ) : Ω) * repM (topM l n m (N * N)) y (EE ε l (m + n) N x c d (gm r₀ * liftSL _ γ) (i : ℚ))
        = repM (topM l n m (N * N)) y ((ex l n w (gm r₀ * liftSL _ γ) : Ω) * EE ε l (m + n) N x c d (gm r₀ * liftSL _ γ) (i : ℚ)) := by
          rw [map_mul, map_natCast]
      _ = _ := by rw [h1, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast]
  have hS2Z : InZl ε l (m + n) S2 := isum _ _ fun y _ => isum _ _ fun r₀ _ => isum _ _ fun γ hγ => irep y _ (hE r₀ γ hγ).1
  have hE0 : InZl ε l (m + n) ((N : Ω) ^ 3 * S2) := imul _ _ iN3 hS2Z
  obtain ⟨E', hNT', hE'Z, -⟩ := GlobalTheory.T.exists_unique_normalizedCyclotomicTrace ε l (m + n) m hm (by omega) _ hE0
  obtain ⟨τ, hτ, hsum⟩ := hNT
  obtain ⟨τ', hτ', hsum'⟩ := hNT'
  rw [Nat.add_sub_cancel_left] at hsum hsum'
  have hkey := sum_key ε l N c d w gm hP x a₀ ha₀ m n hm R hR z τ hτ μ (fun Φ Ψ h => hμ c d gm hP n m hm Ω Φ Ψ h) i
  have hterm : ∀ a, τ a ((N : Ω) ^ 3 * ((l : Ω) ^ ((m + n) * w) * S1 + (l : Ω) ^ n * S2)) =
      (N : Ω) ^ 3 * (l : Ω) ^ ((m + n) * w) * τ a S1 + (l : Ω) ^ n * τ' a ((N : Ω) ^ 3 * S2) := by
    intro a
    rw [← IsNTr.apply_eq_of_mem_adjoin hE0.mem_adjoin ((hτ a).trans (hτ' a).symm)]
    simp only [map_mul, map_add, map_pow, map_natCast]
    ring
  have hB : (l : Ω) ^ (m + n) = (l : Ω) ^ n * (l : Ω) ^ m := by rw [add_comm, pow_add]
  have hln : (l : Ω) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.ne_zero)
  have hprim := (UpperTheory.isPrimitiveRoot_eOm_and_pow_compatible ε l N).1 (m + n)
  have hzm := (UpperTheory.isPrimitiveRoot_eOm_and_pow_compatible ε l N).2.2 m n
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  set T : Ω := ∑ a ∈ Finset.univ.filter (fun a : (ZMod (l ^ (m + n)))ˣ => (a : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]), τ a S1 with hT
  have key4 : (l : Ω) ^ n * F' = (N : Ω) ^ 3 * (l : Ω) ^ ((m + n) * w) * T + (l : Ω) ^ n * ((l : Ω) ^ n * E') := by
    have h1 : ∑ a ∈ Finset.univ.filter (fun a : (ZMod (l ^ (m + n)))ˣ => (a : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]),
        τ a ((N : Ω) ^ 3 * ((l : Ω) ^ ((m + n) * w) * S1 + (l : Ω) ^ n * S2)) =
        (N : Ω) ^ 3 * (l : Ω) ^ ((m + n) * w) * T + (l : Ω) ^ n * ∑ a ∈ Finset.univ.filter (fun a : (ZMod (l ^ (m + n)))ˣ => (a : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]), τ' a ((N : Ω) ^ 3 * S2) := by
      rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hsum, hF, h1, ← hsum']
  set z₀ : ZMod (l ^ m) := (((z : ZMod (l ^ (m + n))).val : ℕ) : ZMod (l ^ m)) with hz₀
  have hcp : Nat.Coprime (l ^ (m + n)) N := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hl).2 hP.cop)
  have htop : (l : ℤ) ^ n * (topT l (m + n) N : ℤ) ≡ t [ZMOD N] := by
    have h1 : (l : ZMod N) ^ (m + n) * (topT l (m + n) N : ZMod N) = 1 := by
      unfold topT
      rw [ZMod.natCast_zmod_val]
      have h := ZMod.coe_mul_inv_eq_one (l ^ (m + n)) hcp
      simpa using h
    have h2 : (l : ZMod N) ^ m * (t : ZMod N) = 1 := by
      have h := (ZMod.intCast_eq_intCast_iff _ _ N).2 ht
      push_cast at h
      exact h
    apply (ZMod.intCast_eq_intCast_iff _ _ N).1
    push_cast
    rw [pow_add] at h1
    linear_combination (-((l : ZMod N) ^ n * (topT l (m + n) N : ZMod N))) * h2 + (t : ZMod N) * h1
  have e1 : (l : ℤ) ^ n * ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ)) ≡ (x.val : ℤ) * a₀ * t [ZMOD N] := by
    have h := htop.mul_left ((x.val : ℤ) * a₀)
    rwa [show (x.val : ℤ) * a₀ * ((l : ℤ) ^ n * (topT l (m + n) N : ℤ)) = (l : ℤ) ^ n * ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ)) by ring] at h
  have e3 : (l : ℤ) ^ n * (a₀ * (topT l (m + n) N : ℤ)) ≡ a₀ * t [ZMOD N] := by
    have h := htop.mul_left a₀
    rwa [show a₀ * ((l : ℤ) ^ n * (topT l (m + n) N : ℤ)) = (l : ℤ) ^ n * (a₀ * (topT l (m + n) N : ℤ)) by ring] at h
  have e0 : (l : ℤ) ^ n * (0 : ℤ) ≡ 0 [ZMOD N] := by rw [mul_zero]
  have hnd : ∀ e : ℕ, Nat.Coprime e (6 * l * N) → ¬ (l : ℤ) ∣ (e : ℤ) := by
    intro e he h
    have h' : l ∣ e := Int.natCast_dvd_natCast.1 h
    have h2 : l ∣ Nat.gcd e (6 * l * N) := Nat.dvd_gcd h' ⟨6 * N, by ring⟩
    rw [he.gcd_eq_one] at h2
    exact hl.one_lt.ne' (Nat.dvd_one.1 h2)
  have down := UpperTheory.pieceT_level_raise_eq_vp l N m (w + 2) (c : ℤ) (d : ℤ) z₀ (NeZero.pos N) hP.cop hm (by omega) (hnd c hP.cc) (hnd d hP.dc) n ζ
    ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) ((x.val : ℤ) * a₀ * t, 0) (a₀ * t, 0)
    hprim e1 e0 e3 e0 (l ^ (m + n) * i)
  have hzm' : ζ ^ (l ^ n) = eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) := hzm
  have hζm1 : (ζ ^ (l ^ n)) ^ (N * l ^ m) = 1 := by
    rw [← pow_mul, show l ^ n * (N * l ^ m) = N * l ^ (m + n) by rw [pow_add]; ring]
    exact hprim.pow_eq_one
  have hunit : IsUnit z₀ := by
    have hd : l ^ m ∣ l ^ (m + n) := pow_dvd_pow l (by omega)
    have h := z.isUnit.map (ZMod.castHom hd (ZMod (l ^ m)))
    rwa [ZMod.castHom_apply, ← ZMod.natCast_val] at h
  have hβ' : (β : ZMod (l ^ m)) = z₀ := (ZMod.natCast_eq_natCast_iff _ _ _).2 hβ
  have beta := UpperTheory.pieceT_det_fiber_eq_pieceT_root_pow l N m (w + 2) (c : ℤ) (d : ℤ) ((x.val : ℤ) * a₀ * t) (a₀ * t) (ζ ^ (l ^ n)) β z₀ (NeZero.pos N) hm hζm1 hunit hβ' (l ^ m * i)
  have hvp : ∀ f : ℕ → Ω, vp (l ^ n) f (l ^ (m + n) * i) = f (l ^ m * i) := by
    intro f
    have hdiv : l ^ (m + n) * i = l ^ n * (l ^ m * i) := by rw [pow_add]; ring
    rw [hdiv]
    unfold vp
    rw [if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ (pow_pos hl.pos n)]
  rw [hvp] at down
  set Ks : Ω := ∑ γ ∈ ((unitSet l (m + n)).filter fun γ : GL (Fin 2) (ZMod (l ^ (m + n))) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))).det.val : ℕ) : ZMod (l ^ m)) = z₀),
    kg ζ l (m + n) N (c : ℤ) (d : ℤ) w ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) γ (l ^ (m + n) * i) with hKs
  have key2 : pieceT N l (m + n) m (w + 2) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ) ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) ζ ((unitSet l (m + n)).filter fun γ : GL (Fin 2) (ZMod (l ^ (m + n))) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))).det.val : ℕ) : ZMod (l ^ m)) = z₀) (l ^ (m + n) * i) =
      -((l : Ω) ^ (((m + n : ℕ) : ℤ) * ((w : ℤ) - 2))) * Ks :=
    UpperTheory.twistedEisensteinPiece_trivialCharacter_eq l N (m + n) m w (c : ℤ) (d : ℤ) ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) ζ z₀ hm (by omega) (l ^ (m + n) * i)
  have hk' : ((topMu l n m N : ℕ) : Ω) * T = (μ : Ω) * (Nat.totient (N * N) : Ω) * Ks := hkey
  have key1 : (l : Ω) ^ (m + n) * (N : Ω) ^ 2 * T = (μ : Ω) * (Nat.totient (N * N) : Ω) * Ks := by
    rw [← hk']; unfold topMu; push_cast; ring
  have key3 : (l : Ω) ^ (((m + n : ℕ) : ℤ) * ((w : ℤ) - 2)) * ((l : Ω) ^ (m + n)) ^ 2 = (l : Ω) ^ ((m + n) * w) := by
    rw [← pow_mul, ← zpow_natCast (l : Ω) ((m + n) * 2), ← zpow_add₀ hl0, ← zpow_natCast (l : Ω) ((m + n) * w)]
    congr 1
    push_cast
    ring
  refine ⟨E', hE'Z, ?_⟩
  have hQ : toQ (l ^ m) (pieceT N l m m (w + 2) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ) ((x.val : ℤ) * a₀ * t, 0) (a₀ * t, 0) (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β) ((unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i =
      pieceT N l (m + n) m (w + 2) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ) ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) ζ ((unitSet l (m + n)).filter fun γ : GL (Fin 2) (ZMod (l ^ (m + n))) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))).det.val : ℕ) : ZMod (l ^ m)) = z₀) (l ^ (m + n) * i) := by
    rw [down, beta, hzm']
    rfl
  rw [hQ]
  apply mul_left_cancel₀ hln
  push_cast
  linear_combination key4 - (N : Ω) * (Nat.totient (N * N) : Ω) * (μ : Ω) * (pieceT N l (m + n) m (w + 2) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ) ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) ζ ((unitSet l (m + n)).filter fun γ : GL (Fin 2) (ZMod (l ^ (m + n))) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))).det.val : ℕ) : ZMod (l ^ m)) = z₀) (l ^ (m + n) * i)) * hB +
    (N : Ω) * (Nat.totient (N * N) : Ω) * (μ : Ω) * (l : Ω) ^ (m + n) * key2 - (N : Ω) ^ 3 * T * key3 +
    (N : Ω) * (l : Ω) ^ (((m + n : ℕ) : ℤ) * ((w : ℤ) - 2)) * (l : Ω) ^ (m + n) * key1
