import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetGramSumElimSmulSub
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexMulMeasure

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.CoordHeight

section Val

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)
  (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
include hϖ

theorem vE_one : vE L ϖ (algebraMap F E 1) = 0 := by
  have h := (GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).1 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at h
  omega

theorem vE_unit (x : F) (hx : x ≠ 0) (h1 : algebraMap F E x ∈ L.O)
    (h2 : ∃ y ∈ L.O, algebraMap F E x * y = 1) : vE L ϖ (algebraMap F E x) = 0 := by
  obtain ⟨hadd, -, hint, -⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  obtain ⟨-, -, -, -, hO, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  obtain ⟨y, hy, hxy⟩ := h2
  have e : y = algebraMap F E x⁻¹ := by
    calc y = algebraMap F E (x⁻¹ * x) * y := by rw [inv_mul_cancel₀ hx, map_one, one_mul]
      _ = algebraMap F E x⁻¹ := by rw [map_mul, mul_assoc, hxy, mul_one]
  have a1 := (hint x hx).2 ((hO x).1 h1)
  have a2 := (hint x⁻¹ (inv_ne_zero hx)).2 ((hO _).1 (e ▸ hy))
  have a3 := hadd x x⁻¹ hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, vE_one L ϖ hϖ] at a3
  omega

theorem vE_pow (x : F) (hx : x ≠ 0) (n : ℕ) :
    vE L ϖ (algebraMap F E (x ^ n)) = n * vE L ϖ (algebraMap F E x) := by
  induction n with
  | zero => simpa using vE_one L ϖ hϖ
  | succ n ih =>
    rw [pow_succ, (GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).1 _ _ (pow_ne_zero n hx) hx, ih]
    push_cast
    ring

theorem vE_neg_one : vE L ϖ (algebraMap F E (-1)) = 0 := by
  have h := vE_pow L ϖ hϖ (-1) (by simp) 2
  rw [neg_one_sq, vE_one L ϖ hϖ] at h
  omega

omit [IsNonarchimedeanLocalField F] [CharZero F] hϖ in
theorem norm_mem (x : E) (hx : IsUnit x) : ∃ c : F, c ≠ 0 ∧ x * L.cj x = algebraMap F E c := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)
  obtain ⟨c, hc⟩ := (L.cj_fix (x * L.cj x)).1 (by rw [map_mul, L.cj_cj, mul_comm])
  refine ⟨c, ?_, hc.symm⟩
  rintro rfl
  rw [map_zero] at hc
  exact (hx.mul (hx.map L.cj)).ne_zero hc.symm

end Val

section Transport

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
include c

theorem Dm_eq (l : Fin (r + 2)) : P.Dm l = S.D l := by
  have hZ : H.Zhat P.A.f P.B.f = S.Zh := by
    ext a b
    simp only [HermSp.Zhat, Frames.Zh, Matrix.of_apply, c.f_eq, c.f'_eq, c.h_eq]
  unfold LocNG.FPair.Dm HermSp.Dl Frames.D lead
  rw [dif_pos (Nat.lt_succ_iff.mp l.2), hZ]

theorem Gv_eq : P.Gv = S.G := by
  have h1 := Dm_eq c (Fin.last (r + 1))
  have h2 := Dm_eq c (Fin.last r).castSucc
  unfold LocNG.FPair.Gv HermSp.Gdet HermSp.normE Frames.G
  rw [← h1, ← h2, c.T_eq, c.T'_eq]
  rfl

theorem theta_eq : LocNG.theta M = S.th := by
  unfold LocNG.theta Frames.th
  cases h : M.split with
  | none => simp [c.gg_none h]
  | some g =>
    obtain ⟨h1, h2⟩ := c.gg_some g h
    simp [h1, h2]

end Transport

theorem height_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), P.Hp = S.Hp ∧ LocNG.qF F = S.q ∧ (P.PrimeTo → S.gg = false ∧ vE M.L S.ϖ S.G = 0 ∧ ∀ l, S.D l ≠ 0 → vE M.L S.ϖ (S.D l * M.L.cj (S.D l)) = 0) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c
  have := hM.loc
  have := hM.char0
  obtain ⟨hq, hmod⟩ := GlobalTheory.BaseModule.modK_algebraMap M hM S.ϖ S.ϖ_irr
  obtain ⟨-, -, ⟨g, hg0, hg⟩, -, hD, hth, -⟩ := GlobalTheory.FrameBasic.main M.L r k S
  obtain ⟨hadd, hvp, -, -⟩ := GlobalTheory.UnramVal.vE_valuation M.L S.ϖ S.ϖ_irr
  obtain ⟨-, hcj, -, -, -, -, hq2, -⟩ := GlobalTheory.UnramOrder.order_facts M.L S.ϖ S.ϖ_irr
  have hnt : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [M.L.rank]; norm_num)
  have hgram := GlobalTheory.det_gram_frame_generators M hM H r k P
  rw [theta_eq c, Gv_eq c, hg] at hgram
  have hvth : vE M.L S.ϖ (algebraMap F E S.th) = S.vth := by
    unfold Frames.th Frames.vth
    split_ifs
    · exact hvp
    · exact vE_one M.L S.ϖ S.ϖ_irr
  have hends : ∀ l : Fin (r + 2), (l : ℕ) ∈ P.ends ↔ l ≠ 0 ∧ S.D l ≠ 0 := by
    intro l
    unfold LocNG.FPair.ends
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [Dm_eq c]
    constructor
    · rintro ⟨-, h1, h2⟩
      refine ⟨?_, h2.ne_zero⟩
      rintro rfl
      simp at h1
    · rintro ⟨h1, h2⟩
      refine ⟨l.2, ?_, hD l h2⟩
      exact Nat.one_le_iff_ne_zero.mpr fun h => h1 (Fin.ext h)
  refine ⟨?_, hq, ?_⟩
  · have hq0 : (0 : ℝ) < (resQ S.ϖ : ℝ) := by
      have : 0 < resQ S.ϖ := by omega
      exact_mod_cast this
    set d : F := (-1) ^ (r + 1) * g * (S.th ^ (2 * (r + 1)))⁻¹ with hd
    have hp0 : S.th ^ (2 * (r + 1)) ≠ 0 := pow_ne_zero _ hth
    have hs0 : ((-1 : F) ^ (r + 1)) ≠ 0 := pow_ne_zero _ (by simp)
    have hd0 : d ≠ 0 := mul_ne_zero (mul_ne_zero hs0 hg0) (inv_ne_zero hp0)
    have hdet : (H.gram P.MMgen).det = algebraMap F E d := by
      calc (H.gram P.MMgen).det
          = (H.gram P.MMgen).det * algebraMap F E (S.th ^ (2 * (r + 1)) * (S.th ^ (2 * (r + 1)))⁻¹) := by
            rw [mul_inv_cancel₀ hp0, map_one, mul_one]
        _ = algebraMap F E d := by
            rw [map_mul, ← mul_assoc, map_pow, hgram, hd]
            simp only [map_mul, map_pow, map_neg, map_one]
    have hva : vE M.L S.ϖ (algebraMap F E d) = S.a := by
      have e : d * S.th ^ (2 * (r + 1)) = (-1) ^ (r + 1) * g := by
        rw [hd, mul_assoc, inv_mul_cancel₀ hp0, mul_one]
      have h1 := hadd _ _ hd0 hp0
      rw [e, hadd _ _ hs0 hg0, vE_pow M.L S.ϖ S.ϖ_irr _ hth, vE_pow M.L S.ϖ S.ϖ_irr _ (by simp),
        vE_neg_one M.L S.ϖ S.ϖ_irr, hvth] at h1
      unfold Frames.a
      rw [hg]
      push_cast at h1
      linarith
    have hprod : ∏ l ∈ P.ends, M.modK (P.Dm l * M.L.cj (P.Dm l)) = (resQ S.ϖ : ℝ) ^ (-(2 * S.vD)) := by
      have hsub : P.ends ⊆ Finset.range (r + 2) := by
        unfold LocNG.FPair.ends
        exact @Finset.filter_subset _ _ (_) _
      rw [← Finset.inter_eq_right.mpr hsub, ← Finset.prod_ite_mem, Finset.prod_range]
      unfold Frames.vD
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      have hz : ∀ (s : Finset (Fin (r + 2))) (f : Fin (r + 2) → ℤ),
          (resQ S.ϖ : ℝ) ^ (∑ i ∈ s, f i) = ∏ i ∈ s, (resQ S.ϖ : ℝ) ^ f i := by
        intro s f
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hq0.ne', ih]
      rw [hz]
      refine Finset.prod_congr rfl fun l _ => ?_
      by_cases hl : l ≠ 0 ∧ S.D l ≠ 0
      · rw [if_pos ((hends l).2 hl), if_pos hl, Dm_eq c]
        obtain ⟨n, hn0, hn⟩ := norm_mem M.L _ (hD l hl.2)
        rw [hn, hmod n hn0]
      · rw [if_neg (fun h => hl ((hends l).1 h)), if_neg hl]
        simp
    unfold LocNG.FPair.Hp Frames.Hp Frames.q
    rw [hprod, hdet, theta_eq c, hmod _ hth, hmod _ hd0, hvth, hva, ← zpow_add₀ hq0.ne',
      ← zpow_add₀ hq0.ne', ← Real.rpow_intCast, ← Real.rpow_mul hq0.le, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  · rintro ⟨h1, h2, h3⟩
    refine ⟨c.gg_none h1, ?_, fun l hl => ?_⟩
    · rw [Gv_eq c, hg] at h2
      rw [hg]
      exact vE_unit M.L S.ϖ S.ϖ_irr g hg0 h2.1 h2.2
    · have hu : LocNG.IsUnitO M (S.D l) := by
        by_cases h0 : l = 0
        · have : S.D l = 1 := by
            subst h0
            unfold Frames.D lead
            exact Matrix.det_isEmpty (n := Fin 0)
          rw [this]
          exact ⟨M.L.O.one_mem, 1, M.L.O.one_mem, mul_one 1⟩
        · have := h3 l ((hends l).2 ⟨h0, hl⟩)
          rwa [Dm_eq c] at this
      obtain ⟨n, hn0, hn⟩ := norm_mem M.L _ (hD l hl)
      obtain ⟨hm, y, hy, hxy⟩ := hu
      rw [hn]
      refine vE_unit M.L S.ϖ S.ϖ_irr n hn0 ?_ ⟨y * M.L.cj y, M.L.O.mul_mem hy (hcj y hy).1, ?_⟩
      · rw [← hn]
        exact M.L.O.mul_mem hm (hcj _ hm).1
      · rw [← hn, mul_mul_mul_comm, ← map_mul, hxy, map_one, mul_one]

end GlobalTheory.HL.CoordHeight
