import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaEigenStep
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

theorem convAll_algebraMap_teich (c : L) : T.ConvAll (algebraMap Γ T.B (T.teich c)) := fun r h0 h1 =>
  T.mem_Econ.1 (T.algebraMap_teich_mem_Econ c ⟨r, h0, h1⟩)

theorem extNorm_ofAll_teich {σ : Set.Ioo (0 : ℝ) 1} (ρ : Set.Ioc (0 : ℝ) σ) (c : L) :
    T.extNorm σ ρ (T.ofAll _ (convAll_algebraMap_teich c) σ) = ‖c‖ := by
  rw [extNorm_ofAll, coeffB_algebraMap, zcoeff_teich, gaussNorm_pi_single _ _ ρ.2.1]
  simp

theorem extNorm_sum_pow_le {σ : Set.Ioo (0 : ℝ) 1} (ρ : Set.Ioc (0 : ℝ) σ) {ι : Type*} (s : Finset ι)
    (f : ι → T.RobbaExt σ) {q : ℕ} (hq : q ≠ 0) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ i ∈ s, T.extNorm σ ρ (f i) ^ q ≤ M) : T.extNorm σ ρ (∑ i ∈ s, f i) ^ q ≤ M := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, extNorm_zero, zero_pow hq]; exact hM
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (pow_le_pow_left₀ (T.extNorm_nonneg _ _) (T.extNorm_add_le ρ _ _) _).trans
      (max_pow_le (T.extNorm_nonneg _ _) (T.extNorm_nonneg _ _) (h i (Finset.mem_insert_self i s))
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem pow_eq_mul_pow_pred (x : ℝ) {q : ℕ} (hq : 1 ≤ q) : x ^ q = x * x ^ (q - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ, mul_comm]

namespace TeichFrob

variable {F : T.TeichFrob} {n : ℕ}

abbrev twistDiff {ρ : Set.Ioo (0 : ℝ) 1} (A : Matrix (Fin n) (Fin n) (T.RobbaExt ρ)) (N : ℕ)
    (w : Fin n → T.RobbaExt ρ) : Fin n → T.RobbaExt (F.powRadius ρ) :=
  F.twistFrob A N ρ (F.powRadius_le_self ρ) w - fun i => T.res (F.powRadius_le_self ρ) (w i)

theorem twistDiff_sub {ρ : Set.Ioo (0 : ℝ) 1} (A : Matrix (Fin n) (Fin n) (T.RobbaExt ρ)) (N : ℕ)
    (w w' : Fin n → T.RobbaExt ρ) :
    twistDiff (F := F) A N (w - w') = twistDiff (F := F) A N w - twistDiff (F := F) A N w' := by
  funext i
  simp only [twistDiff, twistFrob_sub, Pi.sub_apply, map_sub]
  ring

theorem exists_start (ha : 0 < F.a) {ρ : Set.Ioo (0 : ℝ) 1}
    (A A' : Matrix (Fin n) (Fin n) (T.RobbaExt ρ)) (hAA : A * A' = 1) (N : ℕ) {C : ℝ} (hC : 1 ≤ C)
    (hAσ : ∀ i j, T.extNorm ρ (F.radPow ρ) (A i j) ≤ C)
    (hA'σ : ∀ i j, T.extNorm ρ (F.radPow ρ) (A' i j) ≤ C)
    (hA'σ2 : ∀ i j, T.extNorm ρ (F.radPow2 ρ) (A' i j) ≤ C)
    (hN : 8 * 2 ^ p ^ F.a * C ^ 2 * (F.powRadius ρ : ℝ) ^ (N * (p ^ F.a - 1)) ≤ 1) (i0 : Fin n) :
    ∃ (U : ℕ → Fin n → T.RobbaExt ρ) (e : ℕ → Fin n → T.RobbaExt (F.powRadius ρ)) (c : L),
      0 < ‖c‖ ∧
      (∀ J, T.extNorm ρ (F.radPow ρ) (U J i0 - T.ofAll _ (convAll_algebraMap_teich c) ρ) ≤ ‖c‖ / 2) ∧
      (∀ J, twistDiff (F := F) A N (U J) = e J) ∧
      (∀ J i, T.extNorm (F.powRadius ρ) (topRad _) (e J i) ≤ ‖c‖ / 2 / 2 ^ J) ∧
      (∀ J K, J ≤ K → ∀ i, T.extNorm ρ (F.radPow ρ) (U J i - U K i) ≤ ‖c‖ / 2 / 2 ^ J ∧
        T.extNorm ρ (topRad ρ) (U J i - U K i) ^ p ^ F.a ≤ C * (‖c‖ / 2 / 2 ^ J)) := by
  classical
  have hq2 : 2 ≤ p ^ F.a := F.two_le_q ha
  have hq0 : p ^ F.a ≠ 0 := by omega
  have hσ0 : (0 : ℝ) < F.powRadius ρ := (F.powRadius ρ).2.1
  have hσ1 : (F.powRadius ρ : ℝ) < 1 := (F.powRadius ρ).2.2
  have hσρ : (F.powRadius ρ : ℝ) ≤ ρ := F.powRadius_le_self ρ
  have hρr : (ρ : ℝ) ≤ F.rootRadius ρ := F.le_rootRadius ρ
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hκ0 : 0 < (F.powRadius ρ : ℝ) ^ N := pow_pos hσ0 N
  have hlam0 : 0 ≤ (F.powRadius ρ : ℝ) ^ (N * (p ^ F.a - 1)) := pow_nonneg hσ0.le _
  have hlam : ((F.powRadius ρ : ℝ) ^ p ^ F.a) ^ N =
      (F.powRadius ρ : ℝ) ^ N * (F.powRadius ρ : ℝ) ^ (N * (p ^ F.a - 1)) := by
    rw [← pow_mul, ← pow_add]; congr 1
    rw [Nat.mul_sub_one, Nat.add_sub_cancel' (Nat.le_mul_of_pos_right N (by omega)), mul_comm]

  set lo : ℝ := 2 ^ p ^ F.a * C * ((F.powRadius ρ : ℝ) ^ p ^ F.a) ^ N with hlo
  set hi : ℝ := (F.powRadius ρ : ℝ) ^ N / (2 * C) with hhi
  have hlo0 : 0 < lo := by positivity
  have hlohi : lo < hi := by
    rw [hlo, hhi, hlam, lt_div_iff₀ (by positivity)]
    have h8 : 2 * 2 ^ p ^ F.a * C ^ 2 * (F.powRadius ρ : ℝ) ^ (N * (p ^ F.a - 1)) < 1 := by
      have : 0 ≤ 2 ^ p ^ F.a * C ^ 2 * (F.powRadius ρ : ℝ) ^ (N * (p ^ F.a - 1)) := by positivity
      nlinarith
    have e : 2 ^ p ^ F.a * C * ((F.powRadius ρ : ℝ) ^ N * (F.powRadius ρ : ℝ) ^ (N * (p ^ F.a - 1))) *
        (2 * C) = (2 * 2 ^ p ^ F.a * C ^ 2 * (F.powRadius ρ : ℝ) ^ (N * (p ^ F.a - 1))) *
          (F.powRadius ρ : ℝ) ^ N := by ring
    rw [e]
    exact (mul_lt_mul_of_pos_right h8 hκ0).trans_le (one_mul _).le
  have hm : (p ^ F.a - 1 : ℕ) ≠ 0 := by omega
  have hαβ : lo ^ (((p ^ F.a - 1 : ℕ) : ℝ)⁻¹) < hi ^ (((p ^ F.a - 1 : ℕ) : ℝ)⁻¹) :=
    Real.rpow_lt_rpow hlo0.le hlohi (by positivity)
  obtain ⟨c, hc1, hc2⟩ := exists_norm_mem_Ioo_of_perfect p (L := L)
    (Real.rpow_pos_of_pos hlo0 _) hαβ
  have ha0 : 0 < ‖c‖ := (Real.rpow_pos_of_pos hlo0 _).trans hc1
  have hclo : lo ≤ ‖c‖ ^ (p ^ F.a - 1) := by
    have := pow_le_pow_left₀ (Real.rpow_pos_of_pos hlo0 _).le hc1.le (p ^ F.a - 1)
    rwa [Real.rpow_inv_natCast_pow hlo0.le hm] at this
  have hchi : ‖c‖ ^ (p ^ F.a - 1) ≤ hi := by
    have := pow_le_pow_left₀ ha0.le hc2.le (p ^ F.a - 1)
    rwa [Real.rpow_inv_natCast_pow (hlo0.trans hlohi).le hm] at this

  set V0 : Fin n → T.RobbaExt ρ := fun j => if j = i0 then T.ofAll _ (convAll_algebraMap_teich c) ρ else 0
    with hV0
  have hV0le : ∀ (r : Set.Ioc (0 : ℝ) ρ) j, T.extNorm ρ r (V0 j) ≤ ‖c‖ := fun r j => by
    simp only [hV0]
    split_ifs
    · rw [extNorm_ofAll_teich]
    · rw [extNorm_zero]; exact ha0.le

  have hP : ∀ i, T.extNorm (F.powRadius ρ) (topRad _)
      (F.twistFrob A N ρ (F.powRadius_le_self ρ) V0 i) ≤ ‖c‖ / 2 := fun i => by
    have h1 := extNorm_twistFrob_le A N (F.powRadius_le_self ρ) V0 (topRad ρ) hC0.le
      (pow_nonneg ha0.le _) (fun i j => hAσ i j)
      (fun j => pow_le_pow_left₀ (T.extNorm_nonneg _ _) (hV0le _ j) _) i
    refine h1.trans ?_
    change ((F.powRadius ρ : ℝ) ^ N)⁻¹ * (C * ‖c‖ ^ p ^ F.a) ≤ ‖c‖ / 2
    rw [pow_eq_mul_pow_pred ‖c‖ (by omega : 1 ≤ p ^ F.a), inv_mul_le_iff₀ hκ0]
    have := mul_le_mul_of_nonneg_left hchi (mul_nonneg hC0.le ha0.le)
    calc C * (‖c‖ * ‖c‖ ^ (p ^ F.a - 1)) = C * ‖c‖ * ‖c‖ ^ (p ^ F.a - 1) := by ring
      _ ≤ C * ‖c‖ * hi := this
      _ = (F.powRadius ρ : ℝ) ^ N * (‖c‖ / 2) := by rw [hhi]; field_simp
  let sσ : Set.Ioc (0 : ℝ) (F.rootRadius ρ) := ⟨F.powRadius ρ, hσ0, hσρ.trans hρr⟩
  have hB : ∀ i, T.extNorm (F.rootRadius ρ) sσ (F.untwist A' N V0 i) ≤ ‖c‖ / 2 := fun i => by
    have h1 := extNorm_untwist_pow_le N A' V0 sσ hC0.le ha0.le (fun i j => hA'σ2 i j)
      (fun j => hV0le _ j) i
    refine (pow_le_pow_iff_left₀ (T.extNorm_nonneg _ _) (by linarith) hq0).1 (h1.trans ?_)
    change ((F.powRadius ρ : ℝ) ^ p ^ F.a) ^ N * (C * ‖c‖) ≤ (‖c‖ / 2) ^ p ^ F.a
    rw [div_pow, le_div_iff₀ (by positivity), pow_eq_mul_pow_pred ‖c‖ (by omega : 1 ≤ p ^ F.a)]
    have := mul_le_mul_of_nonneg_left hclo ha0.le
    calc ((F.powRadius ρ : ℝ) ^ p ^ F.a) ^ N * (C * ‖c‖) * 2 ^ p ^ F.a = ‖c‖ * lo := by
          rw [hlo]; ring
      _ ≤ ‖c‖ * ‖c‖ ^ (p ^ F.a - 1) := this

  set b0 : Fin n → T.RobbaExt ρ := fun i => T.res hρr (F.untwist A' N V0 i) with hb0
  set u : Fin n → T.RobbaExt ρ := V0 + b0 with hu
  have he0 : ∀ i, twistDiff (F := F) A N u i =
      F.twistFrob A N ρ (F.powRadius_le_self ρ) V0 i + -T.res hσρ (b0 i) := fun i => by
    have h1 := congrFun (twistFrob_res_untwist (F := F) A N A' hAA V0) i
    simp only [twistDiff, hu, twistFrob_add, Pi.sub_apply, Pi.add_apply, map_add]
    rw [show F.twistFrob A N ρ (F.powRadius_le_self ρ) b0 i = T.res hσρ (V0 i) from h1]
    ring
  have he0b : ∀ i, T.extNorm (F.powRadius ρ) (topRad _) (twistDiff (F := F) A N u i) ≤ ‖c‖ / 2 :=
    fun i => by
      rw [he0]
      refine (T.extNorm_add_le _ _ _).trans (max_le (hP i) ?_)
      rw [extNorm_neg, hb0, extNorm_res, extNorm_res]
      exact hB i
  obtain ⟨e, z, hez, hstep, heb, hzσ, hzρ⟩ := exists_solve_seq ha A A' hAA N hC hAσ hA'σ hA'σ2 hN
    (twistDiff (F := F) A N u) (half_pos ha0) he0b
  set U : ℕ → Fin n → T.RobbaExt ρ := fun J => u - ∑ j ∈ Finset.range J, z j with hU
  have hUe : ∀ J, twistDiff (F := F) A N (U J) = e J := by
    intro J
    induction J with
    | zero => simp only [hU, Finset.range_zero, Finset.sum_empty, sub_zero]; exact hez.symm
    | succ J ih =>
      have : U (J + 1) = U J - z J := by
        simp only [hU, Finset.sum_range_succ]; abel
      rw [this, twistDiff_sub, ih, hstep J]
  have hdiff : ∀ J K, J ≤ K → U J - U K = ∑ j ∈ Finset.Ico J K, z j := fun J K hJK => by
    simp only [hU]
    rw [← Finset.sum_range_add_sum_Ico _ hJK]; abel
  have hhalf : ∀ J j, J ≤ j → ‖c‖ / 2 / 2 ^ j ≤ ‖c‖ / 2 / 2 ^ J := fun J j h =>
    div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ (by norm_num) h)
  refine ⟨U, e, c, ha0, fun J => ?_, hUe, heb, fun J K hJK i => ?_⟩
  ·
    have e1 : U J i0 - T.ofAll _ (convAll_algebraMap_teich c) ρ = b0 i0 + -∑ j ∈ Finset.range J, z j i0 := by
      simp only [hU, hu, Pi.sub_apply, Pi.add_apply, hV0, ↓reduceIte, Finset.sum_apply]; ring
    rw [e1]
    refine (T.extNorm_add_le _ _ _).trans (max_le ?_ ?_)
    · rw [hb0, extNorm_res]; exact hB i0
    · rw [extNorm_neg]
      refine extNorm_sum_le _ _ _ (by positivity) fun j _ => (hzσ j i0).trans ?_
      simpa using hhalf 0 j (Nat.zero_le j)
  · rw [show U J i - U K i = (U J - U K) i from rfl, hdiff J K hJK, Finset.sum_apply]
    refine ⟨extNorm_sum_le _ _ _ (by positivity) fun j hj =>
      (hzσ j i).trans (hhalf J j (Finset.mem_Ico.1 hj).1), ?_⟩
    exact extNorm_sum_pow_le _ _ _ hq0 (by positivity) fun j hj =>
      (hzρ j i).trans (mul_le_mul_of_nonneg_left (hhalf J j (Finset.mem_Ico.1 hj).1) hC0.le)

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

variable (F : T.TeichFrob) {n : ℕ}

def radSeq (ρ : Set.Ioo (0 : ℝ) 1) : ℕ → Set.Ioo (0 : ℝ) 1
  | 0 => ρ
  | t + 1 => F.powRadius (radSeq ρ t)

theorem radSeq_succ_le (ρ : Set.Ioo (0 : ℝ) 1) (t : ℕ) :
    (F.radSeq ρ (t + 1) : ℝ) ≤ F.radSeq ρ t :=
  F.powRadius_le_self _

theorem radSeq_le (ρ : Set.Ioo (0 : ℝ) 1) (t : ℕ) : (F.radSeq ρ t : ℝ) ≤ ρ := by
  induction t with
  | zero => exact le_rfl
  | succ t ih => exact (F.radSeq_succ_le ρ t).trans ih

theorem radSeq_le_pow (ha : 0 < F.a) (ρ : Set.Ioo (0 : ℝ) 1) (t : ℕ) :
    (F.radSeq ρ t : ℝ) ≤ (ρ : ℝ) ^ (t + 1) := by
  induction t with
  | zero => simp [radSeq]
  | succ t ih =>
    have h0 : (0 : ℝ) ≤ F.radSeq ρ t := (F.radSeq ρ t).2.1.le
    have h1 : (F.radSeq ρ t : ℝ) ≤ 1 := (F.radSeq ρ t).2.2.le
    change (F.radSeq ρ t : ℝ) ^ p ^ F.a ≤ _
    calc (F.radSeq ρ t : ℝ) ^ p ^ F.a ≤ (F.radSeq ρ t : ℝ) ^ 2 :=
          pow_le_pow_of_le_one h0 h1 (F.two_le_q ha)
      _ = (F.radSeq ρ t : ℝ) * F.radSeq ρ t := sq _
      _ ≤ (ρ : ℝ) ^ (t + 1) * ρ := mul_le_mul ih (F.radSeq_le ρ t) h0 (pow_nonneg ρ.2.1.le _)
      _ = (ρ : ℝ) ^ (t + 1 + 1) := (pow_succ _ _).symm

theorem tendsto_radSeq (ha : 0 < F.a) (ρ : Set.Ioo (0 : ℝ) 1) :
    Tendsto (fun t => (F.radSeq ρ t : ℝ)) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one ρ.2.1.le ρ.2.2).comp (tendsto_add_atTop_nat 1)
  exact squeeze_zero (fun t => (F.radSeq ρ t).2.1.le) (F.radSeq_le_pow ha ρ) h

def phiIter {ρ : Set.Ioo (0 : ℝ) 1} (A : Matrix (Fin n) (Fin n) (T.RobbaExt ρ)) (N : ℕ)
    (w : Fin n → T.RobbaExt ρ) : (t : ℕ) → Fin n → T.RobbaExt (F.radSeq ρ t)
  | 0 => w
  | t + 1 => F.twistFrob A N (F.radSeq ρ t) (F.radSeq_le ρ (t + 1)) (phiIter A N w t)

variable {F}

def SeqSmall {τ : Set.Ioo (0 : ℝ) 1} (x : ℕ → Fin n → T.RobbaExt τ) (r : Set.Ioc (0 : ℝ) τ) : Prop :=
  ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, ∀ i, T.extNorm τ r (x J i) ≤ ε

def SeqCauchy {τ : Set.Ioo (0 : ℝ) 1} (x : ℕ → Fin n → T.RobbaExt τ) (r : Set.Ioc (0 : ℝ) τ) :
    Prop :=
  ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, ∀ K ≥ J₀, ∀ i, T.extNorm τ r (x J i - x K i) ≤ ε

variable {ρ : Set.Ioo (0 : ℝ) 1} (A : Matrix (Fin n) (Fin n) (T.RobbaExt ρ)) (N : ℕ)

theorem twistFrob_small {τ : Set.Ioo (0 : ℝ) 1}
    (hτ : ((F.powRadius τ : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ ρ) (r : Set.Ioc (0 : ℝ) τ) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ w : Fin n → T.RobbaExt τ, (∀ j, T.extNorm τ r (w j) ≤ δ) →
      ∀ i, T.extNorm (F.powRadius τ) (F.powRad r) (F.twistFrob A N τ hτ w i) ≤ ε := by
  set s : Set.Ioc (0 : ℝ) ρ := ⟨_, (F.powRad r).2.1, (F.powRad r).2.2.trans hτ⟩
  set K : ℝ := ∑ i, ∑ j, T.extNorm ρ s (A i j) with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => T.extNorm_nonneg _ _
  have hKA : ∀ i j, T.extNorm ρ s (A i j) ≤ K := fun i j =>
    (Finset.single_le_sum (f := fun j => T.extNorm ρ s (A i j))
      (fun j _ => T.extNorm_nonneg _ _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, T.extNorm ρ s (A i j))
      (fun i _ => Finset.sum_nonneg fun j _ => T.extNorm_nonneg _ _) (Finset.mem_univ i))
  set c0 : ℝ := (((r : ℝ) ^ p ^ F.a) ^ N)⁻¹ * (K + 1) with hc0
  have hc00 : 0 < c0 := mul_pos (inv_pos.2 (pow_pos (pow_pos r.2.1 _) _)) (by linarith)
  refine ⟨min 1 (ε / c0), lt_min one_pos (div_pos hε hc00), fun w hw i => ?_⟩
  set δ := min 1 (ε / c0)
  have hδ0 : 0 ≤ δ := le_min zero_le_one (div_pos hε hc00).le
  have hwq : ∀ j, T.extNorm τ r (w j) ^ p ^ F.a ≤ δ := fun j =>
    (pow_le_pow_left₀ (T.extNorm_nonneg _ _) (hw j) _).trans
      (pow_le_of_le_one hδ0 (min_le_left _ _) F.q_pos.ne')
  refine (extNorm_twistFrob_le A N hτ w r hK0 hδ0 (fun i j => hKA i j) hwq i).trans ?_
  calc (((r : ℝ) ^ p ^ F.a) ^ N)⁻¹ * (K * δ) ≤ (((r : ℝ) ^ p ^ F.a) ^ N)⁻¹ * ((K + 1) * δ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hδ0)
          (inv_nonneg.2 (pow_nonneg (pow_nonneg r.2.1.le _) _))
    _ = c0 * δ := by rw [hc0]; ring
    _ ≤ c0 * (ε / c0) := mul_le_mul_of_nonneg_left (min_le_right _ _) hc00.le
    _ = ε := by field_simp

theorem SeqSmall.twistFrob {τ : Set.Ioo (0 : ℝ) 1}
    (hτ : ((F.powRadius τ : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ ρ) {x : ℕ → Fin n → T.RobbaExt τ}
    {r : Set.Ioc (0 : ℝ) τ} (hx : SeqSmall x r) :
    SeqSmall (fun J => F.twistFrob A N τ hτ (x J)) (F.powRad r) := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := twistFrob_small A N hτ r hε
  obtain ⟨J₀, hJ₀⟩ := hx δ hδ
  exact ⟨J₀, fun J hJ i => h (x J) (hJ₀ J hJ) i⟩

theorem SeqCauchy.twistFrob {τ : Set.Ioo (0 : ℝ) 1}
    (hτ : ((F.powRadius τ : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ ρ) {x : ℕ → Fin n → T.RobbaExt τ}
    {r : Set.Ioc (0 : ℝ) τ} (hx : SeqCauchy x r) :
    SeqCauchy (fun J => F.twistFrob A N τ hτ (x J)) (F.powRad r) := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := twistFrob_small A N hτ r hε
  obtain ⟨J₀, hJ₀⟩ := hx δ hδ
  refine ⟨J₀, fun J hJ K hK i => ?_⟩
  have := h (x J - x K) (fun j => hJ₀ J hJ K hK j) i
  rwa [twistFrob_sub] at this

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

variable {F : T.TeichFrob} {n : ℕ}

theorem exists_fixed (ha : 0 < F.a) {ρ : Set.Ioo (0 : ℝ) 1}
    (A A' : Matrix (Fin n) (Fin n) (T.RobbaExt ρ)) (hAA : A * A' = 1) (N : ℕ) {C : ℝ} (hC : 1 ≤ C)
    (hAσ : ∀ i j, T.extNorm ρ (F.radPow ρ) (A i j) ≤ C)
    (hA'σ : ∀ i j, T.extNorm ρ (F.radPow ρ) (A' i j) ≤ C)
    (hA'σ2 : ∀ i j, T.extNorm ρ (F.radPow2 ρ) (A' i j) ≤ C)
    (hN : 8 * 2 ^ p ^ F.a * C ^ 2 * (F.powRadius ρ : ℝ) ^ (N * (p ^ F.a - 1)) ≤ 1) (i0 : Fin n) :
    ∃ v : Fin n → T.RobbaExt ρ, v ≠ 0 ∧ twistDiff (F := F) A N v = 0 := by
  obtain ⟨U, e, c, ha0, hU0, hUe, heb, hUC⟩ :=
    exists_start ha A A' hAA N hC hAσ hA'σ hA'σ2 hN i0
  have hq0 : p ^ F.a ≠ 0 := F.q_pos.ne'
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hgeo : ∀ ε > 0, ∃ J₀ : ℕ, ∀ J ≥ J₀, ‖c‖ / 2 / 2 ^ J ≤ ε := by
    intro ε hε
    obtain ⟨J₀, hJ₀⟩ := exists_pow_lt_of_lt_one (div_pos hε (half_pos ha0))
      (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨J₀, fun J hJ => ?_⟩
    have h1 : ((1 : ℝ) / 2) ^ J ≤ (1 / 2) ^ J₀ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hJ
    calc ‖c‖ / 2 / 2 ^ J = ‖c‖ / 2 * (1 / 2) ^ J := by rw [one_div_pow, mul_one_div]
      _ ≤ ‖c‖ / 2 * (ε / (‖c‖ / 2)) :=
          mul_le_mul_of_nonneg_left (h1.trans hJ₀.le) (half_pos ha0).le
      _ = ε := by field_simp

  have hC0' : SeqCauchy U (topRad ρ) ∧ SeqCauchy U (F.radPow ρ) := by
    have key : ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀, ∀ K ≥ J₀, ∀ i,
        T.extNorm ρ (F.radPow ρ) (U J i - U K i) ≤ ε ∧ T.extNorm ρ (topRad ρ) (U J i - U K i) ≤ ε := by
      intro ε hε
      obtain ⟨J₀, hJ₀⟩ := hgeo (min ε (ε ^ p ^ F.a / C)) (lt_min hε (by positivity))
      refine ⟨J₀, fun J hJ K hK i => ?_⟩
      have hb : ∀ J K, J₀ ≤ J → J ≤ K → T.extNorm ρ (F.radPow ρ) (U J i - U K i) ≤ ε ∧
          T.extNorm ρ (topRad ρ) (U J i - U K i) ≤ ε := fun J K hJ hJK => by
        obtain ⟨h1, h2⟩ := hUC J K hJK i
        have h3 := hJ₀ J hJ
        refine ⟨h1.trans (h3.trans (min_le_left _ _)), ?_⟩
        refine (pow_le_pow_iff_left₀ (T.extNorm_nonneg _ _) hε.le hq0).1 (h2.trans ?_)
        calc C * (‖c‖ / 2 / 2 ^ J) ≤ C * (ε ^ p ^ F.a / C) :=
              mul_le_mul_of_nonneg_left (h3.trans (min_le_right _ _)) hC0.le
          _ = ε ^ p ^ F.a := by field_simp
      rcases le_total J K with h | h
      · exact hb J K hJ h
      · rw [T.extNorm_sub_comm, T.extNorm_sub_comm (topRad ρ)]
        exact hb K J hK h
    exact ⟨fun ε hε => (key ε hε).imp fun J₀ h J hJ K hK i => (h J hJ K hK i).2,
      fun ε hε => (key ε hε).imp fun J₀ h J hJ K hK i => (h J hJ K hK i).1⟩

  set x : (t : ℕ) → ℕ → Fin n → T.RobbaExt (F.radSeq ρ t) := fun t J => F.phiIter A N (U J) t
    with hxdef
  have hCt : ∀ t, SeqCauchy (x t) (topRad _) ∧
      SeqCauchy (x t) ⟨F.radSeq ρ (t + 1), (F.radSeq ρ (t + 1)).2.1, F.radSeq_succ_le ρ t⟩ := by
    intro t
    induction t with
    | zero => exact hC0'
    | succ t ih =>
      exact ⟨ih.1.twistFrob A N (F.radSeq_le ρ (t + 1)), ih.2.twistFrob A N (F.radSeq_le ρ (t + 1))⟩
  have hDt : ∀ t, SeqSmall (fun J => x (t + 1) J - fun i => T.res (F.radSeq_succ_le ρ t) (x t J i))
      (topRad (F.radSeq ρ (t + 1))) := by
    intro t
    induction t with
    | zero =>
      intro ε hε
      obtain ⟨J₀, hJ₀⟩ := hgeo ε hε
      refine ⟨J₀, fun J hJ i => ?_⟩
      change T.extNorm _ _ (twistDiff (F := F) A N (U J) i) ≤ ε
      rw [hUe J]
      exact (heb J i).trans (hJ₀ J hJ)
    | succ t ih =>
      have h := SeqSmall.twistFrob A N (F.radSeq_le ρ (t + 2)) ih
      refine fun ε hε => (h ε hε).imp fun J₀ hJ₀ J hJ i => ?_
      have e1 : (x (t + 2) J - fun i => T.res (F.radSeq_succ_le ρ (t + 1)) (x (t + 1) J i)) =
          F.twistFrob A N (F.radSeq ρ (t + 1)) (F.radSeq_le ρ (t + 2))
            (x (t + 1) J - fun i => T.res (F.radSeq_succ_le ρ t) (x t J i)) := by
        have h2 := twistFrob_res A N (F.radSeq_succ_le ρ t) (F.radSeq_le ρ (t + 1))
          (F.radSeq_le ρ (t + 2)) (x t J)
        have h3 : F.twistFrob A N (F.radSeq ρ (t + 1)) (F.radSeq_le ρ (t + 2)) (x (t + 1) J) -
              F.twistFrob A N (F.radSeq ρ (t + 1)) (F.radSeq_le ρ (t + 2))
                (fun j => T.res (F.radSeq_succ_le ρ t) (x t J j)) =
            F.twistFrob A N (F.radSeq ρ (t + 1)) (F.radSeq_le ρ (t + 2))
              (x (t + 1) J - fun i => T.res (F.radSeq_succ_le ρ t) (x t J i)) :=
          (twistFrob_sub A N (F.radSeq_le ρ (t + 2)) _ _).symm
        rw [← h3]
        exact congrArg₂ (· - ·) rfl h2.symm
      show T.extNorm _ (topRad (F.radSeq ρ (t + 2)))
        ((x (t + 2) J - fun i => T.res (F.radSeq_succ_le ρ (t + 1)) (x (t + 1) J i)) i) ≤ ε
      rw [e1]
      exact hJ₀ J hJ i

  have hglue : ∀ i, ∃ g : T.RobbaExt ρ, ∀ ε > 0, ∃ J₀, ∀ J ≥ J₀,
      T.extNorm ρ (topRad ρ) (g - U J i) ≤ ε ∧ T.extNorm ρ (F.radPow ρ) (g - U J i) ≤ ε := by
    intro i
    refine exists_glue (F.radSeq ρ) (F.radSeq_succ_le ρ) (F.tendsto_radSeq ha ρ)
      (fun t J => x t J i) (fun t ε hε => ?_) (fun t ε hε => ?_)
    · obtain ⟨J₁, h1⟩ := (hCt t).1 ε hε
      obtain ⟨J₂, h2⟩ := (hCt t).2 ε hε
      exact ⟨max J₁ J₂, fun J hJ K hK => ⟨h1 J (le_of_max_le_left hJ) K (le_of_max_le_left hK) i,
        h2 J (le_of_max_le_right hJ) K (le_of_max_le_right hK) i⟩⟩
    · obtain ⟨J₀, h⟩ := hDt t ε hε
      refine ⟨J₀, fun J hJ => ?_⟩
      have := h J hJ i
      rw [← extNorm_neg, neg_sub]
      exact this
  choose g hg using hglue
  refine ⟨g, fun hv => ?_, ?_⟩
  ·
    have hg0 : g i0 = 0 := congrFun hv i0
    obtain ⟨J₀, hJ₀⟩ := hg i0 (‖c‖ / 4) (by positivity)
    have h1 : T.extNorm ρ (F.radPow ρ) (g i0 - U J₀ i0) ≤ ‖c‖ / 4 := (hJ₀ J₀ le_rfl).2
    have h2 := hU0 J₀
    have h3 : T.extNorm ρ (F.radPow ρ) (T.ofAll _ (convAll_algebraMap_teich c) ρ) = ‖c‖ := extNorm_ofAll_teich _ c
    have e1 : T.ofAll _ (convAll_algebraMap_teich c) ρ = -((g i0 - U J₀ i0) + (U J₀ i0 - T.ofAll _ (convAll_algebraMap_teich c) ρ)) := by
      rw [hg0]; ring
    have h4 : T.extNorm ρ (F.radPow ρ) (T.ofAll _ (convAll_algebraMap_teich c) ρ) ≤ max (‖c‖ / 4) (‖c‖ / 2) := by
      rw [e1, extNorm_neg]
      exact (T.extNorm_add_le _ _ _).trans (max_le_max h1 h2)
    rw [h3] at h4
    have : max (‖c‖ / 4) (‖c‖ / 2) < ‖c‖ := max_lt (by linarith) (by linarith)
    linarith
  ·
    funext i
    rw [Pi.zero_apply]
    apply (T.extNorm_eq_zero_iff (topRad _)).1
    have key : ∀ ε > 0, T.extNorm _ (topRad _) (twistDiff (F := F) A N g i) ≤ ε := by
      intro ε hε
      obtain ⟨δ, hδ, hsm⟩ := twistFrob_small A N (F.powRadius_le_self ρ) (topRad ρ) hε
      have hev : ∀ j, ∀ᶠ J in atTop, T.extNorm ρ (topRad ρ) (g j - U J j) ≤ δ := fun j => by
        obtain ⟨J₀, h⟩ := hg j δ hδ
        exact eventually_atTop.2 ⟨J₀, fun J hJ => (h J hJ).1⟩
      have hev2 : ∀ᶠ J in atTop, T.extNorm ρ (F.radPow ρ) (g i - U J i) ≤ ε := by
        obtain ⟨J₀, h⟩ := hg i ε hε
        exact eventually_atTop.2 ⟨J₀, fun J hJ => (h J hJ).2⟩
      have hev3 : ∀ᶠ J in atTop, T.extNorm _ (topRad _) (e J i) ≤ ε := by
        obtain ⟨J₀, h⟩ := hgeo ε hε
        exact eventually_atTop.2 ⟨J₀, fun J hJ => (heb J i).trans (h J hJ)⟩
      obtain ⟨J, hJ1, hJ2, hJ3⟩ := ((Filter.eventually_all.2 hev).and (hev2.and hev3)).exists
      have h1 : F.twistFrob A N ρ (F.powRadius_le_self ρ) g i =
          F.twistFrob A N ρ (F.powRadius_le_self ρ) (g - U J) i +
            F.twistFrob A N ρ (F.powRadius_le_self ρ) (U J) i := by
        rw [twistFrob_sub, Pi.sub_apply, sub_add_cancel]
      have h2 : twistDiff (F := F) A N (U J) i = e J i := congrFun (hUe J) i
      simp only [twistDiff, Pi.sub_apply] at h2 ⊢
      have e2 : F.twistFrob A N ρ (F.powRadius_le_self ρ) g i - T.res (F.powRadius_le_self ρ) (g i) =
          F.twistFrob A N ρ (F.powRadius_le_self ρ) (g - U J) i + e J i +
            -T.res (F.powRadius_le_self ρ) (g i - U J i) := by
        rw [h1, ← h2, map_sub]; ring
      rw [e2]
      refine (extNorm_add_add_le_max _ _ _ _).trans (max_le (hsm (g - U J) (fun j => hJ1 j) i)
        (max_le hJ3 ?_))
      rw [extNorm_neg, extNorm_res]
      exact hJ2
    have h0 := T.extNorm_nonneg (topRad (F.powRadius ρ)) (twistDiff (F := F) A N g i)
    by_contra hne
    have hpos : 0 < T.extNorm _ (topRad _) (twistDiff (F := F) A N g i) :=
      lt_of_le_of_ne h0 (Ne.symm hne)
    linarith [key _ (half_pos hpos)]

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

theorem ofRad_piE (σ : Set.Ioo (0 : ℝ) 1) : T.ofRad σ (T.piE σ) = T.πTilde :=
  (T.edagToTilde_apply (T.algebraMap_π_mem_Econ σ)).symm

theorem exists_ofRad_fintype {ι : Type*} [Fintype ι] (f : ι → T.RobbaTilde) :
    ∃ (ρ : Set.Ioo (0 : ℝ) 1) (g : ι → T.RobbaExt ρ), ∀ i, T.ofRad ρ (g i) = f i := by
  classical
  have key : ∀ s : Finset ι, ∃ (ρ : Set.Ioo (0 : ℝ) 1) (g : ι → T.RobbaExt ρ),
      ∀ i ∈ s, T.ofRad ρ (g i) = f i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨⟨1 / 2, by norm_num, by norm_num⟩, 0, fun i hi => by simp at hi⟩
    | insert a s ha ih =>
      obtain ⟨ρ1, g1, h1⟩ := ih
      obtain ⟨ρ2, y, hy⟩ := T.exists_ofRad (f a)
      let m : Set.Ioo (0 : ℝ) 1 := ⟨min (ρ1 : ℝ) ρ2, lt_min ρ1.2.1 ρ2.2.1, min_lt_of_left_lt ρ1.2.2⟩
      have hm1 : (m : ℝ) ≤ ρ1 := min_le_left _ _
      have hm2 : (m : ℝ) ≤ ρ2 := min_le_right _ _
      refine ⟨m, fun i => if i = a then T.res hm2 y else T.res hm1 (g1 i), fun i hi => ?_⟩
      by_cases hia : i = a
      · subst hia; simp only [↓reduceIte, T.ofRad_res, hy]
      · rcases Finset.mem_insert.1 hi with h | hi'
        · exact absurd h hia
        · simp only [if_neg hia, T.ofRad_res, h1 i hi']
  obtain ⟨ρ, g, h⟩ := key Finset.univ
  exact ⟨ρ, g, fun i => h i (Finset.mem_univ i)⟩

namespace TeichFrob

variable {F : T.TeichFrob} {n : ℕ}

theorem exists_eigen_ext (ha : 0 < F.a) {ρ : Set.Ioo (0 : ℝ) 1}
    (A A' : Matrix (Fin n) (Fin n) (T.RobbaExt ρ)) (hAA : A * A' = 1) (hn : 0 < n) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ v : Fin n → T.RobbaExt ρ, v ≠ 0 ∧
      ∀ i, ∑ j, T.res (F.powRadius_le_self ρ) (A i j) * F.extFrob ρ (v j) =
        T.piE (F.powRadius ρ) ^ N * T.res (F.powRadius_le_self ρ) (v i) := by
  have hq2 : 2 ≤ p ^ F.a := F.two_le_q ha
  set f : Fin n → Fin n → ℝ := fun i j => T.extNorm ρ (F.radPow ρ) (A i j) +
    T.extNorm ρ (F.radPow ρ) (A' i j) + T.extNorm ρ (F.radPow2 ρ) (A' i j) with hf
  have hfe : ∀ i j, f i j = T.extNorm ρ (F.radPow ρ) (A i j) +
      T.extNorm ρ (F.radPow ρ) (A' i j) + T.extNorm ρ (F.radPow2 ρ) (A' i j) := fun i j => rfl
  have hf0 : ∀ i j, 0 ≤ f i j := fun i j => by
    have := T.extNorm_nonneg (F.radPow ρ) (A i j)
    have := T.extNorm_nonneg (F.radPow ρ) (A' i j)
    have := T.extNorm_nonneg (F.radPow2 ρ) (A' i j)
    rw [hfe]; linarith
  set C : ℝ := 1 + ∑ i, ∑ j, f i j with hCdef
  have hfC : ∀ i j, f i j ≤ C := fun i j => by
    have h1 := Finset.single_le_sum (f := fun j => f i j) (fun j _ => hf0 i j) (Finset.mem_univ j)
    have h2 := Finset.single_le_sum (f := fun i => ∑ j, f i j)
      (fun i _ => Finset.sum_nonneg fun j _ => hf0 i j) (Finset.mem_univ i)
    rw [hCdef]; linarith
  have hC1 : 1 ≤ C := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hf0 i j
    rw [hCdef]; linarith
  have hAσ : ∀ i j, T.extNorm ρ (F.radPow ρ) (A i j) ≤ C := fun i j => by
    have := hfC i j
    have := T.extNorm_nonneg (F.radPow ρ) (A' i j)
    have := T.extNorm_nonneg (F.radPow2 ρ) (A' i j)
    rw [hfe] at *; linarith
  have hA'σ : ∀ i j, T.extNorm ρ (F.radPow ρ) (A' i j) ≤ C := fun i j => by
    have := hfC i j
    have := T.extNorm_nonneg (F.radPow ρ) (A i j)
    have := T.extNorm_nonneg (F.radPow2 ρ) (A' i j)
    rw [hfe] at *; linarith
  have hA'σ2 : ∀ i j, T.extNorm ρ (F.radPow2 ρ) (A' i j) ≤ C := fun i j => by
    have := hfC i j
    have := T.extNorm_nonneg (F.radPow ρ) (A i j)
    have := T.extNorm_nonneg (F.radPow ρ) (A' i j)
    rw [hfe] at *; linarith

  have hσ0 : (0 : ℝ) < F.powRadius ρ := (F.powRadius ρ).2.1
  have hσ1 : (F.powRadius ρ : ℝ) < 1 := (F.powRadius ρ).2.2
  have hl1 : (F.powRadius ρ : ℝ) ^ (p ^ F.a - 1) < 1 := pow_lt_one₀ hσ0.le hσ1 (by omega)
  have hK : 0 < 8 * 2 ^ p ^ F.a * C ^ 2 := by positivity
  obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hK) hl1
  refine ⟨N₀, fun N hN => ?_⟩
  have hN' : 8 * 2 ^ p ^ F.a * C ^ 2 * (F.powRadius ρ : ℝ) ^ (N * (p ^ F.a - 1)) ≤ 1 := by
    have h1 : (F.powRadius ρ : ℝ) ^ (N * (p ^ F.a - 1)) ≤ ((F.powRadius ρ : ℝ) ^ (p ^ F.a - 1)) ^ N₀ := by
      rw [mul_comm, pow_mul]
      exact pow_le_pow_of_le_one (pow_nonneg hσ0.le _) hl1.le hN
    calc 8 * 2 ^ p ^ F.a * C ^ 2 * (F.powRadius ρ : ℝ) ^ (N * (p ^ F.a - 1)) ≤
        8 * 2 ^ p ^ F.a * C ^ 2 * (8 * 2 ^ p ^ F.a * C ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left (h1.trans hN₀.le) hK.le
      _ = 1 := mul_inv_cancel₀ hK.ne'
  obtain ⟨v, hv0, hv⟩ := exists_fixed ha A A' hAA N hC1 hAσ hA'σ hA'σ2 hN' ⟨0, hn⟩
  refine ⟨v, hv0, fun i => ?_⟩
  have h := congrFun hv i
  simp only [twistDiff, twistFrob, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h
  rw [← h, ← mul_assoc, ← mul_pow, piE_mul_piInvE, one_pow, one_mul]

variable (F) in

theorem exists_eigenvector (ha : 0 < F.a) (hn : 0 < n) (A : Matrix.GeneralLinearGroup (Fin n) T.RobbaTilde) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ v : Fin n → T.RobbaTilde, v ≠ 0 ∧
      (A : Matrix (Fin n) (Fin n) T.RobbaTilde).mulVec (fun i => F.tildeFrob (v i)) =
        T.πTilde ^ N • v := by
  obtain ⟨ρ, B, hB⟩ := exists_ofRad_fintype (T := T) fun x : Bool × Fin n × Fin n =>
    if x.1 then A.val x.2.1 x.2.2 else A⁻¹.val x.2.1 x.2.2
  set A0 : Matrix (Fin n) (Fin n) (T.RobbaExt ρ) := fun i j => B (true, i, j) with hA0def
  set A0' : Matrix (Fin n) (Fin n) (T.RobbaExt ρ) := fun i j => B (false, i, j) with hA0'def
  have hA0 : ∀ i j, T.ofRad ρ (A0 i j) = (A : Matrix (Fin n) (Fin n) T.RobbaTilde) i j :=
    fun i j => by simpa using hB (true, i, j)
  have hA0' : ∀ i j, T.ofRad ρ (A0' i j) = A⁻¹.val i j :=
    fun i j => by simpa using hB (false, i, j)
  have hAA : A0 * A0' = 1 := by
    ext i k
    apply T.ofRad_injective ρ
    have h1 : (A.val * A⁻¹.val) i k = (1 : Matrix (Fin n) (Fin n) T.RobbaTilde) i k := by
      rw [Units.mul_inv]
    rw [Matrix.mul_apply, map_sum]
    simp only [map_mul, hA0, hA0']
    rw [← Matrix.mul_apply, h1, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  obtain ⟨N₀, hN₀⟩ := exists_eigen_ext (F := F) ha A0 A0' hAA hn
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨v, hv0, hv⟩ := hN₀ N hN
  refine ⟨fun i => T.ofRad ρ (v i), fun h => hv0 (funext fun i => T.ofRad_injective ρ ?_), ?_⟩
  · rw [Pi.zero_apply, map_zero]; exact congrFun h i
  · funext i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    have h := congrArg (T.ofRad (F.powRadius ρ)) (hv i)
    simp only [map_sum, map_mul, map_pow, ofRad_piE, T.ofRad_res, ← F.tildeFrob_ofRad, hA0] at h
    exact h

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
