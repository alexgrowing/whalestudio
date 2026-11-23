import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaDMApprox
import GroundTheory.PAdicHodge.ExtRobbaUnits
import GroundTheory.PAdicHodge.ExtRobbaNewton
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

def ConvAll (b : T.B) : Prop := ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ConvergesAt (T.coeffB b) ρ

variable {T}

theorem ConvAll.add {a b : T.B} (ha : T.ConvAll a) (hb : T.ConvAll b) : T.ConvAll (a + b) :=
  fun ρ h0 h1 => (T.convergesAt_coeffB_add h0 h1 (ha ρ h0 h1) (hb ρ h0 h1)).1

theorem ConvAll.neg {a : T.B} (ha : T.ConvAll a) : T.ConvAll (-a) :=
  fun ρ h0 h1 => (T.convergesAt_coeffB_neg h0 h1 (ha ρ h0 h1)).1

theorem ConvAll.sub {a b : T.B} (ha : T.ConvAll a) (hb : T.ConvAll b) : T.ConvAll (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add hb.neg

theorem ConvAll.mul {a b : T.B} (ha : T.ConvAll a) (hb : T.ConvAll b) : T.ConvAll (a * b) :=
  fun ρ h0 h1 => (T.convergesAt_coeffB_mul h0 h1 (ha ρ h0 h1) (hb ρ h0 h1)).1

theorem convAll_π_pow (c : ℕ) : T.ConvAll (algebraMap Γ T.B T.π ^ c) :=
  fun _ h0 _ => (gaussNorm_π_pow c h0).1

theorem convAll_zero : T.ConvAll (0 : T.B) := fun ρ _ _ => by
  rw [T.coeffB_zero_B]; exact convergesAt_zero

theorem convAll_sum {ι : Type*} (s : Finset ι) (f : ι → T.B) (h : ∀ i ∈ s, T.ConvAll (f i)) :
    T.ConvAll (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact convAll_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

def ofAll (b : T.B) (hb : T.ConvAll b) (σ : Set.Ioo (0 : ℝ) 1) : T.RobbaExt σ :=
  ((⟨b, hb σ σ.2.1 σ.2.2⟩ : T.Econ σ) : T.RobbaExt σ)

theorem ofAll_add {a b : T.B} (ha : T.ConvAll a) (hb : T.ConvAll b) (σ : Set.Ioo (0 : ℝ) 1) :
    T.ofAll (a + b) (ha.add hb) σ = T.ofAll a ha σ + T.ofAll b hb σ := by
  rw [ofAll, ofAll, ofAll, ← Completion.coe_add]; rfl

theorem ofAll_sub {a b : T.B} (ha : T.ConvAll a) (hb : T.ConvAll b) (σ : Set.Ioo (0 : ℝ) 1) :
    T.ofAll (a - b) (ha.sub hb) σ = T.ofAll a ha σ - T.ofAll b hb σ := by
  rw [ofAll, ofAll, ofAll, ← Completion.coe_sub]; rfl

theorem ofAll_mul {a b : T.B} (ha : T.ConvAll a) (hb : T.ConvAll b) (σ : Set.Ioo (0 : ℝ) 1) :
    T.ofAll (a * b) (ha.mul hb) σ = T.ofAll a ha σ * T.ofAll b hb σ := by
  rw [ofAll, ofAll, ofAll, ← Completion.coe_mul]; rfl

theorem ofAll_congr {a b : T.B} (ha : T.ConvAll a) (hb : T.ConvAll b) (h : a = b)
    (σ : Set.Ioo (0 : ℝ) 1) : T.ofAll a ha σ = T.ofAll b hb σ := by
  subst h; rfl

theorem extNorm_ofAll {b : T.B} (hb : T.ConvAll b) {σ : Set.Ioo (0 : ℝ) 1}
    (ρ : Set.Ioc (0 : ℝ) σ) : T.extNorm σ ρ (T.ofAll b hb σ) = gaussNorm (T.coeffB b) ρ :=
  T.extNorm_coe ρ _

theorem res_ofAll {b : T.B} (hb : T.ConvAll b) {σ σ' : Set.Ioo (0 : ℝ) 1} (h : (σ' : ℝ) ≤ σ) :
    T.res h (T.ofAll b hb σ) = T.ofAll b hb σ' := by
  rw [ofAll, res_coe]; rfl

theorem πExt_pow_eq_ofAll (c : ℕ) (σ : Set.Ioo (0 : ℝ) 1) :
    T.πExt σ ^ c = T.ofAll _ (convAll_π_pow c) σ := by
  induction c with
  | zero =>
    rw [pow_zero, ofAll, ← Completion.coe_one]
    congr 1
  | succ c ih =>
    rw [pow_succ, ih, πExt, ofAll, ofAll, ← Completion.coe_mul]
    congr 1

theorem TeichFrob.convAll_toB (F : T.TeichFrob) {b : T.B} (hb : T.ConvAll b) :
    T.ConvAll (F.toB b) := F.convergesAt_toB_of_forall hb

theorem TeichFrob.extFrob_ofAll (F : T.TeichFrob) {b : T.B} (hb : T.ConvAll b)
    (σ : Set.Ioo (0 : ℝ) 1) :
    F.extFrob σ (T.ofAll b hb σ) = T.ofAll (F.toB b) (F.convAll_toB hb) (F.powRadius σ) := by
  rw [ofAll, F.extFrob_coe]; rfl

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

theorem exists_weight_le_of_convergesAt {a : ℤ → L} {ρ : ℝ} (h : ConvergesAt a ρ) {ε : ℝ}
    (hε : 0 < ε) : ∃ K : ℤ, ∀ k, K ≤ k → ‖a k‖ * ρ ^ k ≤ ε := by
  obtain ⟨B, hB⟩ := (h.finite_le hε).bddAbove
  refine ⟨B + 1, fun k hk => ?_⟩
  by_contra hc
  have := hB (show k ∈ {n | ε ≤ ‖a n‖ * ρ ^ n} from (not_le.1 hc).le)
  omega

theorem exists_trunc {τ : ℝ} {b : T.B} (hb : ConvergesAt (T.coeffB b) τ) {ε : ℝ}
    (hε : 0 < ε) : ∃ d : T.B, T.ConvAll d ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ τ →
      ConvergesAt (T.coeffB (b - d)) ρ ∧ gaussNorm (T.coeffB (b - d)) ρ ≤ ε := by
  obtain ⟨K0, hK0⟩ := exists_weight_le_of_convergesAt hb hε
  obtain ⟨M, hMN, hMK⟩ : ∃ M : ℕ, T.den b ≤ M ∧ K0 ≤ (M : ℤ) - T.den b :=
    ⟨T.den b + K0.toNat, by omega, by omega⟩
  refine ⟨algebraMap Γ T.B (T.partialSum (T.num b) M) * IsLocalization.Away.invSelf T.π ^ T.den b, ?_, ?_⟩
  · intro ρ hρ0 hρ1
    refine convergesAt_of_eventually hρ0 (T.coeffB_neg_exists _) fun δ hδ => ⟨(M : ℤ) - T.den b, fun k hk => ?_⟩
    rw [T.coeffB_eq (T.mul_pow_eq_of_invSelf _)]
    simp only
    lift k + (T.den b : ℤ) to ℕ using (by omega) with j hj
    rw [zcoeff_natCast, partialSum, coeff_finSum, if_neg (by omega), norm_zero, zero_mul]
    exact hδ.le
  · have hbd : b - algebraMap Γ T.B (T.partialSum (T.num b) M) * IsLocalization.Away.invSelf T.π ^ T.den b =
        algebraMap Γ T.B (T.num b - T.partialSum (T.num b) M) * IsLocalization.Away.invSelf T.π ^ T.den b := by
      rw [map_sub, sub_mul, ← T.eq_num_mul b]
    have hcb : ∀ k, T.coeffB (b - algebraMap Γ T.B (T.partialSum (T.num b) M) *
        IsLocalization.Away.invSelf T.π ^ T.den b) k =
          if k + (T.den b : ℤ) < M then 0 else T.coeffB b k := by
      intro k
      rw [hbd, T.coeffB_eq (T.mul_pow_eq_of_invSelf _), T.coeffB_eq (T.num_spec b)]
      simp only
      rcases lt_or_ge (k + (T.den b : ℤ)) 0 with h | h
      · rw [T.zcoeff_of_neg _ h, T.zcoeff_of_neg _ h, if_pos (by omega)]
      · lift k + (T.den b : ℤ) to ℕ using h with j hj
        rw [zcoeff_natCast, zcoeff_natCast, coeff_sub_partialSum]
        by_cases hjM : j < M
        · rw [if_pos hjM, if_pos (by exact_mod_cast hjM)]
        · rw [if_neg hjM, if_neg (by exact_mod_cast hjM)]
    intro ρ hρ0 hρτ
    have hbρ : ConvergesAt (T.coeffB b) ρ := convergesAt_of_le (T.coeffB_neg_exists b) hb hρ0 hρτ
    have hle : ∀ k, ‖T.coeffB (b - algebraMap Γ T.B (T.partialSum (T.num b) M) *
        IsLocalization.Away.invSelf T.π ^ T.den b) k‖ ≤ ‖T.coeffB b k‖ := fun k => by
      rw [hcb]; split_ifs <;> simp
    refine ⟨(convergesAt_of_norm_le hρ0 hle hbρ).1, gaussNorm_le fun k => ?_⟩
    rw [hcb]
    split_ifs with hk
    · rw [norm_zero, zero_mul]; exact hε.le
    · have hk0 : 0 ≤ k := by omega
      refine le_trans ?_ (hK0 k (by omega))
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      lift k to ℕ using hk0
      rw [zpow_natCast, zpow_natCast]
      exact pow_le_pow_left₀ hρ0.le hρτ k

theorem gaussNorm_le_max_of_mem_Icc {b : T.B} {α β σ : ℝ} (hα : 0 < α) (hσ : σ ∈ Set.Icc α β)
    (hbα : ConvergesAt (T.coeffB b) α) (hbβ : ConvergesAt (T.coeffB b) β) :
    gaussNorm (T.coeffB b) σ ≤ max (gaussNorm (T.coeffB b) α) (gaussNorm (T.coeffB b) β) :=
  gaussNorm_le fun n => (weight_le_max_of_mem_Icc hα hσ n).trans
    (max_le_max (hbα.le_gaussNorm n) (hbβ.le_gaussNorm n))

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

theorem exists_approx_convAll {σ : Set.Ioo (0 : ℝ) 1} (z : T.RobbaExt σ) (r : Set.Ioc (0 : ℝ) σ)
    {ε : ℝ} (hε : 0 < ε) : ∃ d : T.B, ∃ hd : T.ConvAll d, ∀ ρ : Set.Ioc (0 : ℝ) σ,
      (r : ℝ) ≤ ρ → T.extNorm σ ρ (z - T.ofAll d hd σ) ≤ ε := by
  obtain ⟨b, hb⟩ := T.exists_approx z r (half_pos hε)
  obtain ⟨d, hd, hbd⟩ := exists_trunc (T := T) (τ := σ) b.2 (half_pos hε)
  refine ⟨d, hd, fun ρ hρ => ?_⟩
  have e : z - T.ofAll d hd σ = (z - b) + ((b : T.RobbaExt σ) - T.ofAll d hd σ) := by ring
  rw [e]
  refine (T.extNorm_add_le ρ _ _).trans (max_le ((hb ρ hρ).le.trans (by linarith)) ?_)
  rw [ofAll, ← Completion.coe_sub, extNorm_coe]
  exact ((hbd ρ ρ.2.1 ρ.2.2).2).trans (by linarith)

theorem exists_tendsto_of_gaussNorm {σ : Set.Ioo (0 : ℝ) 1} (s : ℕ → T.Econ σ)
    (h : ∀ ρ : Set.Ioc (0 : ℝ) σ, ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      gaussNorm (T.coeffB ((s m : T.B) - s n)) ρ < ε) :
    ∃ l : T.RobbaExt σ, Tendsto (fun n => (s n : T.RobbaExt σ)) atTop (𝓝 l) := by
  have hs : CauchySeq s := by
    unfold CauchySeq
    change Cauchy (uniformSpace := ⨅ ρ, T.uniformAt σ ρ) _
    have : Nonempty (Set.Ioc (0 : ℝ) σ) := ⟨topRad σ⟩
    rw [cauchy_iInf_uniformSpace]
    intro ρ
    let psm : PseudoMetricSpace (T.Econ σ) := (T.gaussSeminorm σ ρ).toSeminormedRing.toPseudoMetricSpace
    have key : @CauchySeq _ _ psm.toUniformSpace _ s := by
      refine (@Metric.cauchySeq_iff _ _ psm _ _ s).2 fun ε hε => ?_
      obtain ⟨N, hN⟩ := h ρ ε hε
      exact ⟨N, fun m hm n hn => by rw [T.dist_uniformAt']; exact hN m hm n hn⟩
    exact key
  exact cauchySeq_tendsto_of_complete ((Completion.uniformContinuous_coe _).comp_cauchySeq hs)

namespace TeichFrob

variable (F : T.TeichFrob)

theorem exists_step [IsAlgClosed L] (ha : 0 < F.a) (c : ℕ) {σ : Set.Ioo (0 : ℝ) 1}
    (z : T.RobbaExt σ) (r : Set.Ioc (0 : ℝ) σ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t d R : T.B, T.ConvAll t ∧ T.ConvAll R ∧ ∃ hd : T.ConvAll d,
      F.toB t - algebraMap Γ T.B T.π ^ c * t = d - R ∧
      (∀ ρ : Set.Ioc (0 : ℝ) σ, (r : ℝ) ≤ ρ →
        T.extNorm σ ρ (z - T.ofAll d hd σ) ≤ ε ∧ gaussNorm (T.coeffB R) ρ ≤ ε) ∧
      (∀ ρ : ℝ, 0 < ρ → ρ < 1 → gaussNorm (T.coeffB t) ρ ≤
        max 2 (fwdConst (p ^ F.a) c ρ * ρ ^ (-(c : ℤ))) * gaussNorm (T.coeffB d) ρ) := by
  have hq := F.two_le_q ha
  obtain ⟨d, hd, hzd⟩ := exists_approx_convAll z r hε
  have hr0 : (0 : ℝ) < r := r.2.1
  have hr1 : (r : ℝ) < 1 := rad_lt_one σ r
  set D := max (gaussNorm (T.coeffB d) r) (gaussNorm (T.coeffB d) σ)
  have hD : 0 ≤ D := le_max_of_le_left (gaussNorm_nonneg hr0)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, (r : ℝ) ^ (-((c * K : ℕ) : ℤ)) * (1 / 2 : ℝ) ^ ((p ^ F.a) ^ K - 1) * D
      ≤ ε := by
    have := (tendsto_fwdConst_terms hq c hr0).mul_const D
    rw [zero_mul] at this
    exact (this.eventually (ge_mem_nhds hε)).exists
  obtain ⟨t, R, heq, ht, hR⟩ := F.exists_approx_sol ha c hd K
  refine ⟨t, d, R, fun ρ h0 h1 => (ht ρ h0 h1).1, fun ρ h0 h1 => (hR ρ h0 h1).1, hd, heq,
    fun ρ hρ => ⟨hzd ρ hρ, ?_⟩, fun ρ h0 h1 => (ht ρ h0 h1).2⟩
  have hρ0 : (0 : ℝ) < ρ := ρ.2.1
  have hρ1 : (ρ : ℝ) < 1 := rad_lt_one σ ρ
  refine (hR ρ hρ0 hρ1).2.trans (le_trans ?_ hK)
  have hdρ : gaussNorm (T.coeffB d) ρ ≤ D :=
    gaussNorm_le_max_of_mem_Icc hr0 ⟨hρ, ρ.2.2⟩ (hd r hr0 hr1) (hd σ σ.2.1 σ.2.2)
  have hz : (ρ : ℝ) ^ (-((c * K : ℕ) : ℤ)) ≤ (r : ℝ) ^ (-((c * K : ℕ) : ℤ)) := by
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    exact inv_anti₀ (pow_pos hr0 _) (pow_le_pow_left₀ hr0.le hρ _)
  exact mul_le_mul (mul_le_mul_of_nonneg_right hz (by positivity)) hdρ (gaussNorm_nonneg hρ0)
    (by positivity)

end TeichFrob

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

variable (F : T.TeichFrob)

theorem continuous_extFrob (σ : Set.Ioo (0 : ℝ) 1) : Continuous (F.extFrob σ) :=
  Completion.continuous_map

theorem powRadius_le_self (σ : Set.Ioo (0 : ℝ) 1) : ((F.powRadius σ : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ σ :=
  pow_le_of_le_one σ.2.1.le σ.2.2.le F.q_pos.ne'

def halvedRad (τ : Set.Ioo (0 : ℝ) 1) (N : ℕ) : Set.Ioc (0 : ℝ) τ :=
  ⟨τ * (1 / 2) ^ N, mul_pos τ.2.1 (by positivity),
    mul_le_of_le_one_right τ.2.1.le (pow_le_one₀ (by norm_num) (by norm_num))⟩

theorem halvedRad_anti (τ : Set.Ioo (0 : ℝ) 1) {m n : ℕ} (h : m ≤ n) :
    ((halvedRad τ n : Set.Ioc (0 : ℝ) τ) : ℝ) ≤ halvedRad τ m :=
  mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) h) τ.2.1.le

theorem exists_halvedRad_le (τ : Set.Ioo (0 : ℝ) 1) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ N : ℕ, ((halvedRad τ N : Set.Ioc (0 : ℝ) τ) : ℝ) ≤ ρ := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < ρ / τ from div_pos hρ τ.2.1)
    (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N, ?_⟩
  change (τ : ℝ) * (1 / 2) ^ N ≤ ρ
  rw [lt_div_iff₀ τ.2.1] at hN
  linarith

end TeichFrob

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

theorem gaussNorm_sum_range_sub_le (f : ℕ → T.B) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hf : ∀ n, ConvergesAt (T.coeffB (f n)) ρ) {δ : ℝ} (hδ : 0 ≤ δ) {N0 : ℕ}
    (h : ∀ n, N0 ≤ n → gaussNorm (T.coeffB (f n)) ρ ≤ δ) (m n : ℕ) (hm : N0 ≤ m) (hn : N0 ≤ n) :
    gaussNorm (T.coeffB (∑ k ∈ Finset.range m, f k - ∑ k ∈ Finset.range n, f k)) ρ ≤ δ := by
  rcases le_total n m with hnm | hmn
  · rw [← Finset.sum_Ico_eq_sub _ hnm]
    exact (T.gaussNorm_finsetSum_le _ f hρ0 hρ1 hδ fun k hk =>
      ⟨hf k, h k (hn.trans (Finset.mem_Ico.1 hk).1)⟩).2
  · rw [← neg_sub, ← Finset.sum_Ico_eq_sub _ hmn]
    obtain ⟨h1, h2⟩ := T.gaussNorm_finsetSum_le (Finset.Ico m n) f hρ0 hρ1 hδ fun k hk =>
      ⟨hf k, h k (hm.trans (Finset.mem_Ico.1 hk).1)⟩
    rw [(T.convergesAt_coeffB_neg hρ0 hρ1 h1).2]; exact h2

namespace TeichFrob

variable (F : T.TeichFrob)

theorem extFrob_sub_ofAll (c : ℕ) (ρ0 : Set.Ioo (0 : ℝ) 1) {b : T.B} (hb : T.ConvAll b) :
    F.extFrob ρ0 (T.ofAll b hb ρ0) -
      T.πExt (F.powRadius ρ0) ^ c * T.res (F.powRadius_le_self ρ0) (T.ofAll b hb ρ0) =
      T.ofAll (F.toB b - algebraMap Γ T.B T.π ^ c * b)
        ((F.convAll_toB hb).sub ((convAll_π_pow c).mul hb)) (F.powRadius ρ0) := by
  rw [F.extFrob_ofAll, res_ofAll, πExt_pow_eq_ofAll, ← ofAll_mul, ← ofAll_sub]

end TeichFrob

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

variable (F : T.TeichFrob)

theorem exists_extFrob_sub_eq [IsAlgClosed L] (ha : 0 < F.a) (c : ℕ) (ρ0 : Set.Ioo (0 : ℝ) 1)
    (y : T.RobbaExt (F.powRadius ρ0)) :
    ∃ x : T.RobbaExt ρ0, F.extFrob ρ0 x -
      T.πExt (F.powRadius ρ0) ^ c * T.res (F.powRadius_le_self ρ0) x = y := by
  have hq := F.two_le_q ha
  have hε : ∀ N : ℕ, (0 : ℝ) < (1 / 2) ^ N := fun N => by positivity
  choose t d R ht hR hd heq hnear hbd using
    fun (z : T.RobbaExt (F.powRadius ρ0)) (N : ℕ) =>
      F.exists_step ha c z (halvedRad (F.powRadius ρ0) N) (hε N)
  obtain ⟨zs, hz0, hzs⟩ : ∃ zs : ℕ → T.RobbaExt (F.powRadius ρ0), zs 0 = y ∧ ∀ N, zs (N + 1) =
      zs N - T.ofAll (d (zs N) N - R (zs N) N) ((hd _ N).sub (hR _ N)) (F.powRadius ρ0) :=
    ⟨fun N => Nat.rec y (fun N zN =>
      zN - T.ofAll (d zN N - R zN N) ((hd zN N).sub (hR zN N)) (F.powRadius ρ0)) N,
      rfl, fun N => rfl⟩

  have hA : ∀ (N : ℕ) (ρ : Set.Ioc (0 : ℝ) (F.powRadius ρ0)),
      ((halvedRad (F.powRadius ρ0) N : Set.Ioc (0 : ℝ) _) : ℝ) ≤ ρ →
      T.extNorm _ ρ (zs (N + 1)) ≤ (1 / 2) ^ N := by
    intro N ρ hρ
    have e : zs (N + 1) = (zs N - T.ofAll (d (zs N) N) (hd _ N) (F.powRadius ρ0)) +
        T.ofAll (R (zs N) N) (hR _ N) (F.powRadius ρ0) := by
      rw [hzs N, ofAll_sub (hd _ N) (hR _ N)]; ring
    rw [e]
    refine (T.extNorm_add_le ρ _ _).trans (max_le (hnear _ N ρ hρ).1 ?_)
    rw [extNorm_ofAll]; exact (hnear _ N ρ hρ).2
  have hB : ∀ (N : ℕ) (ρ : Set.Ioc (0 : ℝ) (F.powRadius ρ0)),
      ((halvedRad (F.powRadius ρ0) N : Set.Ioc (0 : ℝ) _) : ℝ) ≤ ρ →
      gaussNorm (T.coeffB (d (zs (N + 1)) (N + 1))) ρ ≤ (1 / 2) ^ N ∧
        gaussNorm (T.coeffB (R (zs (N + 1)) (N + 1))) ρ ≤ (1 / 2) ^ N := by
    intro N ρ hρ
    have hρ' : ((halvedRad (F.powRadius ρ0) (N + 1) : Set.Ioc (0 : ℝ) _) : ℝ) ≤ ρ :=
      (halvedRad_anti _ (Nat.le_succ N)).trans hρ
    have hhalf : ((1 : ℝ) / 2) ^ (N + 1) ≤ (1 / 2) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ N)
    refine ⟨?_, (hnear _ (N + 1) ρ hρ').2.trans hhalf⟩
    rw [← extNorm_ofAll (hd _ (N + 1))]
    have e : T.ofAll (d (zs (N + 1)) (N + 1)) (hd _ (N + 1)) (F.powRadius ρ0) =
        zs (N + 1) + -(zs (N + 1) - T.ofAll (d (zs (N + 1)) (N + 1)) (hd _ (N + 1))
          (F.powRadius ρ0)) := by ring
    rw [e]
    refine (T.extNorm_add_le ρ _ _).trans (max_le (hA N ρ hρ) ?_)
    rw [extNorm_neg]
    exact (hnear _ (N + 1) ρ hρ').1.trans hhalf

  have hE : ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 → ∀ δ > 0, ∃ N0 : ℕ, ∀ n, N0 ≤ n →
      gaussNorm (T.coeffB (t (zs n) n)) ρ ≤ δ := by
    intro ρ hρ0 hρρ0 δ hδ
    have hρ1 : ρ < 1 := lt_of_le_of_lt hρρ0 ρ0.2.2
    set σ' := ρ ^ p ^ F.a
    have hσ'0 : 0 < σ' := pow_pos hρ0 _
    have hσ'1 : σ' < 1 := pow_lt_one₀ hρ0.le hρ1 F.q_pos.ne'
    have hσ'τ : σ' ≤ (F.powRadius ρ0 : ℝ) := pow_le_pow_left₀ hρ0.le hρρ0 _
    let σr : Set.Ioc (0 : ℝ) (F.powRadius ρ0) := ⟨σ', hσ'0, hσ'τ⟩
    set A := max (max 2 (fwdConst (p ^ F.a) c σ' * σ' ^ (-(c : ℤ)))) 1
    have hA1 : 1 ≤ A := le_max_right _ _
    obtain ⟨N1, hN1⟩ := exists_halvedRad_le (F.powRadius ρ0) hσ'0
    obtain ⟨N2, hN2⟩ : ∃ N2 : ℕ, A * (1 / 2 : ℝ) ^ N2 ≤ δ ^ p ^ F.a := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul A
      rw [mul_zero] at this
      exact (this.eventually (ge_mem_nhds (pow_pos hδ _))).exists
    refine ⟨max N1 N2 + 1, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm1 : ((halvedRad (F.powRadius ρ0) m : Set.Ioc (0 : ℝ) _) : ℝ) ≤ σ' :=
      (halvedRad_anti _ (show N1 ≤ m by omega)).trans hN1
    obtain ⟨hdm, hRm⟩ := hB m σr hm1
    have hhalf : ((1 : ℝ) / 2) ^ m ≤ (1 / 2) ^ N2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (show N2 ≤ m by omega)
    set tn := t (zs (m + 1)) (m + 1)
    set dn := d (zs (m + 1)) (m + 1)
    set Rn := R (zs (m + 1)) (m + 1)
    have htn : gaussNorm (T.coeffB tn) σ' ≤ A * (1 / 2) ^ m :=
      (hbd _ (m + 1) σ' hσ'0 hσ'1).trans (mul_le_mul (le_max_left _ _) hdm
        (gaussNorm_nonneg hσ'0) (zero_le_one.trans hA1))
    have hkey : F.toB tn = algebraMap Γ T.B T.π ^ c * tn + (dn - Rn) := by
      rw [← heq]; ring
    have htc := ht (zs (m + 1)) (m + 1) σ' hσ'0 hσ'1
    obtain ⟨hp1, hp2⟩ := gaussNorm_π_pow (T := T) c hσ'0
    obtain ⟨hm1c, hm1n⟩ := T.convergesAt_coeffB_mul hσ'0 hσ'1 hp1 htc
    have hdc := hd (zs (m + 1)) (m + 1) σ' hσ'0 hσ'1
    have hRc := hR (zs (m + 1)) (m + 1) σ' hσ'0 hσ'1
    obtain ⟨hsc, hsn⟩ := T.convergesAt_coeffB_add hσ'0 hσ'1 hdc
      (T.convergesAt_coeffB_neg hσ'0 hσ'1 hRc).1
    rw [(T.convergesAt_coeffB_neg hσ'0 hσ'1 hRc).2, ← sub_eq_add_neg] at hsn
    rw [← sub_eq_add_neg] at hsc
    have hphi : gaussNorm (T.coeffB (F.toB tn)) σ' ≤ A * (1 / 2) ^ m := by
      rw [hkey]
      refine (T.convergesAt_coeffB_add hσ'0 hσ'1 hm1c hsc).2.trans (max_le ?_ ?_)
      · rw [hm1n, hp2]
        exact (mul_le_of_le_one_left (gaussNorm_nonneg hσ'0)
          (pow_le_one₀ hσ'0.le hσ'1.le)).trans htn
      · exact hsn.trans (max_le (hdm.trans (le_mul_of_one_le_left (by positivity) hA1))
          (hRm.trans (le_mul_of_one_le_left (by positivity) hA1)))
    rw [F.gaussNorm_coeffB_toB hρ0 hρ1 (ht _ (m + 1) ρ hρ0 hρ1)] at hphi
    have := hphi.trans ((mul_le_mul_of_nonneg_left hhalf (zero_le_one.trans hA1)).trans hN2)
    exact (pow_le_pow_iff_left₀ (gaussNorm_nonneg hρ0) hδ.le F.q_pos.ne').1 this

  have hxs : ∀ N, T.ConvAll (∑ n ∈ Finset.range N, t (zs n) n) := fun N =>
    convAll_sum _ _ fun n _ => ht (zs n) n
  obtain ⟨x, hx⟩ := exists_tendsto_of_gaussNorm (T := T) (σ := ρ0)
    (fun N => ⟨∑ n ∈ Finset.range N, t (zs n) n, hxs N ρ0 ρ0.2.1 ρ0.2.2⟩) fun ρ ε hε => by
      obtain ⟨N0, hN0⟩ := hE ρ ρ.2.1 ρ.2.2 (ε / 2) (half_pos hε)
      refine ⟨N0, fun m hm n hn => lt_of_le_of_lt ?_ (half_lt_self hε)⟩
      exact gaussNorm_sum_range_sub_le (fun k => t (zs k) k) ρ.2.1 (rad_lt_one ρ0 ρ)
        (fun k => ht (zs k) k ρ ρ.2.1 (rad_lt_one ρ0 ρ)) (half_pos hε).le hN0 m n hm hn
  refine ⟨x, ?_⟩

  have hH : ∀ N, F.extFrob ρ0 (T.ofAll _ (hxs N) ρ0) - T.πExt (F.powRadius ρ0) ^ c *
      T.res (F.powRadius_le_self ρ0) (T.ofAll _ (hxs N) ρ0) = y - zs N := by
    intro N
    induction N with
    | zero =>
      rw [hz0, sub_self, ofAll_congr (hxs 0) convAll_zero (by simp)]
      rw [F.extFrob_sub_ofAll, ofAll_congr _ convAll_zero (by simp)]
      simp only [ofAll]
      exact Completion.coe_zero
    | succ N ih =>
      rw [ofAll_congr (hxs (N + 1)) ((hxs N).add (ht (zs N) N)) (Finset.sum_range_succ _ _),
        ofAll_add (hxs N) (ht (zs N) N), map_add, map_add, mul_add, add_sub_add_comm, ih,
        F.extFrob_sub_ofAll,
        ofAll_congr _ ((hd _ N).sub (hR _ N)) (heq _ N), hzs N]
      ring

  set E : T.RobbaExt ρ0 → T.RobbaExt (F.powRadius ρ0) := fun w =>
    F.extFrob ρ0 w - T.πExt (F.powRadius ρ0) ^ c * T.res (F.powRadius_le_self ρ0) w
  have hEc : Continuous E :=
    (F.continuous_extFrob ρ0).sub (continuous_const.mul (T.continuous_res _))
  have hlim : Tendsto (fun N => E (T.ofAll _ (hxs N) ρ0)) atTop (𝓝 (E x)) :=
    (hEc.tendsto x).comp hx
  have hzero : ∀ ρ : Set.Ioc (0 : ℝ) (F.powRadius ρ0), T.extNorm _ ρ (E x - y) = 0 := by
    intro ρ
    have h1 : Tendsto (fun N => T.extNorm _ ρ (E (T.ofAll _ (hxs N) ρ0) - y)) atTop
        (𝓝 (T.extNorm _ ρ (E x - y))) :=
      ((T.continuous_extNorm ρ).tendsto _).comp (hlim.sub_const y)
    have h2 : Tendsto (fun N => T.extNorm _ ρ (E (T.ofAll _ (hxs N) ρ0) - y)) atTop (𝓝 0) := by
      obtain ⟨N1, hN1⟩ := exists_halvedRad_le (F.powRadius ρ0) ρ.2.1
      have hle : ∀ N, N1 ≤ N → T.extNorm _ ρ (E (T.ofAll _ (hxs (N + 1)) ρ0) - y) ≤
          (1 / 2) ^ N := fun N hN => by
        change T.extNorm _ ρ ((F.extFrob ρ0 (T.ofAll _ (hxs (N + 1)) ρ0) -
          T.πExt (F.powRadius ρ0) ^ c * T.res (F.powRadius_le_self ρ0)
            (T.ofAll _ (hxs (N + 1)) ρ0)) - y) ≤ _
        rw [hH, sub_sub_cancel_left, extNorm_neg]
        exact hA N ρ ((halvedRad_anti _ hN).trans hN1)
      rw [← tendsto_add_atTop_iff_nat 1]
      refine squeeze_zero' (Eventually.of_forall fun N => T.extNorm_nonneg ρ _)
        (eventually_atTop.2 ⟨N1, hle⟩) ?_
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact tendsto_nhds_unique h1 h2
  exact sub_eq_zero.1 (T.eq_zero_of_forall_extNorm_eq_zero hzero)

end TeichFrob

end TeichLift

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

variable (T) in

def πTilde : T.RobbaTilde := T.edagToTilde ⟨algebraMap Γ T.B T.π, T.Econ_le_Edag ⟨1 / 2, by norm_num, by norm_num⟩
  (T.algebraMap_π_mem_Econ _)⟩

theorem ofRad_πExt (ρ1 : Set.Ioo (0 : ℝ) 1) : T.ofRad ρ1 (T.πExt ρ1) = T.πTilde :=
  (T.edagToTilde_apply (T.algebraMap_π_mem_Econ ρ1)).symm

namespace TeichFrob

variable (F : T.TeichFrob)

theorem tildeFrob_sub_surjective [IsAlgClosed L] (ha : 0 < F.a) (c : ℕ) (y : T.RobbaTilde) :
    ∃ x : T.RobbaTilde, F.tildeFrob x - T.πTilde ^ c * x = y := by
  obtain ⟨σ, y0, rfl⟩ := T.exists_ofRad y
  have h : ((F.powRadius (F.rootRadius σ) : Set.Ioo (0 : ℝ) 1) : ℝ) ≤ σ := by
    rw [F.powRadius_rootRadius]
  obtain ⟨x0, hx0⟩ := F.exists_extFrob_sub_eq ha c (F.rootRadius σ) (T.res h y0)
  refine ⟨T.ofRad (F.rootRadius σ) x0, ?_⟩
  rw [F.tildeFrob_ofRad, ← T.ofRad_res (F.powRadius_le_self (F.rootRadius σ)) x0,
    ← ofRad_πExt (F.powRadius (F.rootRadius σ)), ← map_pow, ← map_mul, ← map_sub, hx0,
    T.ofRad_res]

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
