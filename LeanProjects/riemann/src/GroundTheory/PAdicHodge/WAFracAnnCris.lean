import Mathlib
import GroundTheory.PAdicHodge.WAFracAnn
import GroundTheory.PAdicHodge.WAPeriodT
import GroundTheory.PAdicHodge.BCrisNewtonApprox
import GroundTheory.PAdicHodge.ACrisGalois
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Laurent Filter Topology UniformSpace

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
  {ρ0 : Set.Ioo (0 : ℝ) 1} {σ0 : Set.Ioc (0 : ℝ) ρ0}

def annNormR (x : T.Ann ρ0 σ0) (s : ℝ) : ℝ :=
  if h : s ∈ Set.Icc (σ0 : ℝ) ρ0 then T.annNorm ρ0 σ0 ⟨s, h⟩ x else 0

theorem annNormR_of_mem (x : T.Ann ρ0 σ0) (r : AnnRad ρ0 σ0) :
    T.annNormR x r = T.annNorm ρ0 σ0 r x := by
  rw [annNormR, dif_pos r.2]

theorem continuousOn_gaussNorm_coreVal (b : T.AnnCore ρ0 σ0) :
    ContinuousOn (gaussNorm (T.coeffB (T.coreVal ρ0 σ0 b))) (Set.Icc (σ0 : ℝ) ρ0) := by
  by_cases hb : T.coeffB (T.coreVal ρ0 σ0 b) = 0
  · rw [hb]
    have : gaussNorm (0 : ℤ → L) = fun _ => 0 := by funext s; simp [gaussNorm]
    rw [this]; exact continuousOn_const
  exact continuousOn_gaussNorm σ0.2.1 (T.convergesAt_coreVal b (annIn ρ0 σ0))
    (T.convergesAt_coreVal b (annOut ρ0 σ0)) hb

theorem continuousOn_annNormR (x : T.Ann ρ0 σ0) :
    ContinuousOn (T.annNormR x) (Set.Icc (σ0 : ℝ) ρ0) := by
  intro s hs
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨b, hb⟩ := T.exists_coeAnn_near x (show 0 < ε / 3 by positivity)
  have hc := T.continuousOn_gaussNorm_coreVal (T.coreOf ρ0 σ0 b) s hs
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 hc (ε / 3) (by positivity)
  refine ⟨δ, hδ, fun {s'} hs' hd => ?_⟩
  have key : ∀ r : AnnRad ρ0 σ0, |T.annNorm ρ0 σ0 r x -
      gaussNorm (T.coeffB (T.coreVal ρ0 σ0 (T.coreOf ρ0 σ0 b))) r| < ε / 3 := by
    intro r
    rw [← annNorm_coe, ← coeAnn_apply]
    have h1 := T.annNorm_sub_le r x (x - T.coeAnn b)
    have h2 := T.annNorm_add_le r (x - T.coeAnn b) (T.coeAnn b)
    rw [sub_sub_cancel] at h1
    rw [sub_add_cancel] at h2
    have h3 := hb r
    rw [abs_sub_lt_iff]
    constructor
    · rcases le_max_iff.1 h2 with h | h
      · linarith [T.annNorm_nonneg r (T.coeAnn b)]
      · linarith [T.annNorm_nonneg r (x - T.coeAnn b)]
    · rcases le_max_iff.1 h1 with h | h
      · linarith [T.annNorm_nonneg r x]
      · linarith [T.annNorm_nonneg r x]
  have k1 := key ⟨s', hs'⟩
  have k2 := key ⟨s, hs⟩
  have k3 := hδc hs' hd
  rw [Real.dist_eq] at k3 ⊢
  rw [annNormR_of_mem T x ⟨s', hs'⟩, annNormR_of_mem T x ⟨s, hs⟩]
  set A := T.annNorm ρ0 σ0 ⟨s', hs'⟩ x
  set D := T.annNorm ρ0 σ0 ⟨s, hs⟩ x
  set B := gaussNorm (T.coeffB (T.coreVal ρ0 σ0 (T.coreOf ρ0 σ0 b))) s'
  set C := gaussNorm (T.coeffB (T.coreVal ρ0 σ0 (T.coreOf ρ0 σ0 b))) s
  have e1 := abs_sub_le A B D
  have e2 := abs_sub_le B C D
  have e3 : |C - D| < ε / 3 := by rw [abs_sub_comm]; exact k2
  linarith

theorem annNorm_pos_of_annIn_pos {x : T.Ann ρ0 σ0} (hx : 0 < T.annNorm ρ0 σ0 (annIn ρ0 σ0) x)
    (r : AnnRad ρ0 σ0) : 0 < T.annNorm ρ0 σ0 r x := by
  refine lt_of_le_of_ne (T.annNorm_nonneg r x) fun h0 => ?_
  rcases eq_or_lt_of_le r.2.1 with hr | hr
  · have : r = annIn ρ0 σ0 := Subtype.ext hr.symm
    rw [this] at h0; linarith

  have hzero : ∀ s ∈ Set.Ioo (σ0 : ℝ) r, T.annNormR x s = 0 := by
    intro s hs
    have hsI : s ∈ Set.Icc (σ0 : ℝ) ρ0 := ⟨hs.1.le, hs.2.le.trans r.2.2⟩
    obtain ⟨t, ht0, ht1, hst⟩ := exists_interp_exponent σ0.2.1 hs.1 hs.2
    have := T.annNorm_interp_le (annIn ρ0 σ0) r ⟨s, hsI⟩ ht0.le ht1.le hst x
    rw [← h0, Real.zero_rpow ht0.ne', mul_zero] at this
    rw [annNormR_of_mem T x ⟨s, hsI⟩]
    exact le_antisymm this (T.annNorm_nonneg _ x)

  have hc : ContinuousWithinAt (T.annNormR x) (Set.Ioo (σ0 : ℝ) r) σ0 :=
    (T.continuousOn_annNormR x σ0 ⟨le_rfl, σ0.2.2⟩).mono fun s hs => ⟨hs.1.le, hs.2.le.trans r.2.2⟩
  have hmem : (σ0 : ℝ) ∈ closure (Set.Ioo (σ0 : ℝ) r) := by
    rw [closure_Ioo hr.ne]; exact ⟨le_rfl, hr.le⟩
  have hlim := hc.mem_closure_image hmem
  have hsub : T.annNormR x '' Set.Ioo (σ0 : ℝ) r ⊆ {0} := by
    rintro _ ⟨s, hs, rfl⟩; exact hzero s hs
  have := closure_mono hsub hlim
  have h' : T.annNormR x (σ0 : ℝ) = T.annNorm ρ0 σ0 (annIn ρ0 σ0) x := T.annNormR_of_mem x (annIn ρ0 σ0)
  rw [closure_singleton, Set.mem_singleton_iff, h'] at this
  linarith

end TeichLift

namespace WAFrac

open _root_.WittVector WittTilt WAEval TeichLift PhiGamma ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)

variable (ρ0 : Set.Ioo (0 : ℝ) 1) (σ0 : Set.Ioc (0 : ℝ) ρ0)

def awayToAnn : 𝔸 →+* (𝓣).Ann ρ0 σ0 := (𝓣).coeAnn.comp (awayToEcon p ρ0)

variable {ρ0 σ0}

theorem annNorm_awayToAnn (r : AnnRad ρ0 σ0) (z : 𝔸) :
    (𝓣).annNorm ρ0 σ0 r (awayToAnn ρ0 σ0 z) = gn ℂ_[p] p r z :=
  (𝓣).annNorm_coeAnn r _

theorem awayToAnn_eq_toAnn (z : 𝔸) : awayToAnn ρ0 σ0 z = (𝓣).toAnn ρ0 σ0 (awayToExt p ρ0 z) :=
  ((𝓣).toAnn_coe _).symm

theorem rad_pos' (r : AnnRad ρ0 σ0) : (0 : ℝ) < r := σ0.2.1.trans_le r.2.1

theorem rad_lt_one' (r : AnnRad ρ0 σ0) : (r : ℝ) < 1 := r.2.2.trans_lt ρ0.2.2

theorem annNorm_awayToAnn_natCast_p (r : AnnRad ρ0 σ0) :
    (𝓣).annNorm ρ0 σ0 r (p : (𝓣).Ann ρ0 σ0) = r := by
  rw [← map_natCast (awayToAnn ρ0 σ0) p, annNorm_awayToAnn]
  exact gn_natCast_p (rad_pos' r)

theorem isUnit_natCast_p_ann : IsUnit (p : (𝓣).Ann ρ0 σ0) := by
  have h : IsUnit (p : 𝔸) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := 𝔸) (p : AInf ℂ_[p] p)
    rwa [map_natCast] at this
  have := h.map (awayToAnn ρ0 σ0)
  rwa [map_natCast] at this

variable (hσ : (p : ℝ)⁻¹ ≤ σ0)
include hσ

theorem norm_p_le_rad (r : AnnRad ρ0 σ0) : ‖(p : ℂ_[p])‖ ≤ r := by
  rw [norm_natCast_p]; exact hσ.trans r.2.1

theorem annNorm_awayToAnn_le_one (r : AnnRad ρ0 σ0) {z : 𝔸} (hz : z ∈ ACrisZero ℂ_[p] p) :
    (𝓣).annNorm ρ0 σ0 r (awayToAnn ρ0 σ0 z) ≤ 1 := by
  rw [annNorm_awayToAnn]
  exact gn_acrisZero_le_one (norm_p_le_rad hσ r) (rad_pos' r) (rad_lt_one' r) hz

theorem annNorm_awayToAnn_sub_le (r : AnnRad ρ0 σ0) {c₁ c₂ : ACrisZero ℂ_[p] p} {N : ℕ}
    (h : algebraMap _ (ACris ℂ_[p] p) c₁ - algebraMap _ (ACris ℂ_[p] p) c₂ ∈
      Ideal.span {(p : ACris ℂ_[p] p) ^ N}) :
    (𝓣).annNorm ρ0 σ0 r (awayToAnn ρ0 σ0 (c₁ : 𝔸) - awayToAnn ρ0 σ0 (c₂ : 𝔸)) ≤ (r : ℝ) ^ N := by
  rw [← map_sub, annNorm_awayToAnn]
  exact gn_sub_le_of_mem (norm_p_le_rad hσ r) (rad_lt_one' r) h

omit hσ in

def acrisApprox (a : ACris ℂ_[p] p) (N : ℕ) : ACrisZero ℂ_[p] p := (exists_approx a N).choose

omit hσ in
theorem acrisApprox_spec (a : ACris ℂ_[p] p) (N : ℕ) :
    a - algebraMap _ (ACris ℂ_[p] p) (acrisApprox a N) ∈ Ideal.span {(p : ACris ℂ_[p] p) ^ N} :=
  (exists_approx a N).choose_spec

omit hσ in
theorem sub_mem_span_of_le {a : ACris ℂ_[p] p} {c₁ c₂ : ACrisZero ℂ_[p] p} {M N : ℕ} (hMN : M ≤ N)
    (h₁ : a - algebraMap _ (ACris ℂ_[p] p) c₁ ∈ Ideal.span {(p : ACris ℂ_[p] p) ^ M})
    (h₂ : a - algebraMap _ (ACris ℂ_[p] p) c₂ ∈ Ideal.span {(p : ACris ℂ_[p] p) ^ N}) :
    algebraMap _ (ACris ℂ_[p] p) c₂ - algebraMap _ (ACris ℂ_[p] p) c₁ ∈
      Ideal.span {(p : ACris ℂ_[p] p) ^ M} := by
  have h₂' : a - algebraMap _ (ACris ℂ_[p] p) c₂ ∈ Ideal.span {(p : ACris ℂ_[p] p) ^ M} :=
    Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hMN) h₂
  have := sub_mem h₁ h₂'
  rwa [sub_sub_sub_cancel_left] at this

theorem rad_pow_le (r : AnnRad ρ0 σ0) (N : ℕ) : (r : ℝ) ^ N ≤ (ρ0 : ℝ) ^ N :=
  pow_le_pow_left₀ (rad_pos' r).le r.2.2 N

theorem exists_acrisLimit (a : ACris ℂ_[p] p) :
    ∃ x : (𝓣).Ann ρ0 σ0, ∀ r : AnnRad ρ0 σ0,
      Tendsto (fun N => (𝓣).annNorm ρ0 σ0 r (awayToAnn ρ0 σ0 (acrisApprox a N : 𝔸) - x)) atTop (𝓝 0) := by
  refine (𝓣).exists_limit_ann fun ε hε => ?_
  obtain ⟨J₀, hJ₀⟩ := exists_pow_lt_of_lt_one hε ρ0.2.2
  have key : ∀ r : AnnRad ρ0 σ0, ∀ J ≥ J₀, ∀ K ≥ J₀, (𝓣).annNorm ρ0 σ0 r
      (awayToAnn ρ0 σ0 (acrisApprox a J : 𝔸) - awayToAnn ρ0 σ0 (acrisApprox a K : 𝔸)) ≤ ε := by
    intro r J hJ K hK
    have hle : ∀ M N, M ≤ N → (𝓣).annNorm ρ0 σ0 r
        (awayToAnn ρ0 σ0 (acrisApprox a N : 𝔸) - awayToAnn ρ0 σ0 (acrisApprox a M : 𝔸)) ≤
          (r : ℝ) ^ M := fun M N hMN =>
      annNorm_awayToAnn_sub_le hσ r (sub_mem_span_of_le hMN (acrisApprox_spec a M) (acrisApprox_spec a N))
    have hJ' : (r : ℝ) ^ J₀ ≤ ε := ((rad_pow_le hσ r J₀).trans hJ₀.le)
    rcases le_total J K with h | h
    · rw [(𝓣).annNorm_sub_comm]
      exact (hle J K h).trans ((pow_le_pow_of_le_one (rad_pos' r).le (rad_lt_one' r).le hJ).trans hJ')
    · exact (hle K J h).trans ((pow_le_pow_of_le_one (rad_pos' r).le (rad_lt_one' r).le hK).trans hJ')
  exact ⟨J₀, fun J hJ K hK => ⟨key _ J hJ K hK, key _ J hJ K hK⟩⟩

def acrisToAnnFun (a : ACris ℂ_[p] p) : (𝓣).Ann ρ0 σ0 := (exists_acrisLimit hσ a).choose

theorem annNorm_acrisToAnnFun_sub_le (a : ACris ℂ_[p] p) {c : ACrisZero ℂ_[p] p} {N : ℕ}
    (hc : a - algebraMap _ (ACris ℂ_[p] p) c ∈ Ideal.span {(p : ACris ℂ_[p] p) ^ N})
    (r : AnnRad ρ0 σ0) :
    (𝓣).annNorm ρ0 σ0 r (acrisToAnnFun hσ a - awayToAnn ρ0 σ0 (c : 𝔸)) ≤ (r : ℝ) ^ N := by
  set x := acrisToAnnFun hσ a
  have hx := (exists_acrisLimit hσ a).choose_spec r
  have hbound : ∀ J ≥ N, (𝓣).annNorm ρ0 σ0 r (x - awayToAnn ρ0 σ0 (c : 𝔸)) ≤
      max ((𝓣).annNorm ρ0 σ0 r (awayToAnn ρ0 σ0 (acrisApprox a J : 𝔸) - x)) ((r : ℝ) ^ N) := by
    intro J hJ
    have e : x - awayToAnn ρ0 σ0 (c : 𝔸) = -(awayToAnn ρ0 σ0 (acrisApprox a J : 𝔸) - x) +
        (awayToAnn ρ0 σ0 (acrisApprox a J : 𝔸) - awayToAnn ρ0 σ0 (c : 𝔸)) := by ring
    rw [e]
    refine ((𝓣).annNorm_add_le r _ _).trans (max_le_max (by rw [(𝓣).annNorm_neg]) ?_)
    exact annNorm_awayToAnn_sub_le hσ r (sub_mem_span_of_le hJ hc (acrisApprox_spec a J))
  have hlim : Tendsto (fun J => max ((𝓣).annNorm ρ0 σ0 r (awayToAnn ρ0 σ0 (acrisApprox a J : 𝔸) - x))
      ((r : ℝ) ^ N)) atTop (𝓝 (max 0 ((r : ℝ) ^ N))) := hx.max tendsto_const_nhds
  rw [max_eq_right (pow_nonneg (rad_pos' r).le N)] at hlim
  exact ge_of_tendsto hlim (eventually_atTop.2 ⟨N, hbound⟩)

theorem annNorm_acrisToAnnFun_le_one (a : ACris ℂ_[p] p) (r : AnnRad ρ0 σ0) :
    (𝓣).annNorm ρ0 σ0 r (acrisToAnnFun hσ a) ≤ 1 := by
  have h1 := annNorm_acrisToAnnFun_sub_le hσ a (acrisApprox_spec a 0) r
  have e : acrisToAnnFun hσ a = (acrisToAnnFun hσ a - awayToAnn ρ0 σ0 (acrisApprox a 0 : 𝔸)) +
      awayToAnn ρ0 σ0 (acrisApprox a 0 : 𝔸) := by ring
  rw [e]
  refine ((𝓣).annNorm_add_le r _ _).trans (max_le (h1.trans (by rw [pow_zero])) ?_)
  exact annNorm_awayToAnn_le_one hσ r (acrisApprox a 0).2

theorem eq_acrisToAnnFun {a : ACris ℂ_[p] p} {x : (𝓣).Ann ρ0 σ0}
    (h : ∀ N : ℕ, ∃ c : ACrisZero ℂ_[p] p,
      a - algebraMap _ (ACris ℂ_[p] p) c ∈ Ideal.span {(p : ACris ℂ_[p] p) ^ N} ∧
      ∀ r : AnnRad ρ0 σ0, (𝓣).annNorm ρ0 σ0 r (x - awayToAnn ρ0 σ0 (c : 𝔸)) ≤ (ρ0 : ℝ) ^ N) :
    x = acrisToAnnFun hσ a := by
  have key : ∀ r : AnnRad ρ0 σ0, (𝓣).annNorm ρ0 σ0 r (x - acrisToAnnFun hσ a) = 0 := by
    intro r
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) ((𝓣).annNorm_nonneg r _)
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε ρ0.2.2
    obtain ⟨c, hc, hx⟩ := h N
    have e : x - acrisToAnnFun hσ a = (x - awayToAnn ρ0 σ0 (c : 𝔸)) +
        -(acrisToAnnFun hσ a - awayToAnn ρ0 σ0 (c : 𝔸)) := by ring
    rw [e, zero_add]
    refine ((𝓣).annNorm_add_le r _ _).trans (max_le ((hx r).trans hN.le) ?_)
    rw [(𝓣).annNorm_neg]
    exact (annNorm_acrisToAnnFun_sub_le hσ a hc r).trans ((rad_pow_le hσ r N).trans hN.le)
  exact (𝓣).eq_of_annNorm_sub (key _) (key _)

theorem acrisToAnnFun_algebraMap (c : ACrisZero ℂ_[p] p) :
    acrisToAnnFun hσ (algebraMap _ (ACris ℂ_[p] p) c) = awayToAnn ρ0 σ0 (c : 𝔸) :=
  (eq_acrisToAnnFun hσ fun N => ⟨c, by rw [sub_self]; exact Ideal.zero_mem _, fun r => by
    rw [sub_self, (𝓣).annNorm_zero]; exact pow_nonneg ρ0.2.1.le N⟩).symm

def acrisToAnn : ACris ℂ_[p] p →+* (𝓣).Ann ρ0 σ0 where
  toFun := acrisToAnnFun hσ
  map_one' := by
    have := acrisToAnnFun_algebraMap hσ 1
    rwa [map_one, OneMemClass.coe_one, map_one] at this
  map_zero' := by
    have := acrisToAnnFun_algebraMap hσ 0
    rwa [map_zero, ZeroMemClass.coe_zero, map_zero] at this
  map_add' a b := by
    refine (eq_acrisToAnnFun hσ fun N => ⟨acrisApprox a N + acrisApprox b N, ?_, fun r => ?_⟩).symm
    · rw [map_add, add_sub_add_comm]
      exact add_mem (acrisApprox_spec a N) (acrisApprox_spec b N)
    · have e : acrisToAnnFun hσ a + acrisToAnnFun hσ b -
          awayToAnn ρ0 σ0 ((acrisApprox a N + acrisApprox b N : ACrisZero ℂ_[p] p) : 𝔸) =
          (acrisToAnnFun hσ a - awayToAnn ρ0 σ0 (acrisApprox a N : 𝔸)) +
            (acrisToAnnFun hσ b - awayToAnn ρ0 σ0 (acrisApprox b N : 𝔸)) := by
        rw [Subalgebra.coe_add, map_add]; ring
      rw [e]
      exact ((𝓣).annNorm_add_le r _ _).trans (max_le
        ((annNorm_acrisToAnnFun_sub_le hσ a (acrisApprox_spec a N) r).trans (rad_pow_le hσ r N))
        ((annNorm_acrisToAnnFun_sub_le hσ b (acrisApprox_spec b N) r).trans (rad_pow_le hσ r N)))
  map_mul' a b := by
    refine (eq_acrisToAnnFun hσ fun N => ⟨acrisApprox a N * acrisApprox b N, ?_, fun r => ?_⟩).symm
    · have e : a * b - algebraMap _ (ACris ℂ_[p] p) (acrisApprox a N * acrisApprox b N) =
          a * (b - algebraMap _ (ACris ℂ_[p] p) (acrisApprox b N)) +
            (a - algebraMap _ (ACris ℂ_[p] p) (acrisApprox a N)) *
              algebraMap _ (ACris ℂ_[p] p) (acrisApprox b N) := by
        rw [map_mul]; ring
      rw [e]
      exact add_mem (Ideal.mul_mem_left _ _ (acrisApprox_spec b N))
        (Ideal.mul_mem_right _ _ (acrisApprox_spec a N))
    · have e : acrisToAnnFun hσ a * acrisToAnnFun hσ b -
          awayToAnn ρ0 σ0 ((acrisApprox a N * acrisApprox b N : ACrisZero ℂ_[p] p) : 𝔸) =
          acrisToAnnFun hσ a * (acrisToAnnFun hσ b - awayToAnn ρ0 σ0 (acrisApprox b N : 𝔸)) +
            (acrisToAnnFun hσ a - awayToAnn ρ0 σ0 (acrisApprox a N : 𝔸)) *
              awayToAnn ρ0 σ0 (acrisApprox b N : 𝔸) := by
        rw [Subalgebra.coe_mul, map_mul]; ring
      rw [e]
      refine ((𝓣).annNorm_add_le r _ _).trans (max_le ?_ ?_)
      · rw [(𝓣).annNorm_mul]
        refine (mul_le_of_le_one_left ((𝓣).annNorm_nonneg r _)
          (annNorm_acrisToAnnFun_le_one hσ a r)).trans ?_
        exact (annNorm_acrisToAnnFun_sub_le hσ b (acrisApprox_spec b N) r).trans (rad_pow_le hσ r N)
      · rw [(𝓣).annNorm_mul]
        refine (mul_le_of_le_one_right ((𝓣).annNorm_nonneg r _)
          (annNorm_awayToAnn_le_one hσ r (acrisApprox b N).2)).trans ?_
        exact (annNorm_acrisToAnnFun_sub_le hσ a (acrisApprox_spec a N) r).trans (rad_pow_le hσ r N)

theorem acrisToAnn_apply (a : ACris ℂ_[p] p) : acrisToAnn hσ a = acrisToAnnFun hσ a := rfl

theorem acrisToAnn_algebraMap (c : ACrisZero ℂ_[p] p) :
    acrisToAnn hσ (algebraMap _ (ACris ℂ_[p] p) c) = awayToAnn ρ0 σ0 (c : 𝔸) :=
  acrisToAnnFun_algebraMap hσ c

theorem annNorm_acrisToAnn_sub_le (a : ACris ℂ_[p] p) {c : ACrisZero ℂ_[p] p} {N : ℕ}
    (hc : a - algebraMap _ (ACris ℂ_[p] p) c ∈ Ideal.span {(p : ACris ℂ_[p] p) ^ N})
    (r : AnnRad ρ0 σ0) :
    (𝓣).annNorm ρ0 σ0 r (acrisToAnn hσ a - awayToAnn ρ0 σ0 (c : 𝔸)) ≤ (r : ℝ) ^ N :=
  annNorm_acrisToAnnFun_sub_le hσ a hc r

theorem eq_acrisToAnn {a : ACris ℂ_[p] p} {x : (𝓣).Ann ρ0 σ0}
    (h : ∀ N : ℕ, ∃ c : ACrisZero ℂ_[p] p,
      a - algebraMap _ (ACris ℂ_[p] p) c ∈ Ideal.span {(p : ACris ℂ_[p] p) ^ N} ∧
      ∀ r : AnnRad ρ0 σ0, (𝓣).annNorm ρ0 σ0 r (x - awayToAnn ρ0 σ0 (c : 𝔸)) ≤ (ρ0 : ℝ) ^ N) :
    x = acrisToAnn hσ a :=
  eq_acrisToAnnFun hσ h

theorem isUnit_acrisToAnn_p : IsUnit (acrisToAnn hσ (p : ACris ℂ_[p] p)) := by
  rw [map_natCast]; exact isUnit_natCast_p_ann

def bcrisToAnn : BCrisPlus ℂ_[p] p →+* (𝓣).Ann ρ0 σ0 :=
  IsLocalization.Away.lift (p : ACris ℂ_[p] p) (isUnit_acrisToAnn_p hσ)

theorem bcrisToAnn_algebraMap (a : ACris ℂ_[p] p) :
    bcrisToAnn hσ (algebraMap _ (BCrisPlus ℂ_[p] p) a) = acrisToAnn hσ a :=
  IsLocalization.Away.lift_eq _ _ a

end WAFrac

end GroundTheory.PAdicHodge
