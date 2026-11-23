import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaEigenGlue
import GroundTheory.PAdicHodge.ExtRobbaIsoLift
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace Uniformity

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
  (ρ0 : Set.Ioo (0 : ℝ) 1) (σ0 : Set.Ioc (0 : ℝ) ρ0)

def annSeminorm : RingSeminorm (T.Econ ρ0) where
  toFun b := max (T.gaussSeminorm ρ0 σ0 b) (T.gaussSeminorm ρ0 (topRad ρ0) b)
  map_zero' := by simp
  add_le' a b := max_le
    (((T.gaussSeminorm ρ0 σ0).add_le' a b).trans (add_le_add (le_max_left _ _) (le_max_left _ _)))
    (((T.gaussSeminorm ρ0 (topRad ρ0)).add_le' a b).trans
      (add_le_add (le_max_right _ _) (le_max_right _ _)))
  neg' a := by simp only [map_neg_eq_map]
  mul_le' a b := by
    have h0 : ∀ (f : RingSeminorm (T.Econ ρ0)) (x : T.Econ ρ0), 0 ≤ f x := fun f x => apply_nonneg f x
    refine max_le (((T.gaussSeminorm ρ0 σ0).mul_le' a b).trans ?_)
      (((T.gaussSeminorm ρ0 (topRad ρ0)).mul_le' a b).trans ?_)
    · exact mul_le_mul (le_max_left _ _) (le_max_left _ _) (h0 _ _) ((h0 _ _).trans (le_max_left _ _))
    · exact mul_le_mul (le_max_right _ _) (le_max_right _ _) (h0 _ _) ((h0 _ _).trans (le_max_left _ _))

theorem annSeminorm_apply (b : T.Econ ρ0) :
    T.annSeminorm ρ0 σ0 b = max (gaussNorm (T.coeffB b) σ0) (gaussNorm (T.coeffB b) ρ0) := rfl

abbrev AnnRad := Set.Icc ((σ0 : ℝ)) (ρ0 : ℝ)

variable {ρ0 σ0} in

def annIoc (r : AnnRad ρ0 σ0) : Set.Ioc (0 : ℝ) ρ0 := ⟨r, σ0.2.1.trans_le r.2.1, r.2.2⟩

@[simp] theorem coe_annIoc {r : AnnRad ρ0 σ0} : ((annIoc r : Set.Ioc (0 : ℝ) ρ0) : ℝ) = r := rfl

def annIn : AnnRad ρ0 σ0 := ⟨σ0, le_rfl, σ0.2.2⟩

def annOut : AnnRad ρ0 σ0 := ⟨ρ0, σ0.2.2, le_rfl⟩

@[simp] theorem coe_annIn : ((annIn ρ0 σ0 : AnnRad ρ0 σ0) : ℝ) = σ0 := rfl

@[simp] theorem coe_annOut : ((annOut ρ0 σ0 : AnnRad ρ0 σ0) : ℝ) = ρ0 := rfl

variable {ρ0 σ0} in

theorem gaussNorm_le_annSeminorm (b : T.Econ ρ0) (r : AnnRad ρ0 σ0) :
    gaussNorm (T.coeffB b) r ≤ T.annSeminorm ρ0 σ0 b :=
  gaussNorm_le_max σ0.2.1 r.2.1 r.2.2 (T.convergesAt_rad ρ0 b σ0) (T.convergesAt_rad ρ0 b (topRad ρ0))

@[nolint unusedArguments]
def AnnCore (_σ0 : Set.Ioc (0 : ℝ) ρ0) : Type _ := T.Econ ρ0

instance : CommRing (T.AnnCore ρ0 σ0) := inferInstanceAs (CommRing (T.Econ ρ0))

instance : PseudoMetricSpace (T.AnnCore ρ0 σ0) :=
  (T.annSeminorm ρ0 σ0).toSeminormedRing.toPseudoMetricSpace

instance : IsUniformAddGroup (T.AnnCore ρ0 σ0) :=
  (T.annSeminorm ρ0 σ0).toAddGroupSeminorm.toSeminormedAddCommGroup.to_isUniformAddGroup

instance : IsTopologicalRing (T.AnnCore ρ0 σ0) := by
  have : ContinuousMul (T.AnnCore ρ0 σ0) :=
    @NonUnitalSeminormedRing.toContinuousMul _
      (T.annSeminorm ρ0 σ0).toSeminormedRing.toNonUnitalSeminormedRing
  exact {}

abbrev Ann := UniformSpace.Completion (T.AnnCore ρ0 σ0)

def coreOf : T.Econ ρ0 →+* T.AnnCore ρ0 σ0 := RingHom.id (T.Econ ρ0)

def coreVal (b : T.AnnCore ρ0 σ0) : T.B := ((show T.Econ ρ0 from b) : T.B)

variable {ρ0 σ0}

@[simp] theorem coreVal_coreOf (b : T.Econ ρ0) : T.coreVal ρ0 σ0 (T.coreOf ρ0 σ0 b) = b := rfl

theorem coreVal_sub (a b : T.AnnCore ρ0 σ0) :
    T.coreVal ρ0 σ0 (a - b) = T.coreVal ρ0 σ0 a - T.coreVal ρ0 σ0 b := rfl

theorem coreVal_add (a b : T.AnnCore ρ0 σ0) :
    T.coreVal ρ0 σ0 (a + b) = T.coreVal ρ0 σ0 a + T.coreVal ρ0 σ0 b := rfl

theorem coreVal_mul (a b : T.AnnCore ρ0 σ0) :
    T.coreVal ρ0 σ0 (a * b) = T.coreVal ρ0 σ0 a * T.coreVal ρ0 σ0 b := rfl

theorem coreVal_neg (a : T.AnnCore ρ0 σ0) : T.coreVal ρ0 σ0 (-a) = -T.coreVal ρ0 σ0 a := rfl

theorem coreVal_one : T.coreVal ρ0 σ0 1 = 1 := rfl

theorem coreVal_zero : T.coreVal ρ0 σ0 0 = 0 := rfl

theorem convergesAt_coreVal (b : T.AnnCore ρ0 σ0) (r : AnnRad ρ0 σ0) :
    ConvergesAt (T.coeffB (T.coreVal ρ0 σ0 b)) r :=
  T.convergesAt_rad ρ0 (show T.Econ ρ0 from b) (annIoc r)

theorem dist_annCore (a b : T.AnnCore ρ0 σ0) :
    dist a b = max (gaussNorm (T.coeffB (T.coreVal ρ0 σ0 (a - b))) σ0)
      (gaussNorm (T.coeffB (T.coreVal ρ0 σ0 (a - b))) ρ0) := by
  change T.annSeminorm ρ0 σ0 (-(show T.Econ ρ0 from a) + (show T.Econ ρ0 from b)) = _
  rw [neg_add_eq_sub, ← neg_sub, map_neg_eq_map, annSeminorm_apply]
  rfl

def coeAnn : T.Econ ρ0 →+* T.Ann ρ0 σ0 := (Completion.coeRingHom).comp (T.coreOf ρ0 σ0)

theorem coeAnn_apply (b : T.Econ ρ0) :
    T.coeAnn b = ((T.coreOf ρ0 σ0 b : T.AnnCore ρ0 σ0) : T.Ann ρ0 σ0) := rfl

theorem gaussNorm_coreVal_le (b : T.AnnCore ρ0 σ0) (r : AnnRad ρ0 σ0) :
    gaussNorm (T.coeffB (T.coreVal ρ0 σ0 b)) r ≤
      max (gaussNorm (T.coeffB (T.coreVal ρ0 σ0 b)) σ0) (gaussNorm (T.coeffB (T.coreVal ρ0 σ0 b)) ρ0) :=
  T.gaussNorm_le_annSeminorm (show T.Econ ρ0 from b) r

theorem gaussNorm_coreVal_nonneg (b : T.AnnCore ρ0 σ0) (r : AnnRad ρ0 σ0) :
    0 ≤ gaussNorm (T.coeffB (T.coreVal ρ0 σ0 b)) r :=
  gaussNorm_nonneg (σ0.2.1.trans_le r.2.1)

theorem abs_gaussNorm_sub_le (a b : T.AnnCore ρ0 σ0) (r : AnnRad ρ0 σ0) :
    |gaussNorm (T.coeffB (T.coreVal ρ0 σ0 a)) r - gaussNorm (T.coeffB (T.coreVal ρ0 σ0 b)) r| ≤
      dist a b := by
  have hr0 : (0 : ℝ) < r := σ0.2.1.trans_le r.2.1
  have hr1 : (r : ℝ) < 1 := r.2.2.trans_lt ρ0.2.2
  have key : ∀ x y : T.AnnCore ρ0 σ0, gaussNorm (T.coeffB (T.coreVal ρ0 σ0 x)) r ≤
      gaussNorm (T.coeffB (T.coreVal ρ0 σ0 y)) r + dist x y := by
    intro x y
    have e : T.coreVal ρ0 σ0 x = T.coreVal ρ0 σ0 y + T.coreVal ρ0 σ0 (x - y) := by
      rw [coreVal_sub]; ring
    have h1 := (T.convergesAt_coeffB_add hr0 hr1 (T.convergesAt_coreVal y r)
      (T.convergesAt_coreVal (x - y) r)).2
    rw [← e] at h1
    refine h1.trans ((max_le_add_of_nonneg (T.gaussNorm_coreVal_nonneg _ r)
      (T.gaussNorm_coreVal_nonneg _ r)).trans (add_le_add le_rfl ?_))
    rw [dist_annCore]
    exact T.gaussNorm_coreVal_le (x - y) r
  rw [abs_sub_le_iff]
  constructor
  · linarith [key a b]
  · linarith [key b a, dist_comm a b]

theorem uniformContinuous_gaussNorm_ann (r : AnnRad ρ0 σ0) :
    UniformContinuous (fun b : T.AnnCore ρ0 σ0 => gaussNorm (T.coeffB (T.coreVal ρ0 σ0 b)) r) :=
  LipschitzWith.uniformContinuous (K := 1) (LipschitzWith.of_dist_le_mul fun a b => by
    rw [NNReal.coe_one, one_mul, Real.dist_eq]
    exact T.abs_gaussNorm_sub_le a b r)

variable (ρ0 σ0) in

def annNorm (r : AnnRad ρ0 σ0) (x : T.Ann ρ0 σ0) : ℝ :=
  Completion.extension (fun b : T.AnnCore ρ0 σ0 => gaussNorm (T.coeffB (T.coreVal ρ0 σ0 b)) r) x

theorem annNorm_coe (r : AnnRad ρ0 σ0) (b : T.AnnCore ρ0 σ0) :
    T.annNorm ρ0 σ0 r (b : T.Ann ρ0 σ0) = gaussNorm (T.coeffB (T.coreVal ρ0 σ0 b)) r :=
  Completion.extension_coe (T.uniformContinuous_gaussNorm_ann r) b

theorem annNorm_coeAnn (r : AnnRad ρ0 σ0) (b : T.Econ ρ0) :
    T.annNorm ρ0 σ0 r (T.coeAnn b) = gaussNorm (T.coeffB b) r :=
  T.annNorm_coe r _

theorem continuous_annNorm (r : AnnRad ρ0 σ0) : Continuous (T.annNorm ρ0 σ0 r) :=
  Completion.continuous_extension

theorem annNorm_nonneg (r : AnnRad ρ0 σ0) (x : T.Ann ρ0 σ0) : 0 ≤ T.annNorm ρ0 σ0 r x :=
  Completion.induction_on x (isClosed_le continuous_const (T.continuous_annNorm r))
    fun b => by rw [annNorm_coe]; exact T.gaussNorm_coreVal_nonneg b r

theorem annNorm_mul (r : AnnRad ρ0 σ0) (x y : T.Ann ρ0 σ0) :
    T.annNorm ρ0 σ0 r (x * y) = T.annNorm ρ0 σ0 r x * T.annNorm ρ0 σ0 r y :=
  Completion.induction_on₂ x y
    (isClosed_eq ((T.continuous_annNorm r).comp continuous_mul)
      (((T.continuous_annNorm r).comp continuous_fst).mul ((T.continuous_annNorm r).comp continuous_snd)))
    fun a b => by
      rw [← Completion.coe_mul, annNorm_coe, annNorm_coe, annNorm_coe, coreVal_mul]
      have hr0 : (0 : ℝ) < r := σ0.2.1.trans_le r.2.1
      have hr1 : (r : ℝ) < 1 := r.2.2.trans_lt ρ0.2.2
      exact (T.convergesAt_coeffB_mul hr0 hr1 (T.convergesAt_coreVal a r) (T.convergesAt_coreVal b r)).2

theorem annNorm_add_le (r : AnnRad ρ0 σ0) (x y : T.Ann ρ0 σ0) :
    T.annNorm ρ0 σ0 r (x + y) ≤ max (T.annNorm ρ0 σ0 r x) (T.annNorm ρ0 σ0 r y) :=
  Completion.induction_on₂ x y
    (isClosed_le ((T.continuous_annNorm r).comp continuous_add)
      (((T.continuous_annNorm r).comp continuous_fst).max ((T.continuous_annNorm r).comp continuous_snd)))
    fun a b => by
      rw [← Completion.coe_add, annNorm_coe, annNorm_coe, annNorm_coe, coreVal_add]
      have hr0 : (0 : ℝ) < r := σ0.2.1.trans_le r.2.1
      have hr1 : (r : ℝ) < 1 := r.2.2.trans_lt ρ0.2.2
      exact (T.convergesAt_coeffB_add hr0 hr1 (T.convergesAt_coreVal a r) (T.convergesAt_coreVal b r)).2

theorem annNorm_neg (r : AnnRad ρ0 σ0) (x : T.Ann ρ0 σ0) :
    T.annNorm ρ0 σ0 r (-x) = T.annNorm ρ0 σ0 r x :=
  Completion.induction_on x
    (isClosed_eq ((T.continuous_annNorm r).comp continuous_neg) (T.continuous_annNorm r))
    fun a => by
      rw [← Completion.coe_neg, annNorm_coe, annNorm_coe, coreVal_neg]
      have hr0 : (0 : ℝ) < r := σ0.2.1.trans_le r.2.1
      have hr1 : (r : ℝ) < 1 := r.2.2.trans_lt ρ0.2.2
      exact (T.convergesAt_coeffB_neg hr0 hr1 (T.convergesAt_coreVal a r)).2

theorem annNorm_sub_comm (r : AnnRad ρ0 σ0) (x y : T.Ann ρ0 σ0) :
    T.annNorm ρ0 σ0 r (x - y) = T.annNorm ρ0 σ0 r (y - x) := by
  rw [← neg_sub, annNorm_neg]

theorem annNorm_sub_le (r : AnnRad ρ0 σ0) (x y : T.Ann ρ0 σ0) :
    T.annNorm ρ0 σ0 r (x - y) ≤ max (T.annNorm ρ0 σ0 r x) (T.annNorm ρ0 σ0 r y) := by
  rw [sub_eq_add_neg]
  exact (T.annNorm_add_le r _ _).trans (by rw [annNorm_neg])

theorem annNorm_one (r : AnnRad ρ0 σ0) : T.annNorm ρ0 σ0 r 1 = 1 := by
  rw [← Completion.coe_one, annNorm_coe, coreVal_one, ← map_one (algebraMap Γ T.B),
    coeffB_algebraMap, zcoeff_one]
  refine le_antisymm (gaussNorm_single_zero_one_le (σ0.2.1.trans_le r.2.1)) ?_
  have := (convergesAt_pi_single (L := L) 0 1 (r : ℝ)).le_gaussNorm 0
  simpa using this

theorem annNorm_zero (r : AnnRad ρ0 σ0) : T.annNorm ρ0 σ0 r 0 = 0 := by
  rw [← Completion.coe_zero, annNorm_coe, coreVal_zero, ← map_zero (algebraMap Γ T.B),
    coeffB_algebraMap, (T.zcoeff_eq_zero_iff 0).2 rfl]
  simp [gaussNorm]

theorem annNorm_pow (r : AnnRad ρ0 σ0) (x : T.Ann ρ0 σ0) (n : ℕ) :
    T.annNorm ρ0 σ0 r (x ^ n) = T.annNorm ρ0 σ0 r x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, annNorm_one]
  | succ n ih => rw [pow_succ, annNorm_mul, ih, pow_succ]

theorem annNorm_le_max (r : AnnRad ρ0 σ0) (x : T.Ann ρ0 σ0) :
    T.annNorm ρ0 σ0 r x ≤ max (T.annNorm ρ0 σ0 (annIn ρ0 σ0) x) (T.annNorm ρ0 σ0 (annOut ρ0 σ0) x) :=
  Completion.induction_on x
    (isClosed_le (T.continuous_annNorm r)
      ((T.continuous_annNorm _).max (T.continuous_annNorm _)))
    fun b => by
      rw [annNorm_coe, annNorm_coe, annNorm_coe]
      exact T.gaussNorm_coreVal_le b r

theorem annNorm_interp_le (r₁ r₂ r : AnnRad ρ0 σ0) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr : (r : ℝ) = (r₁ : ℝ) ^ (1 - t) * (r₂ : ℝ) ^ t) (x : T.Ann ρ0 σ0) :
    T.annNorm ρ0 σ0 r x ≤ T.annNorm ρ0 σ0 r₁ x ^ (1 - t) * T.annNorm ρ0 σ0 r₂ x ^ t :=
  Completion.induction_on x
    (isClosed_le (T.continuous_annNorm r)
      (((T.continuous_annNorm r₁).rpow_const fun _ => Or.inr (by linarith)).mul
        ((T.continuous_annNorm r₂).rpow_const fun _ => Or.inr ht0)))
    fun b => by
      rw [annNorm_coe, annNorm_coe, annNorm_coe, hr]
      exact gaussNorm_interp_le (σ0.2.1.trans_le r₁.2.1) (σ0.2.1.trans_le r₂.2.1)
        (T.convergesAt_coreVal b r₁) (T.convergesAt_coreVal b r₂) ht0 ht1

theorem dist_ann (x y : T.Ann ρ0 σ0) :
    dist x y = max (T.annNorm ρ0 σ0 (annIn ρ0 σ0) (x - y)) (T.annNorm ρ0 σ0 (annOut ρ0 σ0) (x - y)) :=
  Completion.induction_on₂ x y
    (isClosed_eq continuous_dist
      (((T.continuous_annNorm _).comp (continuous_fst.sub continuous_snd)).max
        ((T.continuous_annNorm _).comp (continuous_fst.sub continuous_snd))))
    fun a b => by
      rw [Completion.dist_eq, ← Completion.coe_sub, annNorm_coe, annNorm_coe, dist_annCore]
      rfl

theorem eq_of_annNorm_sub {x y : T.Ann ρ0 σ0} (hlo : T.annNorm ρ0 σ0 (annIn ρ0 σ0) (x - y) = 0)
    (hhi : T.annNorm ρ0 σ0 (annOut ρ0 σ0) (x - y) = 0) : x = y := by
  rw [← dist_eq_zero, dist_ann, hlo, hhi, max_self]

theorem tendsto_ann {z : ℕ → T.Ann ρ0 σ0} {x : T.Ann ρ0 σ0}
    (h : ∀ ε > 0, ∃ J₀ : ℕ, ∀ J ≥ J₀, T.annNorm ρ0 σ0 (annIn ρ0 σ0) (z J - x) ≤ ε ∧
      T.annNorm ρ0 σ0 (annOut ρ0 σ0) (z J - x) ≤ ε) : Tendsto z atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨J₀, hJ₀⟩ := h (ε / 2) (half_pos hε)
  refine ⟨J₀, fun J hJ => ?_⟩
  rw [dist_ann]
  obtain ⟨h1, h2⟩ := hJ₀ J hJ
  exact lt_of_le_of_lt (max_le h1 h2) (half_lt_self hε)

theorem exists_limit_ann {z : ℕ → T.Ann ρ0 σ0}
    (h : ∀ ε > 0, ∃ J₀ : ℕ, ∀ J ≥ J₀, ∀ K ≥ J₀, T.annNorm ρ0 σ0 (annIn ρ0 σ0) (z J - z K) ≤ ε ∧
      T.annNorm ρ0 σ0 (annOut ρ0 σ0) (z J - z K) ≤ ε) :
    ∃ x : T.Ann ρ0 σ0, ∀ r : AnnRad ρ0 σ0, Tendsto (fun J => T.annNorm ρ0 σ0 r (z J - x)) atTop (𝓝 0) := by
  have hc : CauchySeq z := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨J₀, hJ₀⟩ := h (ε / 2) (half_pos hε)
    refine ⟨J₀, fun J hJ => ?_⟩
    rw [dist_ann]
    obtain ⟨h1, h2⟩ := hJ₀ J hJ J₀ le_rfl
    exact lt_of_le_of_lt (max_le h1 h2) (half_lt_self hε)
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨x, fun r => ?_⟩
  have h0 : Tendsto (fun J => T.annNorm ρ0 σ0 r (z J - x)) atTop (𝓝 (T.annNorm ρ0 σ0 r (x - x))) :=
    ((T.continuous_annNorm r).tendsto _).comp (hx.sub tendsto_const_nhds)
  rwa [sub_self, annNorm_zero] at h0

theorem annNorm_sub_le_dist (r : AnnRad ρ0 σ0) (x y : T.Ann ρ0 σ0) :
    T.annNorm ρ0 σ0 r (x - y) ≤ dist x y := by
  rw [dist_ann]; exact T.annNorm_le_max r _

theorem exists_coeAnn_near (x : T.Ann ρ0 σ0) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : T.Econ ρ0, ∀ r : AnnRad ρ0 σ0, T.annNorm ρ0 σ0 r (x - T.coeAnn b) < ε := by
  obtain ⟨b, hb⟩ := Completion.denseRange_coe.exists_dist_lt x hε
  exact ⟨b, fun r => (T.annNorm_sub_le_dist r _ _).trans_lt hb⟩

theorem gaussNorm_mem_uniformity (ρ : Set.Ioc (0 : ℝ) ρ0) {ε : ℝ} (hε : 0 < ε) :
    {x : T.Econ ρ0 × T.Econ ρ0 | gaussNorm (T.coeffB ((x.1 : T.B) - x.2)) ρ < ε} ∈ 𝓤 (T.Econ ρ0) := by
  have hU : {x : T.Econ ρ0 × T.Econ ρ0 |
      @dist _ (T.gaussSeminorm ρ0 ρ).toSeminormedRing.toPseudoMetricSpace.toDist x.1 x.2 < ε} ∈
      @uniformity _ (T.uniformAt ρ0 ρ) :=
    @Metric.dist_mem_uniformity _ (T.gaussSeminorm ρ0 ρ).toSeminormedRing.toPseudoMetricSpace ε hε
  have hiInf : uniformity (T.Econ ρ0) = ⨅ ρ, @uniformity _ (T.uniformAt ρ0 ρ) := iInf_uniformity
  rw [hiInf]
  refine Filter.mem_iInf_of_mem ρ (Filter.mem_of_superset hU fun x hx => ?_)
  change gaussNorm _ _ < ε
  change @dist _ (T.gaussSeminorm ρ0 ρ).toSeminormedRing.toPseudoMetricSpace.toDist x.1 x.2 < ε at hx
  rwa [dist_uniformAt'] at hx

variable (ρ0 σ0) in
theorem uniformContinuous_coreOf : UniformContinuous (T.coreOf ρ0 σ0) := by
  refine Metric.uniformity_basis_dist.tendsto_right_iff.2 fun ε hε => ?_
  filter_upwards [T.gaussNorm_mem_uniformity σ0 hε, T.gaussNorm_mem_uniformity (topRad ρ0) hε] with x h1 h2
  rw [dist_annCore]
  exact max_lt h1 h2

variable (ρ0 σ0) in

def toAnn : T.RobbaExt ρ0 →+* T.Ann ρ0 σ0 :=
  Completion.mapRingHom (T.coreOf ρ0 σ0) (T.uniformContinuous_coreOf ρ0 σ0).continuous

theorem toAnn_coe (b : T.Econ ρ0) : T.toAnn ρ0 σ0 (b : T.RobbaExt ρ0) = T.coeAnn b :=
  Completion.mapRingHom_coe (T.uniformContinuous_coreOf ρ0 σ0).continuous b

theorem continuous_toAnn : Continuous (T.toAnn ρ0 σ0) := Completion.continuous_map

theorem annNorm_toAnn (r : AnnRad ρ0 σ0) (x : T.RobbaExt ρ0) :
    T.annNorm ρ0 σ0 r (T.toAnn ρ0 σ0 x) = T.extNorm ρ0 (annIoc r) x :=
  Completion.induction_on x
    (isClosed_eq ((T.continuous_annNorm r).comp T.continuous_toAnn) (T.continuous_extNorm _))
    fun b => by rw [toAnn_coe, annNorm_coeAnn, extNorm_coe]; rfl

section Res

variable {ρ1 : Set.Ioo (0 : ℝ) 1} (σ1 : Set.Ioc (0 : ℝ) ρ1) (h : (ρ1 : ℝ) ≤ ρ0)

variable {σ1} in

def annRadOf (hσ : (σ0 : ℝ) ≤ σ1) (r : AnnRad ρ1 σ1) : AnnRad ρ0 σ0 :=
  ⟨r, hσ.trans r.2.1, r.2.2.trans h⟩

variable {σ1} in
@[simp] theorem coe_annRadOf (hσ : (σ0 : ℝ) ≤ σ1) (r : AnnRad ρ1 σ1) :
    ((annRadOf h hσ r : AnnRad ρ0 σ0) : ℝ) = r := rfl

def coreIncl : T.AnnCore ρ0 σ0 →+* T.AnnCore ρ1 σ1 := T.incl h

theorem coreVal_coreIncl (b : T.AnnCore ρ0 σ0) :
    T.coreVal ρ1 σ1 (T.coreIncl σ1 h b) = T.coreVal ρ0 σ0 b := rfl

variable {σ1} in
theorem dist_coreIncl_le (hσ : (σ0 : ℝ) ≤ σ1) (a b : T.AnnCore ρ0 σ0) :
    dist (T.coreIncl σ1 h a) (T.coreIncl σ1 h b) ≤ dist a b := by
  rw [dist_annCore (a := T.coreIncl σ1 h a), dist_annCore (a := a), ← map_sub, coreVal_coreIncl]
  exact max_le (T.gaussNorm_coreVal_le (a - b) (annRadOf h hσ (annIn ρ1 σ1)))
    (T.gaussNorm_coreVal_le (a - b) (annRadOf h hσ (annOut ρ1 σ1)))

variable {σ1} in
theorem uniformContinuous_coreIncl (hσ : (σ0 : ℝ) ≤ σ1) :
    UniformContinuous (T.coreIncl (σ0 := σ0) σ1 h) :=
  LipschitzWith.uniformContinuous (K := 1) (LipschitzWith.of_dist_le_mul fun a b => by
    rw [NNReal.coe_one, one_mul]; exact T.dist_coreIncl_le h hσ a b)

variable {σ1} in

def annRes (hσ : (σ0 : ℝ) ≤ σ1) : T.Ann ρ0 σ0 →+* T.Ann ρ1 σ1 :=
  Completion.mapRingHom (T.coreIncl σ1 h) (T.uniformContinuous_coreIncl h hσ).continuous

variable {σ1} (hσ : (σ0 : ℝ) ≤ σ1)

theorem annRes_coe (b : T.AnnCore ρ0 σ0) :
    T.annRes h hσ (b : T.Ann ρ0 σ0) = ((T.coreIncl σ1 h b : T.AnnCore ρ1 σ1) : T.Ann ρ1 σ1) :=
  Completion.mapRingHom_coe (T.uniformContinuous_coreIncl h hσ).continuous b

theorem continuous_annRes : Continuous (T.annRes h hσ) := Completion.continuous_map

theorem annNorm_annRes (r : AnnRad ρ1 σ1) (x : T.Ann ρ0 σ0) :
    T.annNorm ρ1 σ1 r (T.annRes h hσ x) = T.annNorm ρ0 σ0 (annRadOf h hσ r) x :=
  Completion.induction_on x
    (isClosed_eq ((T.continuous_annNorm r).comp (T.continuous_annRes h hσ)) (T.continuous_annNorm _))
    fun b => by rw [annRes_coe, annNorm_coe, annNorm_coe, coreVal_coreIncl]; rfl

theorem annRes_coeAnn (b : T.Econ ρ0) : T.annRes h hσ (T.coeAnn b) = T.coeAnn (T.incl h b) :=
  T.annRes_coe h hσ _

theorem annRes_toAnn (x : T.RobbaExt ρ0) :
    T.annRes h hσ (T.toAnn ρ0 σ0 x) = T.toAnn ρ1 σ1 (T.res h x) :=
  Completion.induction_on x
    (isClosed_eq ((T.continuous_annRes h hσ).comp T.continuous_toAnn)
      (T.continuous_toAnn.comp (T.continuous_res h)))
    fun b => by rw [toAnn_coe, annRes_coeAnn, res_coe, toAnn_coe]

end Res

theorem max_pow_eq_pow_max {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    max (a ^ n) (b ^ n) = max a b ^ n := by
  rcases le_total a b with hab | hab
  · rw [max_eq_right hab, max_eq_right (pow_le_pow_left₀ ha hab n)]
  · rw [max_eq_left hab, max_eq_left (pow_le_pow_left₀ hb hab n)]

namespace TeichFrob

variable {T} (F : T.TeichFrob)

def annPowRad (r : AnnRad ρ0 σ0) : AnnRad (F.powRadius ρ0) (F.powRad σ0) :=
  ⟨(r : ℝ) ^ p ^ F.a, pow_le_pow_left₀ σ0.2.1.le r.2.1 _, pow_le_pow_left₀ (σ0.2.1.trans_le r.2.1).le r.2.2 _⟩

@[simp] theorem coe_annPowRad (r : AnnRad ρ0 σ0) :
    ((F.annPowRad r : AnnRad (F.powRadius ρ0) (F.powRad σ0)) : ℝ) = (r : ℝ) ^ p ^ F.a := rfl

def coreFrob : T.AnnCore ρ0 σ0 →+* T.AnnCore (F.powRadius ρ0) (F.powRad σ0) := F.econFrob ρ0

theorem coreVal_coreFrob (b : T.AnnCore ρ0 σ0) :
    T.coreVal _ _ (F.coreFrob b) = F.toB (T.coreVal ρ0 σ0 b) := rfl

theorem gaussNorm_coreFrob (b : T.AnnCore ρ0 σ0) (r : AnnRad ρ0 σ0) :
    gaussNorm (T.coeffB (T.coreVal _ _ (F.coreFrob b))) (F.annPowRad r) =
      gaussNorm (T.coeffB (T.coreVal ρ0 σ0 b)) r ^ p ^ F.a := by
  rw [coreVal_coreFrob, coe_annPowRad]
  exact F.gaussNorm_toB_pow (σ0.2.1.trans_le r.2.1) (r.2.2.trans_lt ρ0.2.2) (T.convergesAt_coreVal b r)

theorem dist_coreFrob (a b : T.AnnCore ρ0 σ0) :
    dist (F.coreFrob a) (F.coreFrob b) = dist a b ^ p ^ F.a := by
  rw [dist_annCore, dist_annCore, ← map_sub]
  have e1 := F.gaussNorm_coreFrob (a - b) (annIn ρ0 σ0)
  have e2 := F.gaussNorm_coreFrob (a - b) (annOut ρ0 σ0)
  have h1 : ((F.powRad σ0 : Set.Ioc (0 : ℝ) (F.powRadius ρ0)) : ℝ) = (F.annPowRad (annIn ρ0 σ0) : ℝ) :=
    rfl
  have h2 : ((F.powRadius ρ0 : Set.Ioo (0 : ℝ) 1) : ℝ) = (F.annPowRad (annOut ρ0 σ0) : ℝ) := rfl
  rw [coe_annIn] at e1
  rw [coe_annOut] at e2
  rw [h1, h2, e1, e2]
  exact max_pow_eq_pow_max (T.gaussNorm_coreVal_nonneg _ (annIn ρ0 σ0)) (T.gaussNorm_coreVal_nonneg _ (annOut ρ0 σ0)) _

theorem uniformContinuous_coreFrob : UniformContinuous (F.coreFrob (ρ0 := ρ0) (σ0 := σ0)) := by
  refine Metric.uniformContinuous_iff.2 fun ε hε => ⟨min 1 ε, lt_min one_pos hε, fun {a b} hab => ?_⟩
  rw [F.dist_coreFrob]
  have h0 : 0 ≤ dist a b := dist_nonneg
  have h1 : dist a b ≤ 1 := hab.le.trans (min_le_left _ _)
  exact (pow_le_of_le_one h0 h1 (pow_ne_zero _ hp.out.ne_zero)).trans_lt (hab.trans_le (min_le_right _ _))

def annFrob : T.Ann ρ0 σ0 →+* T.Ann (F.powRadius ρ0) (F.powRad σ0) :=
  Completion.mapRingHom F.coreFrob F.uniformContinuous_coreFrob.continuous

theorem annFrob_coe (b : T.AnnCore ρ0 σ0) :
    F.annFrob (b : T.Ann ρ0 σ0) = ((F.coreFrob b : T.AnnCore _ _) : T.Ann _ _) :=
  Completion.mapRingHom_coe F.uniformContinuous_coreFrob.continuous b

theorem continuous_annFrob : Continuous (F.annFrob (ρ0 := ρ0) (σ0 := σ0)) := Completion.continuous_map

theorem annNorm_annFrob (r : AnnRad ρ0 σ0) (x : T.Ann ρ0 σ0) :
    T.annNorm _ _ (F.annPowRad r) (F.annFrob x) = T.annNorm ρ0 σ0 r x ^ p ^ F.a :=
  Completion.induction_on x
    (isClosed_eq ((T.continuous_annNorm _).comp F.continuous_annFrob) ((T.continuous_annNorm r).pow _))
    fun b => by rw [annFrob_coe, annNorm_coe, annNorm_coe, F.gaussNorm_coreFrob]

theorem annFrob_coeAnn (b : T.Econ ρ0) : F.annFrob (T.coeAnn (σ0 := σ0) b) = T.coeAnn (F.econFrob ρ0 b) :=
  F.annFrob_coe _

theorem annFrob_toAnn (x : T.RobbaExt ρ0) :
    F.annFrob (T.toAnn ρ0 σ0 x) = T.toAnn (F.powRadius ρ0) (F.powRad σ0) (F.extFrob ρ0 x) :=
  Completion.induction_on x
    (isClosed_eq (F.continuous_annFrob.comp T.continuous_toAnn)
      (T.continuous_toAnn.comp (F.continuous_extFrob ρ0)))
    fun b => by rw [toAnn_coe, annFrob_coeAnn, extFrob_coe, toAnn_coe]

end TeichFrob

namespace TeichIso

variable {T} (G : T.TeichIso)

def coreMap : T.AnnCore ρ0 σ0 →+* T.AnnCore ρ0 σ0 := G.econMap ρ0

theorem coreVal_coreMap (b : T.AnnCore ρ0 σ0) : T.coreVal ρ0 σ0 (G.coreMap b) = G.toB (T.coreVal ρ0 σ0 b) :=
  rfl

theorem dist_coreMap (a b : T.AnnCore ρ0 σ0) : dist (G.coreMap a) (G.coreMap b) = dist a b := by
  rw [dist_annCore, dist_annCore, ← map_sub, coreVal_coreMap, G.gaussNorm_coeffB_toB,
    G.gaussNorm_coeffB_toB]

theorem uniformContinuous_coreMap : UniformContinuous (G.coreMap (ρ0 := ρ0) (σ0 := σ0)) :=
  LipschitzWith.uniformContinuous (K := 1) (LipschitzWith.of_dist_le_mul fun a b => by
    rw [NNReal.coe_one, one_mul, G.dist_coreMap])

def annMap : T.Ann ρ0 σ0 →+* T.Ann ρ0 σ0 :=
  Completion.mapRingHom G.coreMap G.uniformContinuous_coreMap.continuous

theorem annMap_coe (b : T.AnnCore ρ0 σ0) :
    G.annMap (b : T.Ann ρ0 σ0) = ((G.coreMap b : T.AnnCore ρ0 σ0) : T.Ann ρ0 σ0) :=
  Completion.mapRingHom_coe G.uniformContinuous_coreMap.continuous b

theorem continuous_annMap : Continuous (G.annMap (ρ0 := ρ0) (σ0 := σ0)) := Completion.continuous_map

theorem annNorm_annMap (r : AnnRad ρ0 σ0) (x : T.Ann ρ0 σ0) :
    T.annNorm ρ0 σ0 r (G.annMap x) = T.annNorm ρ0 σ0 r x :=
  Completion.induction_on x
    (isClosed_eq ((T.continuous_annNorm r).comp G.continuous_annMap) (T.continuous_annNorm r))
    fun b => by rw [annMap_coe, annNorm_coe, annNorm_coe, coreVal_coreMap, G.gaussNorm_coeffB_toB]

theorem annMap_coeAnn (b : T.Econ ρ0) : G.annMap (T.coeAnn (σ0 := σ0) b) = T.coeAnn (G.econMap ρ0 b) :=
  G.annMap_coe _

theorem annMap_toAnn (x : T.RobbaExt ρ0) :
    G.annMap (T.toAnn ρ0 σ0 x) = T.toAnn ρ0 σ0 (G.extMap ρ0 x) :=
  Completion.induction_on x
    (isClosed_eq (G.continuous_annMap.comp T.continuous_toAnn)
      (T.continuous_toAnn.comp Completion.continuous_map))
    fun b => by rw [toAnn_coe, annMap_coeAnn, extMap_coe, toAnn_coe]

end TeichIso

end TeichLift

end GroundTheory.PAdicHodge
