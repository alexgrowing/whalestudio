import Mathlib

noncomputable section

namespace PI.VolStabW

open MeasureTheory Set
open scoped ENNReal Pointwise

section Abs

variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]

instance subMeasurableMul (H : Subgroup G) : MeasurableMul H where
  measurable_const_mul c := by
    exact (((measurable_const_mul (c : G)).comp measurable_subtype_coe).subtype_mk :
      Measurable fun x : H => (⟨(c : G) * x, H.mul_mem c.2 x.2⟩ : H))
  measurable_mul_const c := by
    exact (((measurable_mul_const (c : G)).comp measurable_subtype_coe).subtype_mk :
      Measurable fun x : H => (⟨(x : G) * c, H.mul_mem x.2 c.2⟩ : H))

instance subMeasurableInv (H : Subgroup G) : MeasurableInv H where
  measurable_inv := by
    exact ((measurable_inv.comp measurable_subtype_coe).subtype_mk :
      Measurable fun x : H => (⟨(x : G)⁻¹, H.inv_mem x.2⟩ : H))

theorem fd_of_subset {Γ : Subgroup G} [Countable Γ] {μ : Measure G} [μ.IsMulLeftInvariant]
    {s t : Set G} (h : IsFundamentalDomain Γ s μ) (hts : t ⊆ s) (ht : MeasurableSet t)
    (hnull : μ (s \ t) = 0) : IsFundamentalDomain Γ t μ where
  nullMeasurableSet := ht.nullMeasurableSet
  ae_covers := by
    have h1 : ∀ (γ : Γ), ∀ᵐ g ∂μ, g ∉ (fun g => (γ : G) * g) ⁻¹' (s \ t) := fun γ =>
      measure_eq_zero_iff_ae_notMem.1 (by rw [measure_preimage_mul]; exact hnull)
    have h2 := (ae_all_iff (ι := Γ)).2 h1
    filter_upwards [h.ae_covers, h2] with g hg h3
    obtain ⟨γ, hγ⟩ := hg
    refine ⟨γ, ?_⟩
    by_contra hn
    exact h3 γ ⟨hγ, hn⟩
  aedisjoint := fun γ γ' hne =>
    measure_mono_null (inter_subset_inter (smul_set_mono hts) (smul_set_mono hts)) (h.aedisjoint hne)

theorem fd_count_ae {Γ : Subgroup G} [Countable Γ] {μ : Measure G} {s : Set G}
    (h : IsFundamentalDomain Γ s μ) :
    ∀ᵐ g ∂μ, ∑' γ : Γ, s.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * g) = 1 := by
  have hpair : ∀ᵐ g ∂μ, ∀ γ γ' : Γ, γ • g ∈ s → γ' • g ∈ s → γ = γ' := by
    rw [ae_all_iff]
    intro γ
    rw [ae_all_iff]
    intro γ'
    by_cases hγ : γ = γ'
    · exact Filter.Eventually.of_forall fun _ _ _ => hγ
    · have hd : μ (γ⁻¹ • s ∩ γ'⁻¹ • s) = 0 :=
        h.aedisjoint (show γ⁻¹ ≠ γ'⁻¹ from fun e => hγ (inv_injective e))
      filter_upwards [compl_mem_ae_iff.2 hd] with g hg h1 h2
      exact absurd ⟨Set.mem_inv_smul_set_iff.2 h1, Set.mem_inv_smul_set_iff.2 h2⟩ hg
  filter_upwards [h.ae_covers, hpair] with g hc hu
  obtain ⟨γ0, hγ0⟩ := hc
  rw [tsum_eq_single γ0]
  · exact Set.indicator_of_mem hγ0 _
  · intro γ hne
    exact Set.indicator_apply_eq_zero.2 fun hm => absurd (hu γ γ0 hm hγ0) hne

theorem countable_subgroupOf {Γ H : Subgroup G} [Countable Γ] :
    Countable ((Γ ⊓ H).subgroupOf H) := by
  refine Function.Injective.countable
    (f := fun x : (Γ ⊓ H).subgroupOf H =>
      (⟨((x : H) : G), (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 x.2)).1⟩ : Γ)) ?_
  intro a b hab
  have e : ((a : H) : G) = ((b : H) : G) := congrArg (fun z : Γ => (z : G)) hab
  exact Subtype.ext (Subtype.ext e)

theorem lint_mul_right {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (f : G → ℝ≥0∞) (r : G) : ∫⁻ g, f (g * r) ∂μ = ∫⁻ g, f g ∂μ := by
  calc ∫⁻ g, f (g * r) ∂μ = ∫⁻ g, f (g⁻¹ * r) ∂μ := (lintegral_inv_eq_self (fun g => f (g * r))).symm
    _ = ∫⁻ g, (fun h => f h⁻¹) (r⁻¹ * g) ∂μ := by
      congr 1
      funext g
      simp [mul_inv_rev]
    _ = ∫⁻ g, f g⁻¹ ∂μ := lintegral_mul_left_eq_self (fun h => f h⁻¹) r⁻¹
    _ = ∫⁻ g, f g ∂μ := lintegral_inv_eq_self f

variable [MulAction G Y]

def orbS (Γ : Subgroup G) (y0 : Y) : Set Y := {x | ∃ γ ∈ Γ, γ • y0 = x}

def repO (Γ : Subgroup G) (y0 : Y) (x : orbS Γ y0) : G :=
  Classical.choose (x.2 : ∃ γ ∈ Γ, γ • y0 = (x : Y))

theorem repO_mem (Γ : Subgroup G) (y0 : Y) (x : orbS Γ y0) : repO Γ y0 x ∈ Γ := by
  exact (Classical.choose_spec x.2).1

theorem repO_smul (Γ : Subgroup G) (y0 : Y) (x : orbS Γ y0) : repO Γ y0 x • y0 = x := by
  exact (Classical.choose_spec x.2).2

def cntN (Γ : Subgroup G) (A : Set G) (g : G) : ℝ≥0∞ :=
  ∑' γ : Γ, A.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * g)

def cfun (Γ : Subgroup G) (A : Set G) (y0 : Y) (g : G) : ℝ≥0∞ :=
  ∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * g⁻¹)

theorem meas_cntN (Γ : Subgroup G) [Countable Γ] {A : Set G} (hA : MeasurableSet A) :
    Measurable (cntN Γ A) := by
  unfold cntN
  exact Measurable.ennreal_tsum fun γ =>
    (measurable_const.indicator hA).comp (measurable_const_mul (γ : G))

theorem meas_cfun (Γ : Subgroup G) (y0 : Y) [Countable (orbS Γ y0)] {A : Set G}
    (hA : MeasurableSet A) : Measurable (cfun Γ A y0) := by
  unfold cfun
  exact Measurable.ennreal_tsum fun x =>
    (measurable_const.indicator hA).comp ((measurable_const_mul (repO Γ y0 x)).comp measurable_inv)

theorem cntN_mul (Γ : Subgroup G) (A : Set G) {γ : G} (hγ : γ ∈ Γ) (g : G) :
    cntN Γ A (γ * g) = cntN Γ A g := by
  unfold cntN
  have e := (Equiv.mulRight (⟨γ, hγ⟩ : Γ)).tsum_eq
    (fun δ : Γ => A.indicator (fun _ => (1 : ℝ≥0∞)) ((δ : G) * g))
  simpa [mul_assoc] using e

theorem sum_rep_eq {Γ H : Subgroup G} (y0 : Y) (hH : ∀ k : G, k ∈ H ↔ k • y0 = y0)
    (u : G → ℝ≥0∞) :
    ∑' x : orbS Γ y0, ∑' δ : (Γ ⊓ H).subgroupOf H, u (repO Γ y0 x * ((δ : H) : G)) =
      ∑' γ : Γ, u γ := by
  classical
  let F : orbS Γ y0 × (Γ ⊓ H).subgroupOf H → Γ := fun p =>
    ⟨repO Γ y0 p.1 * ((p.2 : H) : G), Γ.mul_mem (repO_mem Γ y0 p.1)
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 p.2.2)).1⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨x, δ⟩ ⟨x', δ'⟩ he
      have he' : repO Γ y0 x * ((δ : H) : G) = repO Γ y0 x' * ((δ' : H) : G) := congrArg Subtype.val he
      have hδ : ((δ : H) : G) • y0 = y0 := (hH _).1 (δ : H).2
      have hδ' : ((δ' : H) : G) • y0 = y0 := (hH _).1 (δ' : H).2
      have hx : (x : Y) = x' := by
        calc (x : Y) = repO Γ y0 x • y0 := (repO_smul Γ y0 x).symm
          _ = repO Γ y0 x • (((δ : H) : G) • y0) := by rw [hδ]
          _ = (repO Γ y0 x * ((δ : H) : G)) • y0 := (mul_smul _ _ _).symm
          _ = (repO Γ y0 x' * ((δ' : H) : G)) • y0 := by rw [he']
          _ = repO Γ y0 x' • (((δ' : H) : G) • y0) := mul_smul _ _ _
          _ = repO Γ y0 x' • y0 := by rw [hδ']
          _ = x' := repO_smul Γ y0 x'
      have hxx : x = x' := Subtype.ext hx
      subst hxx
      have e : ((δ : H) : G) = ((δ' : H) : G) := mul_left_cancel he'
      exact Prod.ext rfl (Subtype.ext (Subtype.ext e))
    · intro γ
      have hd : (repO Γ y0 ⟨(γ : G) • y0, γ, γ.2, rfl⟩)⁻¹ * γ ∈ H := by
        rw [hH, mul_smul, inv_smul_eq_iff, repO_smul]
      refine ⟨(⟨(γ : G) • y0, γ, γ.2, rfl⟩, ⟨⟨_, hd⟩, Subgroup.mem_subgroupOf.2
        (Subgroup.mem_inf.2 ⟨Γ.mul_mem (Γ.inv_mem (repO_mem Γ y0 _)) γ.2, hd⟩)⟩), ?_⟩
      apply Subtype.ext
      exact mul_inv_cancel_left _ _
  calc _ = ∑' p : orbS Γ y0 × (Γ ⊓ H).subgroupOf H, u (repO Γ y0 p.1 * ((p.2 : H) : G)) :=
        (ENNReal.tsum_prod (f := fun x (δ : (Γ ⊓ H).subgroupOf H) => u (repO Γ y0 x * ((δ : H) : G)))).symm
    _ = ∑' γ : Γ, u γ := (Equiv.ofBijective F hF).tsum_eq (fun γ : Γ => u γ)

end Abs

end PI.VolStabW
