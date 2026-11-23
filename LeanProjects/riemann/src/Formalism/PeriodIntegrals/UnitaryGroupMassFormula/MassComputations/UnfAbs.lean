import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.UnfoldAbs
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst

noncomputable section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace MassDataMassesW.Abs

variable {G Gf : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
  [Group Gf] [MeasurableSpace Gf] [MeasurableMul Gf]

theorem meas_eq_lint_cnt {Γ : Subgroup G} [Countable Γ] {μ : Measure G} [μ.IsMulLeftInvariant]
    {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ) {A : Set G} (hA : MeasurableSet A) :
    μ A = ∫⁻ g in 𝓕, PI.VolStabSW.cntN Γ A g ∂μ := by
  rw [← lintegral_indicator_one hA, h.lintegral_eq_tsum'']
  unfold PI.VolStabSW.cntN
  rw [lintegral_tsum]
  · rfl
  · intro γ
    exact ((measurable_const.indicator hA).comp (measurable_const_mul _)).aemeasurable

theorem meas_smul_set {s : Set Gf} (hs : MeasurableSet s) (x : Gf) : MeasurableSet (x • s) := by
  have : x • s = (fun y => x⁻¹ * y) ⁻¹' s := by
    ext y
    simp [mem_smul_set_iff_inv_smul_mem]
  rw [this]
  exact measurable_const_mul _ hs

theorem unfold_mass {Γ : Subgroup G} [Countable Γ] {μ : Measure G} [μ.IsMulLeftInvariant]
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (p : G →* Gf) (hp : Measurable p) (Γf U : Subgroup Gf)
    (himg : Γ.map p = Γf) (hinj : ∀ γ ∈ Γ, p γ = 1 → γ = 1)
    (hU : MeasurableSet (U : Set Gf)) (hfin : Formalism.L2.SG.TypedSets.MassFinite Γf U)
    (c0 : ℝ≥0∞) (hc0 : ∀ x : Gf, μ (p ⁻¹' (x • (U : Set Gf))) = c0) :
    μ 𝓕 = c0 * ENNReal.ofReal (Formalism.L2.SG.TypedSets.massCl Γf U) := by
  classical
  obtain ⟨hC, hS⟩ := hfin
  haveI := Fintype.ofFinite (DoubleCoset.Quotient (Γf : Set Gf) (U : Set Gf))

  haveI : Countable Γf := by
    have hsurj : Function.Surjective (fun γ : Γ => (⟨p γ, himg ▸ Subgroup.mem_map_of_mem p γ.2⟩ : Γf)) := by
      rintro ⟨y, hy⟩
      rw [← himg] at hy
      obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hy
      exact ⟨⟨γ, hγ⟩, rfl⟩
    exact hsurj.countable
  let cl : Gf → DoubleCoset.Quotient (Γf : Set Gf) (U : Set Gf) := DoubleCoset.mk Γf U
  let xo : DoubleCoset.Quotient (Γf : Set Gf) (U : Set Gf) → Gf := fun c => Quotient.out c
  let Nc : DoubleCoset.Quotient (Γf : Set Gf) (U : Set Gf) → ℕ := fun c =>
    Nat.card ↥(Γf ⊓ U.map (MulAut.conj (xo c)).toMonoidHom)

  have hcl : ∀ c, cl ⁻¹' {c} = ⋃ δ : Γf, (δ : Gf) • (xo c • (U : Set Gf)) := by
    intro c
    ext y
    simp only [mem_preimage, mem_singleton_iff, mem_iUnion]
    constructor
    · intro hy
      have h1 := (DoubleCoset.eq Γf U (xo c) y).1 (by
        show DoubleCoset.mk Γf U (Quotient.out c) = DoubleCoset.mk Γf U y
        rw [DoubleCoset.out_eq']; exact hy.symm)
      obtain ⟨h, hh, k, hk, rfl⟩ := h1
      refine ⟨⟨h, hh⟩, ?_⟩
      rw [smul_smul]
      exact ⟨k, hk, by simp [smul_eq_mul]⟩
    · rintro ⟨δ, k, hk, hy⟩
      obtain ⟨k', hk', rfl⟩ := hk
      simp only [smul_eq_mul] at hy
      show DoubleCoset.mk Γf U y = c
      rw [← DoubleCoset.out_eq' Γf U c, DoubleCoset.eq]
      exact ⟨δ⁻¹, Γf.inv_mem δ.2, k'⁻¹, U.inv_mem hk', by rw [← hy]; simp [xo, mul_assoc]⟩
  have hDm : ∀ c, MeasurableSet (cl ⁻¹' {c}) := by
    intro c
    rw [hcl c]
    exact MeasurableSet.iUnion fun δ => meas_smul_set (meas_smul_set hU _) _

  have hcnt : ∀ c g, PI.VolStabSW.cntN Γ (p ⁻¹' (xo c • (U : Set Gf))) g =
      (cl ⁻¹' {c}).indicator (fun _ => (Nc c : ℝ≥0∞)) (p g) := by
    intro c g
    unfold PI.VolStabSW.cntN
    by_cases hg : cl (p g) = c
    · rw [indicator_of_mem (show p g ∈ cl ⁻¹' {c} from hg)]
      have h1 := (DoubleCoset.eq Γf U (xo c) (p g)).1 (by
        show DoubleCoset.mk Γf U (Quotient.out c) = DoubleCoset.mk Γf U (p g)
        rw [DoubleCoset.out_eq']; exact hg.symm)
      obtain ⟨h, hh, k, hk, hpg⟩ := h1
      rw [← himg] at hh
      obtain ⟨γ0, hγ0, rfl⟩ := Subgroup.mem_map.1 hh
      let V : Subgroup Gf := U.map (MulAut.conj (xo c)).toMonoidHom
      have hiff : ∀ γ : Γ, ((γ : G) * g ∈ p ⁻¹' (xo c • (U : Set Gf))) ↔ p ((γ : G) * γ0) ∈ V := by
        intro γ
        simp only [mem_preimage, map_mul, hpg]
        rw [mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
        simp only [V, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, SetLike.mem_coe]
        constructor
        · intro hm
          refine ⟨(xo c)⁻¹ * (p γ * p γ0) * xo c, ?_, by group⟩
          have := U.mul_mem hm (U.inv_mem hk)
          convert this using 1
          group
        · rintro ⟨v, hv, hv'⟩
          have e : (xo c)⁻¹ * (p γ * (p γ0 * xo c * k)) = v * k := by
            calc _ = (xo c)⁻¹ * ((p γ * p γ0) * xo c * k) := by group
              _ = (xo c)⁻¹ * ((xo c * v * (xo c)⁻¹) * xo c * k) := by rw [hv']
              _ = v * k := by group
          rw [e]
          exact U.mul_mem hv hk
      have hsum1 : ∑' γ : Γ, (p ⁻¹' (xo c • (U : Set Gf))).indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * g) =
          ∑' γ : Γ, {γ : Γ | p (γ : G) ∈ V}.indicator (fun _ => (1 : ℝ≥0∞)) (γ * ⟨γ0, hγ0⟩) := by
        refine tsum_congr fun γ => ?_
        by_cases hm : (γ : G) * g ∈ p ⁻¹' (xo c • (U : Set Gf))
        · rw [indicator_of_mem hm, indicator_of_mem]
          exact (hiff γ).1 hm
        · rw [indicator_of_notMem hm, indicator_of_notMem]
          exact fun h' => hm ((hiff γ).2 h')
      have hsh : ∑' γ : Γ, {γ : Γ | p (γ : G) ∈ V}.indicator (fun _ => (1 : ℝ≥0∞)) (γ * ⟨γ0, hγ0⟩) =
          ∑' γ : Γ, {γ : Γ | p (γ : G) ∈ V}.indicator (fun _ => (1 : ℝ≥0∞)) γ :=
        (Equiv.mulRight (⟨γ0, hγ0⟩ : Γ)).tsum_eq
          (fun γ => {γ : Γ | p (γ : G) ∈ V}.indicator (fun _ => (1 : ℝ≥0∞)) γ)
      rw [hsum1, hsh]
      rw [← tsum_subtype, ENNReal.tsum_one]
      let φ : {γ : Γ | p (γ : G) ∈ V} → ↥(Γf ⊓ V) := fun t =>
        ⟨p ((t : Γ) : G), Subgroup.mem_inf.2 ⟨by rw [← himg]; exact Subgroup.mem_map_of_mem p (t : Γ).2, t.2⟩⟩
      have hφi : Function.Injective φ := by
        intro t t' htt
        have e1 : p ((t : Γ) : G) = p ((t' : Γ) : G) := congrArg Subtype.val htt
        have e2 : ((t : Γ) : G)⁻¹ * ((t' : Γ) : G) = 1 := by
          apply hinj _ (Γ.mul_mem (Γ.inv_mem (t : Γ).2) (t' : Γ).2)
          rw [map_mul, map_inv, e1, inv_mul_cancel]
        exact Subtype.ext (Subtype.ext (inv_mul_eq_one.1 e2))
      have hφs : Function.Surjective φ := by
        rintro ⟨y, hy⟩
        obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
        rw [← himg] at hy1
        obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hy1
        exact ⟨⟨⟨γ, hγ⟩, hy2⟩, rfl⟩
      haveI : Finite ↥(Γf ⊓ V) := hS (xo c)
      haveI : Finite {γ : Γ | p (γ : G) ∈ V} := Finite.of_injective φ hφi
      have hT : Nat.card {γ : Γ | p (γ : G) ∈ V} = Nc c :=
        Nat.card_congr (Equiv.ofBijective φ ⟨hφi, hφs⟩)
      rw [ENat.card_eq_coe_natCard, hT]
      simp
    · rw [indicator_of_notMem (show p g ∉ cl ⁻¹' {c} from hg)]
      refine ENNReal.tsum_eq_zero.2 fun γ => indicator_of_notMem (fun hm => hg ?_) _
      rw [mem_preimage, mem_smul_set] at hm
      obtain ⟨k, hk, hk'⟩ := hm
      show DoubleCoset.mk Γf U (p g) = c
      rw [← DoubleCoset.out_eq' Γf U c, DoubleCoset.eq]
      refine ⟨p γ, by rw [← himg]; exact Subgroup.mem_map_of_mem p γ.2, k⁻¹, U.inv_mem hk, ?_⟩
      rw [map_mul, smul_eq_mul] at hk'
      rw [← hk']
      simp [xo]

  have hpiece : ∀ c, (Nc c : ℝ≥0∞) * μ (𝓕 ∩ p ⁻¹' (cl ⁻¹' {c})) = c0 := by
    intro c
    rw [← hc0 (xo c), meas_eq_lint_cnt h𝓕 (hp (meas_smul_set hU _))]
    simp_rw [hcnt c]
    have : (fun g => (cl ⁻¹' {c}).indicator (fun _ => (Nc c : ℝ≥0∞)) (p g)) =
        (p ⁻¹' (cl ⁻¹' {c})).indicator (fun _ => (Nc c : ℝ≥0∞)) := by
      ext g; simp [indicator]
    rw [this, lintegral_indicator_const (hp (hDm c)), Measure.restrict_apply (hp (hDm c)), inter_comm]
  have hNpos : ∀ c, 0 < Nc c := by
    intro c
    haveI := hS (xo c)
    haveI : Nonempty ↥(Γf ⊓ U.map (MulAut.conj (xo c)).toMonoidHom) := ⟨1⟩
    exact Nat.card_pos

  have hsum : μ 𝓕 = ∑ c, μ (𝓕 ∩ p ⁻¹' (cl ⁻¹' {c})) := by
    have e1 : μ 𝓕 = μ.restrict 𝓕 univ := by rw [Measure.restrict_apply_univ]
    have e2 : (univ : Set G) = ⋃ c ∈ (Finset.univ : Finset (DoubleCoset.Quotient (Γf : Set Gf) (U : Set Gf))),
        p ⁻¹' (cl ⁻¹' {c}) := by
      ext g; simp
    rw [e1, e2, measure_biUnion_finset]
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [Measure.restrict_apply (hp (hDm c)), inter_comm]
    · intro c _ c' _ hne
      exact Set.disjoint_left.2 fun g h1 h2 => hne (h1.symm.trans h2)
    · intro c _
      exact hp (hDm c)
  rw [hsum]
  have hm : Formalism.L2.SG.TypedSets.massCl Γf U = ∑ c, ((Nc c : ℕ) : ℝ)⁻¹ := by
    unfold Formalism.L2.SG.TypedSets.massCl
    rw [finsum_eq_sum_of_fintype]
  rw [hm, ENNReal.ofReal_sum_of_nonneg (fun c _ => by positivity), Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hN0 : (Nc c : ℝ≥0∞) ≠ 0 := by exact_mod_cast (hNpos c).ne'
  rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hNpos c), ENNReal.ofReal_natCast, ← div_eq_mul_inv,
    ENNReal.eq_div_iff hN0 (ENNReal.natCast_ne_top _)]
  exact hpiece c

end MassDataMassesW.Abs
