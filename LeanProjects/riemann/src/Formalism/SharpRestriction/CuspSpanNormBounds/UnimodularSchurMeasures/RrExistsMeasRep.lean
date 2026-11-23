import Mathlib

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Set
open scoped ENNReal Pointwise InnerProductSpace

def rr_rep {G : Type*} [Mul G] (S D : Set G) (y : G) : G := by
  classical
  exact if h : ∃ γ ∈ S, γ * y ∈ D then h.choose * y else y

section Abs

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

structure rr_FD (μ : Measure G) (Γ : Subgroup G) (D : Set G) : Prop where
  meas : MeasurableSet D
  cov : ∀ y : G, ∃ γ ∈ (Γ : Set G), γ * y ∈ D
  disj : ∀ γ ∈ (Γ : Set G), γ ≠ 1 → μ ((fun y => γ * y) '' D ∩ D) = 0

def rr_N (Γ : Subgroup G) (D : Set G) : Set G :=
  {y | ∃ γ₁ ∈ Γ, ∃ γ₂ ∈ Γ, γ₁ ≠ γ₂ ∧ γ₁ * y ∈ D ∧ γ₂ * y ∈ D}

variable {μ : Measure G} {Γ : Subgroup G} {D : Set G}

private theorem mem_rr_N_iff {y : G} :
    y ∈ rr_N Γ D ↔ ∃ γ₁ ∈ Γ, ∃ γ₂ ∈ Γ, γ₁ ≠ γ₂ ∧ γ₁ * y ∈ D ∧ γ₂ * y ∈ D := Iff.rfl

private theorem rr_N_eq_iUnion_preimage_inter :
    rr_N Γ D = ⋃ a : Γ, ⋃ b : Γ, ⋃ (_ : a ≠ b),
      ((fun y => (a : G) * y) ⁻¹' D ∩ (fun y => (b : G) * y) ⁻¹' D) := by
  ext y
  simp only [mem_rr_N_iff, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨a, ha, b, hb, hab, h1, h2⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun e => hab (congrArg Subtype.val e), h1, h2⟩
  · rintro ⟨a, b, hab, h1, h2⟩
    exact ⟨a, a.2, b, b.2, fun e => hab (Subtype.ext e), h1, h2⟩

theorem rr_N_null [μ.IsMulLeftInvariant] [Countable Γ] (h : rr_FD μ Γ D) : μ (rr_N Γ D) = 0 := by
  rw [rr_N_eq_iUnion_preimage_inter]
  refine measure_iUnion_null fun a => measure_iUnion_null fun b => measure_iUnion_null fun hab => ?_
  have hne : (a : G) * (b : G)⁻¹ ≠ 1 := fun e => hab (Subtype.ext (mul_inv_eq_one.mp e))
  have hmem : (a : G) * (b : G)⁻¹ ∈ (Γ : Set G) := Γ.mul_mem a.2 (Γ.inv_mem b.2)
  have hsub : (fun y => (a : G) * y) ⁻¹' D ∩ (fun y => (b : G) * y) ⁻¹' D ⊆
      (fun y => (a : G) * y) ⁻¹' ((fun z => (a : G) * (b : G)⁻¹ * z) '' D ∩ D) := by
    rintro y ⟨h1, h2⟩
    refine ⟨⟨(b : G) * y, h2, ?_⟩, h1⟩
    simp only [mul_assoc, inv_mul_cancel_left]
  refine measure_mono_null hsub ?_
  rw [measure_preimage_mul]
  exact h.disj _ hmem hne

theorem rr_rep_spec (h : rr_FD μ Γ D) (y : G) :
    ∃ γ ∈ Γ, rr_rep (Γ : Set G) D y = γ * y ∧ γ * y ∈ D := by
  have hex : ∃ γ ∈ (Γ : Set G), γ * y ∈ D := h.cov y
  refine ⟨hex.choose, hex.choose_spec.1, ?_, hex.choose_spec.2⟩
  unfold rr_rep
  rw [dif_pos hex]

theorem rr_rep_eq (h : rr_FD μ Γ D) {y : G} (hy : y ∉ rr_N Γ D) {γ : G} (hγ : γ ∈ Γ) (hD : γ * y ∈ D) :
    rr_rep (Γ : Set G) D y = γ * y := by
  obtain ⟨γ₀, hγ₀, he, hD₀⟩ := rr_rep_spec h y
  rw [he]
  by_contra hne
  exact hy (mem_rr_N_iff.mpr ⟨γ₀, hγ₀, γ, hγ, fun e => hne (by rw [e]), hD₀, hD⟩)

theorem rr_N_smul {y c : G} (hc : c ∈ Γ) (hy : y ∉ rr_N Γ D) : c * y ∉ rr_N Γ D := by
  intro hcy
  obtain ⟨g1, hg1, g2, hg2, hne, h1, h2⟩ := mem_rr_N_iff.mp hcy
  refine hy (mem_rr_N_iff.mpr ⟨g1 * c, Γ.mul_mem hg1 hc, g2 * c, Γ.mul_mem hg2 hc,
    fun e => hne (mul_right_cancel e), ?_, ?_⟩)
  · rwa [mul_assoc]
  · rwa [mul_assoc]

theorem rr_rep_smul (h : rr_FD μ Γ D) {y c : G} (hc : c ∈ Γ) (hy : y ∉ rr_N Γ D) :
    rr_rep (Γ : Set G) D (c * y) = rr_rep (Γ : Set G) D y := by
  obtain ⟨γ, hγ, he, hD⟩ := rr_rep_spec h y
  have hD' : γ * c⁻¹ * (c * y) ∈ D := by
    rwa [mul_assoc, inv_mul_cancel_left]
  rw [rr_rep_eq h (rr_N_smul hc hy) (Γ.mul_mem hγ (Γ.inv_mem hc)) hD', he,
    mul_assoc, inv_mul_cancel_left]

theorem rr_exists_meas_rep [Countable Γ] (h : rr_FD μ Γ D) :
    ∃ r : G → G, Measurable r ∧ ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D := by
  classical
  haveI : Nonempty Γ := ⟨1⟩
  obtain ⟨e, he⟩ := exists_surjective_nat Γ
  have hex : ∀ y : G, ∃ n : ℕ, ((e n : Γ) : G) * y ∈ D := by
    intro y
    obtain ⟨γ, hγ, hD⟩ := h.cov y
    obtain ⟨n, hn⟩ := he ⟨γ, hγ⟩
    exact ⟨n, by rw [hn]; exact hD⟩
  refine ⟨fun y => ((e (Nat.find (hex y)) : Γ) : G) * y, ?_,
    fun y => ⟨_, (e (Nat.find (hex y))).2, rfl, Nat.find_spec (hex y)⟩⟩
  exact Measurable.find (f := fun n y => ((e n : Γ) : G) * y) (p := fun n y => ((e n : Γ) : G) * y ∈ D)
    (fun n => measurable_const_mul _) (fun n => measurable_const_mul _ h.meas) hex

theorem rr_FD_right [μ.IsMulRightInvariant] (h : rr_FD μ Γ D) (g : G) : rr_FD μ Γ ((fun x => x * g) ⁻¹' D) where
  meas := (measurable_mul_const g) h.meas
  cov := fun y => by
    obtain ⟨γ, hγ, hD⟩ := h.cov (y * g)
    exact ⟨γ, hγ, by simpa [mul_assoc] using hD⟩
  disj := fun γ hγ h1 => by
    have : (fun y => γ * y) '' ((fun x => x * g) ⁻¹' D) ∩ (fun x => x * g) ⁻¹' D ⊆
        (fun x => x * g) ⁻¹' ((fun y => γ * y) '' D ∩ D) := by
      rintro _ ⟨⟨y, hy, rfl⟩, h2⟩
      exact ⟨⟨y * g, hy, by simp [mul_assoc]⟩, h2⟩
    refine measure_mono_null this ?_
    rw [measure_preimage_mul_right]
    exact h.disj γ hγ h1

private theorem measurableSet_rr_N [Countable Γ] (hD : MeasurableSet D) :
    MeasurableSet (rr_N Γ D) := by
  rw [rr_N_eq_iUnion_preimage_inter]
  exact MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _ =>
    (measurable_const_mul (a : G) hD).inter (measurable_const_mul (b : G) hD)

theorem rr_isFD [μ.IsMulLeftInvariant] [Countable Γ] (h : rr_FD μ Γ D) : IsFundamentalDomain Γ D μ := by
  refine IsFundamentalDomain.mk'' h.meas.nullMeasurableSet
    (ae_of_all _ fun y => ?_) (fun g hg => ?_) (fun g => ?_)
  · obtain ⟨γ, hγ, hD⟩ := h.cov y
    exact ⟨⟨γ, hγ⟩, hD⟩
  · exact h.disj g g.2 (fun e => hg (Subtype.ext e))
  · exact (measurePreserving_mul_left μ (g : G)).quasiMeasurePreserving

end Abs

section Abs2

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
variable {μ : Measure G} {Γ : Subgroup G} {D : Set G}

theorem rr_rep_ae_eq [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Countable Γ] (h : rr_FD μ Γ D) {r : G → G}
    (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D) (g : G) :
    ∀ᵐ x ∂μ, rr_rep (Γ : Set G) D (x * g) = r (x * g) := by
  have hM : μ ((fun x => x * g) ⁻¹' rr_N Γ D) = 0 := by
    rw [measure_preimage_mul_right]; exact rr_N_null h
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) hM
  by_contra hxM
  obtain ⟨γ, hγ, hrx, hD⟩ := hr (x * g)
  exact hx (by rw [hrx]; exact rr_rep_eq (y := x * g) h hxM hγ hD)

private theorem eq_rr_rep_of_not_mem_rr_N (h : rr_FD μ Γ D) {r : G → G}
    (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D) {y : G} (hy : y ∉ rr_N Γ D) :
    r y = rr_rep (Γ : Set G) D y := by
  obtain ⟨γ, hγ, hry, hD⟩ := hr y
  rw [hry, rr_rep_eq h hy hγ hD]

private theorem rr_rep_eq_self_of_mem_of_not_mem_rr_N (h : rr_FD μ Γ D) {y : G}
    (hy : y ∉ rr_N Γ D) (hD : y ∈ D) : rr_rep (Γ : Set G) D y = y := by
  have e := rr_rep_eq h hy Γ.one_mem (by rwa [one_mul])
  rwa [one_mul] at e

theorem rr_meas_pre [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Countable Γ] (h : rr_FD μ Γ D) {r : G → G}
    (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D) (g : G) {A : Set G} (hA : MeasurableSet A) :
    μ ((fun x => r (x * g)) ⁻¹' A ∩ D) = μ (A ∩ D) := by
  obtain ⟨r₀, hr₀, hr₀rep⟩ := rr_exists_meas_rep h
  haveI : MeasurableConstSMul Γ G := ⟨fun c => measurable_const_mul (c : G)⟩
  haveI : SMulInvariantMeasure Γ G μ := ⟨fun c s _ => measure_preimage_mul μ (c : G) s⟩
  have hMmeas : MeasurableSet (rr_N Γ D) := measurableSet_rr_N h.meas
  have hN0 : μ ((fun x => x * g) ⁻¹' rr_N Γ D) = 0 := by
    rw [measure_preimage_mul_right]; exact rr_N_null h
  have hN : ∀ᵐ x ∂μ, x * g ∉ rr_N Γ D := by
    refine ae_iff.mpr (measure_mono_null (fun x hx => ?_) hN0)
    simp only [Set.mem_setOf_eq, not_not] at hx
    exact hx
  have hSmeas : MeasurableSet ((fun x => x * g) ⁻¹' ((rr_N Γ D)ᶜ ∩ r₀ ⁻¹' A)) :=
    measurable_mul_const g (hMmeas.compl.inter (hr₀ hA))
  have hinv : ∀ c : Γ, (fun x => c • x) ⁻¹' ((fun x => x * g) ⁻¹' ((rr_N Γ D)ᶜ ∩ r₀ ⁻¹' A)) = ((fun x => x * g) ⁻¹' ((rr_N Γ D)ᶜ ∩ r₀ ⁻¹' A)) := by
    intro c
    ext x
    show (c : G) * x * g ∉ rr_N Γ D ∧ r₀ ((c : G) * x * g) ∈ A ↔
      x * g ∉ rr_N Γ D ∧ r₀ (x * g) ∈ A
    rw [mul_assoc]
    constructor
    · rintro ⟨h1, h2⟩
      have hy : x * g ∉ rr_N Γ D := by
        have e := rr_N_smul (Γ.inv_mem c.2) h1
        rwa [inv_mul_cancel_left] at e
      refine ⟨hy, ?_⟩
      rwa [eq_rr_rep_of_not_mem_rr_N h hr₀rep h1, rr_rep_smul h c.2 hy,
        ← eq_rr_rep_of_not_mem_rr_N h hr₀rep hy] at h2
    · rintro ⟨h1, h2⟩
      have hy := rr_N_smul c.2 h1
      refine ⟨hy, ?_⟩
      rwa [eq_rr_rep_of_not_mem_rr_N h hr₀rep hy, rr_rep_smul h c.2 h1, ← eq_rr_rep_of_not_mem_rr_N h hr₀rep h1]
  have hfd : IsFundamentalDomain Γ D μ := (rr_isFD h)
  have hfd' : IsFundamentalDomain Γ ((fun x => x * g) ⁻¹' D) μ :=
    (rr_isFD ((rr_FD_right h) g))
  have key := hfd.measure_set_eq hfd' (A := ((fun x => x * g) ⁻¹' ((rr_N Γ D)ᶜ ∩ r₀ ⁻¹' A))) hSmeas hinv
  have e1 : μ ((fun x => r (x * g)) ⁻¹' A ∩ D) = μ (((fun x => x * g) ⁻¹' ((rr_N Γ D)ᶜ ∩ r₀ ⁻¹' A)) ∩ D) := by
    refine measure_congr (hN.mono fun x hx => propext ?_)
    have e : r (x * g) = r₀ (x * g) := by
      rw [eq_rr_rep_of_not_mem_rr_N h hr hx, eq_rr_rep_of_not_mem_rr_N h hr₀rep hx]
    show r (x * g) ∈ A ∧ x ∈ D ↔ (x * g ∉ rr_N Γ D ∧ r₀ (x * g) ∈ A) ∧ x ∈ D
    rw [e]
    exact ⟨fun ⟨h1, h2⟩ => ⟨⟨hx, h1⟩, h2⟩, fun ⟨⟨_, h1⟩, h2⟩ => ⟨h1, h2⟩⟩
  have e2 : μ (((fun x => x * g) ⁻¹' ((rr_N Γ D)ᶜ ∩ r₀ ⁻¹' A)) ∩ (fun x => x * g) ⁻¹' D) = μ ((fun x => x * g) ⁻¹' (A ∩ D)) := by
    refine measure_congr (hN.mono fun x hx => propext ?_)
    show (x * g ∉ rr_N Γ D ∧ r₀ (x * g) ∈ A) ∧ x * g ∈ D ↔ x * g ∈ A ∧ x * g ∈ D
    constructor
    · rintro ⟨⟨_, h1⟩, h2⟩
      refine ⟨?_, h2⟩
      rwa [eq_rr_rep_of_not_mem_rr_N h hr₀rep hx, rr_rep_eq_self_of_mem_of_not_mem_rr_N h hx h2] at h1
    · rintro ⟨h1, h2⟩
      refine ⟨⟨hx, ?_⟩, h2⟩
      rwa [eq_rr_rep_of_not_mem_rr_N h hr₀rep hx, rr_rep_eq_self_of_mem_of_not_mem_rr_N h hx h2]
  rw [e1, key, e2, measure_preimage_mul_right]

theorem rr_map [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Countable Γ] (h : rr_FD μ Γ D) (g : G) :
    AEMeasurable (fun x => rr_rep (Γ : Set G) D (x * g)) (μ.restrict D) ∧
      Measure.map (fun x => rr_rep (Γ : Set G) D (x * g)) (μ.restrict D) = μ.restrict D := by
  obtain ⟨r₀, hr₀, hr₀rep⟩ := rr_exists_meas_rep h
  have hae : AEMeasurable (fun x => rr_rep (Γ : Set G) D (x * g)) (μ.restrict D) :=
    ⟨fun x => r₀ (x * g), hr₀.comp (measurable_mul_const g),
      ae_restrict_of_ae (rr_rep_ae_eq h hr₀rep g)⟩
  refine ⟨hae, Measure.ext fun A hA => ?_⟩
  rw [Measure.map_apply_of_aemeasurable hae hA, Measure.restrict_apply' h.meas,
    Measure.restrict_apply' h.meas]
  exact rr_meas_pre h (rr_rep_spec h) g hA

theorem rr_rep_comp [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Countable Γ] (h : rr_FD μ Γ D) (g k : G) :
    ∀ᵐ x ∂μ, rr_rep (Γ : Set G) D (rr_rep (Γ : Set G) D (x * g) * k) = rr_rep (Γ : Set G) D (x * (g * k)) := by
  have hM : μ ((fun x => x * (g * k)) ⁻¹' rr_N Γ D) = 0 := by
    rw [measure_preimage_mul_right]; exact rr_N_null h
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) hM
  by_contra hxM
  obtain ⟨γ, hγ, he, -⟩ := rr_rep_spec h (x * g)
  refine hx ?_
  rw [he, show γ * (x * g) * k = γ * (x * (g * k)) by simp only [mul_assoc]]
  exact rr_rep_smul (y := x * (g * k)) h hγ hxM

theorem rr_rep_self [μ.IsMulLeftInvariant] [Countable Γ] (h : rr_FD μ Γ D) :
    ∀ᵐ x ∂μ.restrict D, rr_rep (Γ : Set G) D (x * 1) = x := by
  rw [ae_restrict_iff' h.meas, ae_iff]
  refine measure_mono_null (fun x hx => ?_) (rr_N_null h)
  by_contra hxM
  simp only [Set.mem_setOf_eq, _root_.not_imp] at hx
  obtain ⟨hxD, hne⟩ := hx
  apply hne
  rw [mul_one]
  have e := rr_rep_eq h hxM Γ.one_mem (by rwa [one_mul])
  rwa [one_mul] at e

def rr_IsReg (μ : Measure G) (Γ : Subgroup G) (D : Set G)
    (R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))) : Prop :=
  ∀ g F, ((R g F : Lp ℂ 2 (μ.restrict D)) : G → ℂ) =ᵐ[μ.restrict D]
    fun x => (F : G → ℂ) (rr_rep (Γ : Set G) D (x * g))

variable {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))}

theorem rr_norm [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Countable Γ] (h : rr_FD μ Γ D)
    (hR : rr_IsReg μ Γ D R) (g : G) (F : Lp ℂ 2 (μ.restrict D)) : ‖R g F‖ = ‖F‖ := by
  obtain ⟨hae, hmap⟩ := rr_map h g
  have hF : AEStronglyMeasurable (F : G → ℂ)
      (Measure.map (fun x => rr_rep (Γ : Set G) D (x * g)) (μ.restrict D)) := by
    rw [hmap]; exact Lp.aestronglyMeasurable F
  have key := eLpNorm_map_measure (p := 2) hF hae
  rw [hmap] at key
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (hR g F)]
  exact congrArg ENNReal.toReal key.symm

theorem rr_mul [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Countable Γ] (h : rr_FD μ Γ D)
    (hR : rr_IsReg μ Γ D R) (g k : G) : R (g * k) = R g ∘L R k := by
  ext F : 1
  refine Lp.ext ?_
  rw [ContinuousLinearMap.comp_apply]
  obtain ⟨hae, hmap⟩ := rr_map h g
  have h3 : (fun x => ((R k F : Lp ℂ 2 (μ.restrict D)) : G → ℂ) (rr_rep (Γ : Set G) D (x * g)))
      =ᵐ[μ.restrict D] fun x =>
        (F : G → ℂ) (rr_rep (Γ : Set G) D (rr_rep (Γ : Set G) D (x * g) * k)) :=
    ae_eq_comp (f := fun x => rr_rep (Γ : Set G) D (x * g))
      (g := ((R k F : Lp ℂ 2 (μ.restrict D)) : G → ℂ))
      (g' := fun y => (F : G → ℂ) (rr_rep (Γ : Set G) D (y * k))) hae (by rw [hmap]; exact hR k F)
  filter_upwards [hR (g * k) F, hR g (R k F), h3,
    ae_restrict_of_ae (s := D) (rr_rep_comp h g k)] with x e1 e2 e3 e4
  simp only [e1, e2, e3, e4]

theorem rr_one [μ.IsMulLeftInvariant] [Countable Γ] (h : rr_FD μ Γ D) (hR : rr_IsReg μ Γ D R) : R 1 = 1 := by
  ext F : 1
  refine Lp.ext ?_
  rw [ContinuousLinearMap.one_apply]
  filter_upwards [hR 1 F, rr_rep_self h] with x e1 e2
  simp only [e1, e2]

theorem rr_weak_meas [MeasurableMul₂ G] [SFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Countable Γ]
    (h : rr_FD μ Γ D) (hR : rr_IsReg μ Γ D R) (x y : Lp ℂ 2 (μ.restrict D)) :
    StronglyMeasurable fun g => ⟪x, R g y⟫_ℂ := by
  obtain ⟨r₀, hr₀, hr₀rep⟩ := rr_exists_meas_rep h
  have hΦ : StronglyMeasurable
      (fun p : G × G => ⟪(x : G → ℂ) p.2, (y : G → ℂ) (r₀ (p.2 * p.1))⟫_ℂ) :=
    ((Lp.stronglyMeasurable x).comp_measurable measurable_snd).inner
      ((Lp.stronglyMeasurable y).comp_measurable (hr₀.comp (measurable_snd.mul measurable_fst)))
  have hEq : (fun g => ⟪x, R g y⟫_ℂ) =
      fun g => ∫ z, ⟪(x : G → ℂ) z, (y : G → ℂ) (r₀ (z * g))⟫_ℂ ∂(μ.restrict D) := by
    funext g
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hR g y, ae_restrict_of_ae (s := D) (rr_rep_ae_eq h hr₀rep g)] with z e1 e2
    simp only [e1, e2]
  rw [hEq]
  exact hΦ.integral_prod_right'

end Abs2

end Formalism.MainNotions.LeviCoordinates

end
