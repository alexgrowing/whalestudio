import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Two

open MeasureTheory
open scoped Pointwise ENNReal

def IsAv {B G : Type} [Group B] [TopologicalSpace B] [MeasurableSpace B] [Mul G] (Γ : Subgroup B) (ι : B → G) (f c : G → ℂ) : Prop :=
  ∀ (μ : Measure B) (𝓕 : Set B), μ.IsHaarMeasure → IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → ∀ h, c h = ∫ u in 𝓕, f (ι u * h) ∂μ

structure Lat {B : Type} [Group B] [TopologicalSpace B] (Γ : Subgroup B) : Prop where
  cnt : Countable Γ
  disc : DiscreteTopology Γ
  cov : ∃ C : Set B, IsCompact C ∧ ∀ u, ∃ γ ∈ Γ, γ * u ∈ C

section One

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G}

theorem fd_fin [Countable Γ] {C : Set G} (hC : IsCompact C) [T2Space G] (hc : ∀ u, ∃ γ ∈ Γ, γ * u ∈ C) (μ : Measure G)
    [μ.IsHaarMeasure] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ) : μ 𝓕 < ⊤ := by
  calc μ 𝓕 ≤ μ (⋃ γ : Γ, γ • C ∩ 𝓕) := measure_mono fun u hu => by
        obtain ⟨γ, h1, h2⟩ := hc u
        exact Set.mem_iUnion.2 ⟨⟨γ, h1⟩⁻¹, Set.mem_smul_set_iff_inv_smul_mem.2 (by simpa using h2), hu⟩
    _ ≤ ∑' γ : Γ, μ (γ • C ∩ 𝓕) := measure_iUnion_le _
    _ = μ C := (h.measure_eq_tsum C).symm
    _ < ⊤ := hC.measure_lt_top

variable [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]

omit [T2Space G] in
theorem right_of_fd [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] {𝓕 : Set G}
    (hm : MeasurableSet 𝓕) (h : IsFundamentalDomain Γ 𝓕 μ) (hf : μ 𝓕 < ⊤) : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have e := Measure.isMulLeftInvariant_eq_smul (μ.map (· * g)) μ
  set c := Measure.haarScalarFactor (μ.map (· * g)) μ
  have q : Measure.QuasiMeasurePreserving (· * g) μ μ :=
    ⟨measurable_mul_const g, by rw [e]; exact Measure.smul_absolutelyContinuous⟩
  have h2 : IsFundamentalDomain Γ ((Equiv.mulRight g) ⁻¹' 𝓕) μ :=
    h.preimage_of_equiv q Function.bijective_id fun γ x => by
      change _ * x * g = _ * (x * g)
      rw [mul_assoc]; rfl
  have h3 : μ ((· * g) ⁻¹' 𝓕) = μ 𝓕 := h2.measure_eq h
  rw [← Measure.map_apply (measurable_mul_const g) hm, e, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
  have h4 : (c : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj (h.measure_ne_zero (NeZero.ne μ)) hf.ne).1 (h3.trans (one_mul _).symm)
  rw [e, ENNReal.coe_eq_one.1 h4, one_smul]

theorem Lat.right (L : Lat Γ) (μ : Measure G) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  have := L.cnt
  have := L.disc
  obtain ⟨C, hC, hc⟩ := L.cov
  obtain ⟨𝓕, hm, h⟩ := GlobalTheory.FundDomDiscrete.exists_measurable_section Γ
  have h' : IsFundamentalDomain Γ 𝓕 μ := .mk' hm.nullMeasurableSet h
  exact right_of_fd μ hm h' (fd_fin hC hc μ h')

theorem Lat.pair (L : Lat Γ) : ∃ (μ : Measure G) (𝓕 : Set G), μ.IsHaarMeasure ∧ MeasurableSet 𝓕 ∧
    (∀ x, ∃! γ : Γ, γ • x ∈ 𝓕) ∧ μ 𝓕 = 1 := by
  have := L.cnt
  have := L.disc
  obtain ⟨C, hC, hc⟩ := L.cov
  obtain ⟨𝓕, hm, h⟩ := GlobalTheory.FundDomDiscrete.exists_measurable_section Γ
  let μ : Measure G := Measure.haar
  have h' : IsFundamentalDomain Γ 𝓕 μ := .mk' hm.nullMeasurableSet h
  have h0 := h'.measure_ne_zero (NeZero.ne μ)
  have h1 := (fd_fin hC hc μ h').ne
  exact ⟨(μ 𝓕)⁻¹ • μ, 𝓕, Measure.IsHaarMeasure.smul μ (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0), hm, h,
    by rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 h1]⟩

omit [T2Space G] in
theorem int_indep [Countable Γ] {μ μ' : Measure G} [μ.IsHaarMeasure] [μ'.IsHaarMeasure] {𝓕 𝓕' : Set G}
    (h : IsFundamentalDomain Γ 𝓕 μ) (h' : IsFundamentalDomain Γ 𝓕' μ') (h1 : μ 𝓕 = 1) (h1' : μ' 𝓕' = 1) {f : G → ℂ}
    (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) : ∫ u in 𝓕, f u ∂μ = ∫ u in 𝓕', f u ∂μ' := by
  have e := Measure.isMulLeftInvariant_eq_smul μ μ'
  set c := Measure.haarScalarFactor μ μ'
  have h2 : IsFundamentalDomain Γ 𝓕' μ := h'.mono (by rw [e]; exact Measure.smul_absolutelyContinuous)
  have h3 := h.measure_eq h2
  rw [h1, e, Measure.smul_apply, h1', ENNReal.smul_def, smul_eq_mul, mul_one] at h3
  have h4 : μ = μ' := by rw [e, ENNReal.coe_eq_one.1 h3.symm, one_smul]
  subst h4
  exact h.setIntegral_eq h2 fun γ x => hf γ γ.2 x

variable {H : Type} [Group H] {ι : G →* H} {f c c' : H → ℂ}

theorem Lat.isAv_ex (L : Lat Γ) (hf : ∀ γ ∈ Γ, ∀ x, f (ι γ * x) = f x) : ∃ c, IsAv Γ ι f c := by
  have := L.cnt
  obtain ⟨μ, 𝓕, h1, h2, h3, h4⟩ := L.pair
  exact ⟨fun h => ∫ u in 𝓕, f (ι u * h) ∂μ, fun μ' 𝓕' a b d h =>
    int_indep (.mk' h2.nullMeasurableSet h3) b h4 d fun γ hγ x => by rw [map_mul, mul_assoc, hf γ hγ]⟩

theorem Lat.isAv_uniq (L : Lat Γ) {ι : G → H} (h : IsAv Γ ι f c) (h' : IsAv Γ ι f c') : c = c' := by
  have := L.cnt
  obtain ⟨μ, 𝓕, h1, h2, h3, h4⟩ := L.pair
  funext x
  rw [h μ 𝓕 h1 (.mk' h2.nullMeasurableSet h3) h4, h' μ 𝓕 h1 (.mk' h2.nullMeasurableSet h3) h4]

theorem Lat.isAv_prob (L : Lat Γ) : ∃ lam : Measure G, IsProbabilityMeasure lam ∧
    ∀ (ι : G → H) (f c : H → ℂ), IsAv Γ ι f c → ∀ h, c h = ∫ u, f (ι u * h) ∂lam := by
  have := L.cnt
  obtain ⟨μ, 𝓕, h1, h2, h3, h4⟩ := L.pair
  exact ⟨μ.restrict 𝓕, ⟨by simpa using h4⟩, fun ι f c h => h μ 𝓕 h1 (.mk' h2.nullMeasurableSet h3) h4⟩

theorem IsAv.conj (L : Lat Γ) (h : IsAv Γ ι f c) (e : G ≃ₜ* G) (he : ∀ x, e x ∈ Γ ↔ x ∈ Γ) {γ : H}
    (hγ : ∀ u, ι u * γ = γ * ι (e u)) (hf : ∀ x, f (γ * x) = f x) (x : H) : c (γ * x) = c x := by
  have := L.cnt
  obtain ⟨μ, 𝓕, h1, h2, h3, h4⟩ := L.pair
  have hm : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have h5 : ∀ y, ∃! g : Γ, g • y ∈ e ⁻¹' 𝓕 := fun y => by
    obtain ⟨g, a, b⟩ := h3 (e y)
    refine ⟨⟨e.symm g, (he _).1 (by simpa using g.2)⟩, by simpa [Subgroup.smul_def] using a, fun g' hg' => ?_⟩
    have := b ⟨e g', (he _).2 g'.2⟩ (by simpa [Subgroup.smul_def] using hg')
    exact Subtype.ext (by simp [← this])
  have hm' : Measurable e.symm := e.symm.continuous.measurable
  have h6 : μ.map e.symm (e ⁻¹' 𝓕) = 1 := by
    rw [Measure.map_apply hm' (hm.measurable h2), ← h4]
    congr 1
    ext y; simp
  rw [h (μ.map e.symm) (e ⁻¹' 𝓕) inferInstance (.mk' (hm.measurable h2).nullMeasurableSet h5) h6,
    h μ 𝓕 h1 (.mk' h2.nullMeasurableSet h3) h4,
    (show MeasurableEmbedding e.symm from e.symm.toHomeomorph.measurableEmbedding).setIntegral_map]
  congr 1
  · congr 1
    ext y; simp
  · funext y
    rw [← mul_assoc, hγ, mul_assoc, hf, e.apply_symm_apply]

theorem Lat.bound [TopologicalSpace H] [IsTopologicalGroup H] (L : Lat Γ) (hι : Continuous ι) (hc : Continuous f)
    (hf : ∀ γ ∈ Γ, ∀ x, f (ι γ * x) = f x) {K : Set H} (hK : IsCompact K) : ∃ M, ∀ u, ∀ x ∈ K, ‖f (ι u * x)‖ ≤ M := by
  obtain ⟨C, hC, hcov⟩ := L.cov
  obtain ⟨M, hM⟩ := ((hC.image hι).mul hK).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨M, fun u x hx => ?_⟩
  obtain ⟨γ, h1, h2⟩ := hcov u
  rw [← hf γ h1, ← mul_assoc, ← map_mul]
  exact hM _ (Set.mul_mem_mul ⟨_, h2, rfl⟩ hx)

theorem IsAv.cont [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [FirstCountableTopology H] (L : Lat Γ)
    (h : IsAv Γ ι f c) (hι : Continuous ι) (hc : Continuous f) (hf : ∀ γ ∈ Γ, ∀ x, f (ι γ * x) = f x) : Continuous c := by
  obtain ⟨lam, hl, h2⟩ := L.isAv_prob (H := H)
  rw [funext (h2 ι f c h)]
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨K, hK, hx⟩ := exists_compact_mem_nhds x
  obtain ⟨M, hM⟩ := L.bound hι hc hf hK
  exact continuousAt_of_dominated (bound := fun _ => M) (.of_forall fun y => Continuous.aestronglyMeasurable (by fun_prop))
    (Filter.eventually_of_mem hx fun y hy => .of_forall fun u => hM u y hy) (integrable_const M)
    (.of_forall fun u => Continuous.continuousAt (by fun_prop))

end One

structure Semi {S A B : Type} [Group S] [Group A] [Group B] [TopologicalSpace S] [TopologicalSpace A] [TopologicalSpace B]
    (Γ : Subgroup S) (ΓA : Subgroup A) (ΓB : Subgroup B) (j : A →* S) (ι : B →* S) (p : S → A) (π : S →* B) : Prop where
  cj : Continuous j
  cι : Continuous ι
  cp : Continuous p
  cπ : Continuous π
  inj : Function.Injective j
  dec : ∀ s, j (p s) * ι (π s) = s
  πj : ∀ a, π (j a) = 1
  πι : ∀ b, π (ι b) = b
  hA : ∀ a, j a ∈ Γ ↔ a ∈ ΓA
  hB : ∀ b ∈ ΓB, ι b ∈ Γ
  hπ : ∀ s ∈ Γ, π s ∈ ΓB

section Two

variable {S A B : Type} [Group S] [Group A] [Group B] [TopologicalSpace S] [TopologicalSpace A] [TopologicalSpace B]
  {Γ : Subgroup S} {ΓA : Subgroup A} {ΓB : Subgroup B} {j : A →* S} {ι : B →* S} {p : S → A} {π : S →* B}

theorem Semi.p_mul (h : Semi Γ ΓA ΓB j ι p π) (a : A) (s : S) : p (j a * s) = a * p s := by
  have := h.dec (j a * s)
  rw [map_mul, h.πj, one_mul] at this
  refine h.inj (mul_right_cancel (b := ι (π s)) ?_)
  rw [this, map_mul, mul_assoc, h.dec]

theorem Semi.p_ι (h : Semi Γ ΓA ΓB j ι p π) (b : B) : p (ι b) = 1 := by
  have := h.dec (ι b)
  rw [h.πι] at this
  exact h.inj (by simpa using this)

theorem Semi.lat [IsTopologicalGroup S] (h : Semi Γ ΓA ΓB j ι p π) (LA : Lat ΓA) (LB : Lat ΓB) (hc : Countable Γ)
    (hd : DiscreteTopology Γ) : Lat Γ := by
  obtain ⟨CA, a1, a2⟩ := LA.cov
  obtain ⟨CB, b1, b2⟩ := LB.cov
  refine ⟨hc, hd, _, (a1.image h.cj).mul (b1.image h.cι), fun s => ?_⟩
  obtain ⟨β, h1, h2⟩ := b2 (π s)
  obtain ⟨α, h3, h4⟩ := a2 (p (ι β * s))
  refine ⟨j α * ι β, mul_mem ((h.hA _).2 h3) (h.hB _ h1), ?_⟩
  rw [← h.dec (j α * ι β * s)]
  refine Set.mul_mem_mul ⟨_, ?_, rfl⟩ ⟨_, ?_, rfl⟩
  · rwa [mul_assoc, h.p_mul]
  · rwa [map_mul, map_mul, h.πj, h.πι, one_mul]

variable [IsTopologicalGroup S] [IsTopologicalGroup A] [IsTopologicalGroup B] [MeasurableSpace S] [MeasurableSpace A]
  [MeasurableSpace B] [BorelSpace S] [BorelSpace A] [BorelSpace B] [LocallyCompactSpace S] [LocallyCompactSpace A]
  [LocallyCompactSpace B] [SecondCountableTopology S] [SecondCountableTopology A] [SecondCountableTopology B]
  [T2Space S] [T2Space A] [T2Space B]

theorem Semi.stage (h : Semi Γ ΓA ΓB j ι p π) (L : Lat Γ) (LA : Lat ΓA) (LB : Lat ΓB) {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] {inc : S →* G} (hi : Continuous inc) {f cA c : G → ℂ} (hc : Continuous f)
    (hf : ∀ γ ∈ Γ, ∀ x, f (inc γ * x) = f x) (h1 : IsAv ΓA (fun a => inc (j a)) f cA) (h2 : IsAv ΓB (fun b => inc (ι b)) cA c) :
    IsAv Γ inc f c := by
  have := L.cnt
  have := LA.cnt
  have := LB.cnt
  obtain ⟨μA, 𝓐, a1, a2, a3, a4⟩ := LA.pair
  obtain ⟨μB, 𝓑, b1, b2, b3, b4⟩ := LB.pair
  have := LA.right μA
  have := LB.right μB
  have cj := h.cj
  have cι := h.cι
  have cp := h.cp
  have cπ := h.cπ
  let e : B × A ≃ₜ S :=
    { toFun := fun x => j x.2 * ι x.1
      invFun := fun s => (π s, p s)
      left_inv := fun x => by simp [h.πj, h.πι, h.p_mul, h.p_ι]
      right_inv := h.dec
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hm := e.measurableEmbedding
  let ν : Measure S := (μB.prod μA).map e
  have : ν.IsMulRightInvariant := ⟨fun s => by
    have m1 : MeasurePreserving (fun x : B × A => (x.1 * π s, x.2 * p (ι x.1 * j (p s) * (ι x.1)⁻¹))) (μB.prod μA) (μB.prod μA) :=
      (measurePreserving_mul_right μB (π s)).skew_product (g := fun b a => a * p (ι b * j (p s) * (ι b)⁻¹))
        (Continuous.measurable (by fun_prop)) (.of_forall fun b => map_mul_right_eq_self μA _)
    rw [Measure.map_map (measurable_mul_const s) hm.measurable]
    conv_rhs => rw [show ν = (μB.prod μA).map e from rfl, ← m1.map_eq, Measure.map_map hm.measurable m1.measurable]
    congr 1
    funext x
    have e1 := h.dec (ι x.1 * j (p s) * (ι x.1)⁻¹)
    rw [map_mul π, map_mul π, map_inv, h.πj, mul_one, mul_inv_cancel, map_one, mul_one] at e1
    change j x.2 * ι x.1 * s = j (x.2 * _) * ι (x.1 * π s)
    rw [map_mul, map_mul, e1]
    conv_lhs => rw [← h.dec s]
    group⟩
  have : IsFiniteMeasureOnCompacts ν := Measure.IsFiniteMeasureOnCompacts.map _ e
  have : ν.IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective
  have hinv : ν.inv.IsHaarMeasure := {}
  have := L.right ν.inv
  have : ν.IsMulLeftInvariant := by rw [← Measure.inv_inv ν]; infer_instance
  have hν : ν.IsHaarMeasure := {}
  have hF : MeasurableSet (e.symm ⁻¹' 𝓑 ×ˢ 𝓐) := e.symm.continuous.measurable (b2.prod a2)
  have hpre : e ⁻¹' (e.symm ⁻¹' 𝓑 ×ˢ 𝓐) = 𝓑 ×ˢ 𝓐 := by ext x; simp
  have hfd : IsFundamentalDomain Γ (e.symm ⁻¹' 𝓑 ×ˢ 𝓐) ν := .mk' hF.nullMeasurableSet fun s => by
    obtain ⟨β, h3, h4⟩ := b3 (π s)
    obtain ⟨α, h5, h6⟩ := a3 (p (ι β * s))
    refine ⟨⟨j α * ι β, mul_mem ((h.hA _).2 α.2) (h.hB _ β.2)⟩, ⟨?_, ?_⟩, fun γ hγ => ?_⟩
    · change π (j α * ι β * s) ∈ 𝓑
      rwa [map_mul, map_mul, h.πj, h.πι, one_mul]
    · change p (j α * ι β * s) ∈ 𝓐
      rwa [mul_assoc, h.p_mul]
    · have e1 := congrArg Subtype.val (h4 ⟨π γ, h.hπ _ γ.2⟩ (by
        have : π (γ * s) ∈ 𝓑 := hγ.1
        rwa [map_mul] at this))
      have e2 : j (p γ) * ι β = γ := by rw [← e1]; exact h.dec _
      have e3 := congrArg Subtype.val (h6 ⟨p γ, (h.hA _).1 (by
        rw [eq_mul_inv_of_mul_eq e2]; exact mul_mem γ.2 (inv_mem (h.hB _ β.2)))⟩ (by
          have : p (γ * s) ∈ 𝓐 := hγ.2
          rwa [← e2, mul_assoc, h.p_mul] at this))
      exact Subtype.ext (by rw [← e2]; exact congrArg (fun z => j z * ι β) e3)
  have hν1 : ν (e.symm ⁻¹' 𝓑 ×ˢ 𝓐) = 1 := by
    rw [Measure.map_apply hm.measurable hF, hpre, Measure.prod_prod, a4, b4, mul_one]
  intro μ 𝓕 c1 c2 c3 x
  obtain ⟨M, hM⟩ := L.bound hi hc hf (isCompact_singleton (x := x))
  rw [int_indep c2 hfd c3 hν1 (f := fun u => f (inc u * x)) fun γ hγ y => by rw [map_mul, mul_assoc, hf γ hγ],
    hm.setIntegral_map, hpre, setIntegral_prod, h2 μB 𝓑 b1 (.mk' b2.nullMeasurableSet b3) b4]
  · congr 1
    funext b
    rw [h1 μA 𝓐 a1 (.mk' a2.nullMeasurableSet a3) a4]
    congr 1
    funext a
    rw [← mul_assoc, ← map_mul]; rfl
  · exact Measure.integrableOn_of_bounded (M := M) (by rw [Measure.prod_prod, a4, b4]; simp)
      (Continuous.aestronglyMeasurable (by fun_prop)) (.of_forall fun y => hM _ _ rfl)

end Two

end PositivityTheory.ThKEnd.Two

end
