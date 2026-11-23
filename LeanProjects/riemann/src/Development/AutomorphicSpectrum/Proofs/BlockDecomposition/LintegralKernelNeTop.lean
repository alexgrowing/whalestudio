import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotIntegralZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralTsumEnormNeTop

noncomputable section

open MeasureTheory Set Function PositivityTheory.Rg.Tf.Loc
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.TwUnfold

theorem lintegral_fd_le {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] {Γ : Subgroup G} [Countable Γ]
    {μ : Measure G} [μ.IsMulLeftInvariant] {Fd K : Set G} (hFd : IsFundamentalDomain Γ Fd μ) (hK : MeasurableSet K)
    (Ψ : G → ℝ≥0∞) (hinv : ∀ γ ∈ Γ, ∀ x, Ψ (γ * x) = Ψ x) (hsupp : ∀ x, Ψ x ≠ 0 → ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * k) :
    ∫⁻ x in Fd, Ψ x ∂μ ≤ ∫⁻ x in K, Ψ x ∂μ := by
  have hW : MeasurableSet (⋃ g : Γ, g • K) := MeasurableSet.iUnion fun g => hK.const_smul g
  have h1 : ∫⁻ x in Fd, Ψ x ∂μ = ∫⁻ x in Fd, (⋃ g : Γ, g • K).indicator Ψ x ∂μ := by
    refine lintegral_congr fun x => ?_
    by_cases hx : Ψ x = 0
    · by_cases hm : x ∈ ⋃ g : Γ, g • K
      · rw [indicator_of_mem hm]
      · rw [indicator_of_notMem hm, hx]
    · obtain ⟨γ, hγ, k, hk, rfl⟩ := hsupp x hx
      rw [indicator_of_mem]
      exact mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨k, hk, rfl⟩⟩
  rw [h1, setLIntegral_indicator hW, iUnion_inter, hFd.setLIntegral_eq_tsum' Ψ K]
  refine (lintegral_iUnion_le _ _).trans (ENNReal.tsum_le_tsum fun g => le_of_eq ?_)
  refine lintegral_congr fun x => ?_
  exact (hinv _ (g⁻¹ : Γ).2 x).symm

section Orbit

variable {G R : Type*} [Group G] [Group R]

theorem twConj_map_mul (ι : R →* G) (θ : Monoid.End G) (θR : Monoid.End R) (hθ : ∀ r, ι (θR r) = θ (ι r))
    (r d : R) (x : G) : twConj θ (ι r * x) (ι d) = twConj θ x (ι (twConj θR r d)) := by
  simp only [twConj, map_mul, map_inv, hθ]
  group

def repR (ι : R →* G) {S : Subgroup ι.range} (q : ι.range ⧸ S) : R := (q.out).2.choose

theorem map_repR (ι : R →* G) {S : Subgroup ι.range} (q : ι.range ⧸ S) : ι (repR ι q) = (q.out : G) :=
  (q.out).2.choose_spec

def orbPt (ι : R →* G) (θR : Monoid.End R) (δ : R) {S : Subgroup ι.range} (q : ι.range ⧸ S) : R :=
  twConj θR (repR ι q)⁻¹ δ

theorem twConj_out (ι : R →* G) (θ : Monoid.End G) (θR : Monoid.End R) (hθ : ∀ r, ι (θR r) = θ (ι r)) (δ : R)
    {S : Subgroup ι.range} (q : ι.range ⧸ S) (x : G) :
    twConj θ ((q.out : G)⁻¹ * x) (ι δ) = twConj θ x (ι (orbPt ι θR δ q)) := by
  rw [← map_repR ι q, ← map_inv, twConj_map_mul ι θ θR hθ]
  rfl

variable {ι : R →* G} {θR : Monoid.End R} {δ : R} {H : Subgroup G}

theorem orbPt_injective (hH : ∀ g, g ∈ H ↔ ∃ t, ι t = g ∧ twConj θR t δ = δ) :
    Injective (orbPt ι θR δ (S := H.subgroupOf ι.range)) := by
  intro q₁ q₂ h
  have hu : twConj θR ((repR ι q₂)⁻¹ * repR ι q₁) δ = δ := by
    simp only [orbPt, twConj, inv_inv, map_inv] at h
    simp only [twConj, map_mul, map_inv, mul_inv_rev, inv_inv]
    have : (repR ι q₁)⁻¹ * repR ι q₂ * δ * ((θR (repR ι q₂))⁻¹ * θR (repR ι q₁)) =
        (repR ι q₁)⁻¹ * (repR ι q₂ * δ * (θR (repR ι q₂))⁻¹) * θR (repR ι q₁) := by group
    rw [this, ← h]
    group
  have hm : (q₂.out)⁻¹ * q₁.out ∈ H.subgroupOf ι.range := by
    rw [Subgroup.mem_subgroupOf, hH]
    refine ⟨_, ?_, hu⟩
    simp [map_repR]
  have := QuotientGroup.eq.2 hm
  rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
  exact this.symm

theorem exists_orbPt (hι : Injective ι) (hH : ∀ g, g ∈ H ↔ ∃ t, ι t = g ∧ twConj θR t δ = δ) {d : R}
    (hd : TwConjugate θR δ d) : ∃ q : ι.range ⧸ H.subgroupOf ι.range, orbPt ι θR δ q = d := by
  obtain ⟨g, rfl⟩ := hd
  let γ : ι.range := ⟨ι g⁻¹, g⁻¹, rfl⟩
  refine ⟨(γ : ι.range ⧸ H.subgroupOf ι.range), ?_⟩
  set q : ι.range ⧸ H.subgroupOf ι.range := (γ : ι.range ⧸ H.subgroupOf ι.range) with hq
  have h1 : (q.out : ι.range ⧸ H.subgroupOf ι.range) = γ := QuotientGroup.out_eq' q
  have h2 := QuotientGroup.eq.1 h1
  rw [Subgroup.mem_subgroupOf, hH] at h2
  obtain ⟨t, ht, htδ⟩ := h2
  have h3 : t = (repR ι q)⁻¹ * g⁻¹ := hι (by
    rw [ht, map_mul, map_inv, map_repR]
    rfl)
  have h4 : (repR ι q)⁻¹ = t * g := by rw [h3]; group
  rw [orbPt, h4]
  exact twConj_mul_left θR δ htδ g

end Orbit

section Main

variable {G R C : Type*} [Group G] [Group R]
  {ι : R →* G} {θ : Monoid.End G} {θR : Monoid.End R} {cls : R → C} {rep : C → R}

def twPerm (θR : Monoid.End R) (r : R) : R ≃ R where
  toFun d := twConj θR r d
  invFun d := twConj θR r⁻¹ d
  left_inv d := by simp only [twConj, map_inv, inv_inv]; group
  right_inv d := by simp only [twConj, map_inv, inv_inv]; group

theorem cls_twConj (hcls : ∀ c d, cls d = c ↔ TwConjugate θR (rep c) d) (r d : R) :
    cls (twConj θR r d) = cls d := by
  obtain ⟨g, hg⟩ := (hcls (cls d) d).1 rfl
  refine (hcls _ _).2 ⟨g * r, ?_⟩
  generalize rep (cls d) = δ at hg ⊢
  rw [hg]
  simp only [twConj, map_mul]
  group

theorem cls_mem_of_ne {K : Set G} (hθ : ∀ r, ι (θR r) = θ (ι r))
    (hcls : ∀ c d, cls d = c ↔ TwConjugate θR (rep c) d) {χ φ : G → ℂ}
    (hχK : ∀ x, χ x ≠ 0 → ∃ r, ∃ k ∈ K, x = ι r * k) {x : G} {d : R} (h : χ x * φ (twConj θ x (ι d)) ≠ 0) :
    cls d ∈ cls '' {d | ∃ x ∈ K, φ (twConj θ x (ι d)) ≠ 0} := by
  obtain ⟨r, k, hk, rfl⟩ := hχK x (left_ne_zero_of_mul h)
  have h2 := right_ne_zero_of_mul h
  rw [twConj_map_mul ι θ θR hθ] at h2
  exact ⟨_, ⟨k, hk, h2⟩, cls_twConj hcls r d⟩

theorem kernel_decomp (hι : Injective ι) (hθ : ∀ r, ι (θR r) = θ (ι r))
    (hcls : ∀ c d, cls d = c ↔ TwConjugate θR (rep c) d) {H : C → Subgroup G}
    (hH : ∀ c g, g ∈ H c ↔ ∃ t, ι t = g ∧ twConj θR t (rep c) = rep c) {χ φ : G → ℂ}
    (hχi : ∀ r x, χ (ι r * x) = χ x) [TopologicalSpace G] [T1Space G]
    (x : G) (hfin : {d | φ (twConj θ x (ι d)) ≠ 0}.Finite) (T : Finset C)
    (hT : ∀ d, χ x * φ (twConj θ x (ι d)) ≠ 0 → cls d ∈ T) :
    χ x * ∑ᶠ d : R, φ (twConj θ x (ι d)) = ∑ c ∈ T, ∑' q : ι.range ⧸ (H c).subgroupOf ι.range,
      χ ((q.out : G)⁻¹ * x) * φ (twConj θ ((q.out : G)⁻¹ * x) (ι (rep c))) := by
  classical
  set A := hfin.toFinset with hA
  have hg : ∀ c (q : ι.range ⧸ (H c).subgroupOf ι.range), χ ((q.out : G)⁻¹ * x) *
      φ (twConj θ ((q.out : G)⁻¹ * x) (ι (rep c))) = χ x * φ (twConj θ x (ι (orbPt ι θR (rep c) q))) := by
    intro c q
    rw [twConj_out ι θ θR hθ]
    congr 1
    rw [← map_repR ι q, ← map_inv, hχi]
  have hc : ∀ c, ∑' q : ι.range ⧸ (H c).subgroupOf ι.range, χ ((q.out : G)⁻¹ * x) *
      φ (twConj θ ((q.out : G)⁻¹ * x) (ι (rep c))) =
        ∑ d ∈ A, if cls d = c then χ x * φ (twConj θ x (ι d)) else 0 := by
    intro c
    have hinj := orbPt_injective (ι := ι) (θR := θR) (δ := rep c) (H := H c) (hH c)
    have e1 : ∀ q : ι.range ⧸ (H c).subgroupOf ι.range, χ ((q.out : G)⁻¹ * x) *
        φ (twConj θ ((q.out : G)⁻¹ * x) (ι (rep c))) =
          (fun d => if cls d = c then χ x * φ (twConj θ x (ι d)) else 0) (orbPt ι θR (rep c) q) := by
      intro q
      have : cls (orbPt ι θR (rep c) q) = c := (hcls _ _).2 ⟨_, rfl⟩
      simp only [this, if_true]
      exact hg c q
    have hs : support (fun d => if cls d = c then χ x * φ (twConj θ x (ι d)) else 0) ⊆
        range (orbPt ι θR (rep c) (S := (H c).subgroupOf ι.range)) := by
      intro d hd
      have h1 : cls d = c := by
        by_contra h
        simp [h] at hd
      exact exists_orbPt hι (hH c) ((hcls _ _).1 h1)
    rw [tsum_congr e1, hinj.tsum_eq hs]
    refine tsum_eq_sum fun d hd => ?_
    have : φ (twConj θ x (ι d)) = 0 := by
      by_contra h
      exact hd (hfin.mem_toFinset.2 h)
    simp [this]
  simp_rw [hc]
  rw [Finset.sum_comm, finsum_eq_sum_of_support_subset (s := A) _ (fun d hd => hfin.mem_toFinset.2 hd), Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_ite_eq]
  by_cases h : χ x * φ (twConj θ x (ι d)) = 0
  · simp [h]
  · simp [hT d h]

theorem lintegral_kernel_ne_top [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [Countable R]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    (hθ : ∀ r, ι (θR r) = θ (ι r)) {Fd K : Set G} (hFd : IsFundamentalDomain ι.range Fd μ) (hK : IsCompact K)
    {χ φ : G → ℂ} (hχb : ∀ x, ‖χ x‖ ≤ 1) (hχi : ∀ r x, χ (ι r * x) = χ x)
    (hχK : ∀ x, χ x ≠ 0 → ∃ r, ∃ k ∈ K, x = ι r * k) {B : ℝ} (hφb : ∀ g, ‖φ g‖ ≤ B)
    (hfin : {d | ∃ x ∈ K, φ (twConj θ x (ι d)) ≠ 0}.Finite) :
    ∫⁻ x in Fd, ∑' d : R, ‖χ x * φ (twConj θ x (ι d))‖ₑ ∂μ ≠ ∞ := by
  classical
  haveI : Countable ι.range := (Set.countable_range ι).to_subtype
  haveI : MeasurableMul G := inferInstance
  set Ψ : G → ℝ≥0∞ := fun x => ∑' d : R, ‖χ x * φ (twConj θ x (ι d))‖ₑ with hΨ
  have hinv : ∀ γ ∈ ι.range, ∀ x, Ψ (γ * x) = Ψ x := by
    rintro _ ⟨r, rfl⟩ x
    simp only [hΨ, hχi]
    rw [← (twPerm θR r).tsum_eq (fun d => ‖χ x * φ (twConj θ x (ι d))‖ₑ)]
    refine tsum_congr fun d => ?_
    rw [twConj_map_mul ι θ θR hθ]
    rfl
  have hsupp : ∀ x, Ψ x ≠ 0 → ∃ γ ∈ ι.range, ∃ k ∈ K, x = γ * k := by
    intro x hx
    have : χ x ≠ 0 := by
      intro h
      exact hx (by simp [hΨ, h])
    obtain ⟨r, k, hk, rfl⟩ := hχK x this
    exact ⟨_, ⟨r, rfl⟩, k, hk, rfl⟩
  have hB : ∀ k ∈ K, Ψ k ≤ hfin.toFinset.card • ENNReal.ofReal B := by
    intro k hk
    have h1 : Ψ k = ∑ d ∈ hfin.toFinset, ‖χ k * φ (twConj θ k (ι d))‖ₑ := by
      refine tsum_eq_sum fun d hd => ?_
      have : φ (twConj θ k (ι d)) = 0 := by
        by_contra h
        exact hd (hfin.mem_toFinset.2 ⟨k, hk, h⟩)
      simp [this]
    rw [h1]
    refine Finset.sum_le_card_nsmul _ _ _ fun d _ => ?_
    rw [← ofReal_norm_eq_enorm, norm_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ‖χ k‖ * ‖φ (twConj θ k (ι d))‖ ≤ 1 * B :=
          mul_le_mul (hχb k) (hφb _) (norm_nonneg _) zero_le_one
      _ = B := one_mul B
  refine ne_of_lt (lt_of_le_of_lt (lintegral_fd_le hFd hK.measurableSet Ψ hinv hsupp) ?_)
  refine lt_of_le_of_lt (setLIntegral_mono' hK.measurableSet hB) ?_
  rw [setLIntegral_const]
  exact ENNReal.mul_lt_top (by simp [ENNReal.mul_lt_top]) hK.measure_lt_top

theorem unfold_abs [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [Countable R] {μ : Measure G} [μ.IsMulLeftInvariant] [SFinite μ]
    [IsFiniteMeasureOnCompacts μ] (hι : Injective ι) [DiscreteTopology ι.range] (hθ : ∀ r, ι (θR r) = θ (ι r))
    {Fd : Set G} (hFd : IsFundamentalDomain ι.range Fd μ)
    (hcls : ∀ c d, cls d = c ↔ TwConjugate θR (rep c) d) {H : C → Subgroup G}
    (hH : ∀ c g, g ∈ H c ↔ ∃ t, ι t = g ∧ twConj θR t (rep c) = rep c) {χ φ : G → ℂ} (hχm : Measurable χ)
    (hχb : ∀ x, ‖χ x‖ ≤ 1) (hχi : ∀ r x, χ (ι r * x) = χ x) {K : Set G} (hK : IsCompact K)
    (hχK : ∀ x, χ x ≠ 0 → ∃ r, ∃ k ∈ K, x = ι r * k) (hφm : ∀ d, Measurable fun x => φ (twConj θ x (ι d)))
    {B : ℝ} (hφb : ∀ g, ‖φ g‖ ≤ B)
    (hfin : ∀ L : Set G, IsCompact L → {d | ∃ x ∈ L, φ (twConj θ x (ι d)) ≠ 0}.Finite) :
    (support fun c => quotIntegral μ (H c) Measure.count fun x => χ x * φ (twConj θ x (ι (rep c)))).Finite ∧
      ∫ x in Fd, χ x * ∑ᶠ d : R, φ (twConj θ x (ι d)) ∂μ =
        ∑ᶠ c, quotIntegral μ (H c) Measure.count fun x => χ x * φ (twConj θ x (ι (rep c))) := by
  classical
  haveI : Countable ι.range := (Set.countable_range ι).to_subtype
  have hfinK := hfin K hK
  set T : Finset C := (hfinK.image cls).toFinset with hTdef
  have hT : ∀ (x : G) (d : R), χ x * φ (twConj θ x (ι d)) ≠ 0 → cls d ∈ T := fun x d h =>
    (hfinK.image cls).mem_toFinset.2 (cls_mem_of_ne hθ hcls hχK h)
  have hle : ∀ c, H c ≤ ι.range := fun c g hg => by
    obtain ⟨t, rfl, -⟩ := (hH c g).1 hg
    exact ⟨t, rfl⟩
  have hdisc : ∀ c, DiscreteTopology (H c) := fun c =>
    DiscreteTopology.of_subset (s := (ι.range : Set G)) inferInstance (hle c)
  have hFm : ∀ c, Measurable fun x => χ x * φ (twConj θ x (ι (rep c))) := fun c => hχm.mul (hφm _)
  have hFH : ∀ c, ∀ h ∈ H c, ∀ g, χ (h * g) * φ (twConj θ (h * g) (ι (rep c))) =
      χ g * φ (twConj θ g (ι (rep c))) := by
    intro c h hh g
    obtain ⟨t, rfl, ht⟩ := (hH c h).1 hh
    rw [hχi, twConj_map_mul ι θ θR hθ, ht]
  have hsing : ∀ x, {d | φ (twConj θ x (ι d)) ≠ 0}.Finite := fun x =>
    (hfin {x} isCompact_singleton).subset fun d hd => ⟨x, rfl, hd⟩
  have hΨ := lintegral_kernel_ne_top (μ := μ) hθ hFd hK hχb hχi hχK hφb hfinK
  have hint : ∀ c, ∫⁻ x in Fd, ∑' q : ι.range ⧸ (H c).subgroupOf ι.range,
      ‖χ ((q.out : G)⁻¹ * x) * φ (twConj θ ((q.out : G)⁻¹ * x) (ι (rep c)))‖ₑ ∂μ ≠ ∞ := by
    intro c
    refine ne_top_of_le_ne_top hΨ (lintegral_mono fun x => ?_)
    have e1 : ∀ q : ι.range ⧸ (H c).subgroupOf ι.range,
        ‖χ ((q.out : G)⁻¹ * x) * φ (twConj θ ((q.out : G)⁻¹ * x) (ι (rep c)))‖ₑ =
          (fun d => ‖χ x * φ (twConj θ x (ι d))‖ₑ) (orbPt ι θR (rep c) q) := by
      intro q
      simp only
      rw [twConj_out ι θ θR hθ, ← map_repR ι q, ← map_inv, hχi]
    simp_rw [e1]
    exact ENNReal.tsum_comp_le_tsum_of_injective (orbPt_injective (hH c)) _
  have hterm : ∀ c, (quotIntegral μ (H c) Measure.count fun x => χ x * φ (twConj θ x (ι (rep c)))) =
      ∫ x in Fd, ∑' q : ι.range ⧸ (H c).subgroupOf ι.range,
        χ ((q.out : G)⁻¹ * x) * φ (twConj θ ((q.out : G)⁻¹ * x) (ι (rep c))) ∂μ := fun c => by
    haveI := hdisc c
    exact GlobalTheory.CompanionTheory.QuotUnfold.quotIntegral_unfold (hle c) hFd (hFm c) (hFH c) (hint c)
  have hzero : ∀ c, c ∉ T → (quotIntegral μ (H c) Measure.count fun x => χ x * φ (twConj θ x (ι (rep c)))) = 0 := by
    intro c hc
    have : (fun x => χ x * φ (twConj θ x (ι (rep c)))) = fun _ => 0 := by
      funext x
      by_contra h
      refine hc ?_
      have := hT x (rep c) h
      rwa [((hcls c (rep c)).2 ⟨1, by simp [twConj]⟩)] at this
    rw [this]
    unfold quotIntegral
    split_ifs <;> simp
  have hsub : (support fun c => quotIntegral μ (H c) Measure.count fun x => χ x * φ (twConj θ x (ι (rep c)))) ⊆ T :=
    fun c hc => by
      by_contra h
      exact hc (hzero c h)
  refine ⟨T.finite_toSet.subset hsub, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsub]
  have hdec : ∀ x, χ x * ∑ᶠ d : R, φ (twConj θ x (ι d)) = ∑ c ∈ T, ∑' q : ι.range ⧸ (H c).subgroupOf ι.range,
      χ ((q.out : G)⁻¹ * x) * φ (twConj θ ((q.out : G)⁻¹ * x) (ι (rep c))) := fun x =>
    kernel_decomp hι hθ hcls hH hχi x (hsing x) T (hT x)
  simp_rw [hdec]
  rw [integral_finset_sum]
  · exact Finset.sum_congr rfl fun c _ => (hterm c).symm
  · intro c _
    haveI := hdisc c
    exact GlobalTheory.CompanionTheory.QuotUnfold.integrableOn_unfold (hFm c) (hint c)

end Main

end GlobalTheory.CompanionTheory.TwUnfold

end
