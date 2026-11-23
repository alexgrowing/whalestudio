import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
import GroundTheory.AutomorphicForms.LocallyProfinite

open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob

noncomputable section

namespace GlobalTheory.CompanionTheory.FrobHaarR

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem exists_open_left_stab {F : G → ℂ} (hF : F ∈ SB G) :
    ∃ K : OpenSubgroup G, ∀ k ∈ K, ∀ x, F (k * x) = F x := by
  let K : Subgroup G :=
    { carrier := {k | ∀ g, F (k * g) = F g}
      one_mem' := by intro g; simp
      mul_mem' := by
        intro a b ha hb g
        rw [mul_assoc, ha, hb]
      inv_mem' := by
        intro a ha g
        have := ha (a⁻¹ * g)
        simpa using this.symm }
  have h1 : ∀ᶠ k in nhds (1 : G), ∀ g ∈ tsupport F, F (k * g) = F g := by
    apply IsCompact.eventually_forall_of_forall_eventually hF.2
    intro g _
    have a1 : IsLocallyConstant (fun z : G × G => F (z.1 * z.2)) :=
      hF.1.comp_continuous (by fun_prop)
    have a2 : IsLocallyConstant (fun z : G × G => F z.2) :=
      hF.1.comp_continuous (by fun_prop)
    filter_upwards [a1.eventually_eq (1, g), a2.eventually_eq (1, g)] with z hz1 hz2
    simp only [hz1, hz2, one_mul]
  have h2 : ∀ᶠ k in nhds (1 : G), ∀ g ∈ tsupport F, F (k⁻¹ * g) = F g := by
    have : Filter.Tendsto (fun x : G => x⁻¹) (nhds 1) (nhds 1) := by
      simpa using (continuous_inv (G := G)).tendsto 1
    exact this.eventually h1
  have hK : IsOpen (K : Set G) := by
    apply Subgroup.isOpen_of_mem_nhds K (g := 1)
    filter_upwards [h1, h2] with k hk1 hk2
    intro g
    by_cases hg : g ∈ tsupport F
    · exact hk1 g hg
    · by_cases hg' : k * g ∈ tsupport F
      · simpa using (hk2 _ hg').symm
      · rw [image_eq_zero_of_notMem_tsupport hg, image_eq_zero_of_notMem_tsupport hg']
  exact ⟨⟨K, hK⟩, fun k hk x => hk x⟩

theorem ind_mem (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    Set.indicator (K : Set G) (fun _ => (1 : ℂ)) ∈ SB G := by
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_,
    HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _⟩
  by_cases hx : x ∈ (K : Set G)
  · exact ⟨K, K.isOpen, hx, fun y hy => by
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨(K : Set G)ᶜ, K.isClosed.isOpen_compl, hx, fun y hy => by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

def ind (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) : SB G :=
  ⟨_, ind_mem K hK⟩

theorem ind_apply (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G) :
    (ind K hK : G → ℂ) x = Set.indicator (K : Set G) (fun _ => (1 : ℂ)) x :=
  rfl

theorem ind_left (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) (x : G) :
    (ind K hK : G → ℂ) (k * x) = (ind K hK : G → ℂ) x := by
  have h : k * x ∈ (K : Set G) ↔ x ∈ (K : Set G) :=
    Subgroup.mul_mem_cancel_left K.toSubgroup hk
  by_cases hx : x ∈ (K : Set G)
  · rw [ind_apply, ind_apply, Set.indicator_of_mem (h.2 hx), Set.indicator_of_mem hx]
  · rw [ind_apply, ind_apply, Set.indicator_of_notMem (fun h' => hx (h.1 h')),
      Set.indicator_of_notMem hx]

theorem exists_decomp (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (f : SB G)
    (hf : ∀ k ∈ K, ∀ x, (f : G → ℂ) (k * x) = (f : G → ℂ) x) :
    ∃ (S : Finset G) (a : G → ℂ),
      f = ∑ t ∈ S, a t • pullHomeo (Homeomorph.mulRight t) (ind K hK) := by
  classical
  have hdisc : DiscreteTopology (G ⧸ (K : Subgroup G)) :=
    QuotientGroup.discreteTopology K.isOpen
  let π : G → G ⧸ (K : Subgroup G) := fun x => ((x⁻¹ : G) : G ⧸ (K : Subgroup G))
  have hπ : Continuous π := QuotientGroup.continuous_mk.comp continuous_inv
  have hfin : (π '' tsupport (f : G → ℂ)).Finite :=
    ((show IsCompact (tsupport (f : G → ℂ)) from f.2.2).image hπ).finite_of_discrete
  have key : ∀ (x : G) (q : G ⧸ (K : Subgroup G)), x * q.out ∈ K ↔ π x = q := by
    intro x q
    have h := QuotientGroup.eq (s := (K : Subgroup G)) (a := x⁻¹) (b := q.out)
    rw [inv_inv, QuotientGroup.out_eq'] at h
    exact h.symm
  have hinj : Set.InjOn (fun q : G ⧸ (K : Subgroup G) => q.out) (hfin.toFinset : Set _) :=
    fun a _ b _ h => Quotient.out_injective h
  refine ⟨hfin.toFinset.image (fun q => q.out), fun t => (f : G → ℂ) t⁻¹, ?_⟩
  rw [Finset.sum_image hinj]
  apply Subtype.ext
  funext x
  rw [Submodule.coe_sum, Finset.sum_apply]
  have hterm : ∀ q ∈ hfin.toFinset,
      ((((f : G → ℂ) q.out⁻¹ • pullHomeo (Homeomorph.mulRight q.out) (ind K hK) : SB G)) : G → ℂ) x
        = if π x = q then (f : G → ℂ) x else 0 := by
    intro q _
    have e : ((((f : G → ℂ) q.out⁻¹ • pullHomeo (Homeomorph.mulRight q.out) (ind K hK) : SB G)) :
        G → ℂ) x = (f : G → ℂ) q.out⁻¹ * (ind K hK : G → ℂ) (x * q.out) := rfl
    rw [e, ind_apply]
    by_cases h : π x = q
    · have hm : x * q.out ∈ K := (key x q).2 h
      rw [if_pos h, Set.indicator_of_mem (show x * q.out ∈ (K : Set G) from hm), mul_one]
      have := hf _ hm q.out⁻¹
      rw [mul_inv_cancel_right] at this
      exact this.symm
    · rw [if_neg h, Set.indicator_of_notMem
        (show x * q.out ∉ (K : Set G) from fun hm => h ((key x q).1 hm)), mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra h0
    exact h (hfin.mem_toFinset.2 ⟨x, subset_tsupport _ h0, rfl⟩)

theorem exists_coeff (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (f : SB G)
    (hf : ∀ k ∈ K, ∀ x, (f : G → ℂ) (k * x) = (f : G → ℂ) x) :
    ∃ s : ℂ, ∀ M : SB G →ₗ[ℂ] ℂ,
      (∀ (g : G) (α : SB G), M (pullHomeo (Homeomorph.mulRight g) α) = M α) →
        M f = s * M (ind K hK) := by
  obtain ⟨S, a, h⟩ := exists_decomp K hK f hf
  refine ⟨∑ t ∈ S, a t, fun M hM => ?_⟩
  rw [h, _root_.map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_smul, hM, smul_eq_mul]

end Abstract

section Integral

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

theorem integrable_sb (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (α : SB G) :
    Integrable (α : G → ℂ) μ :=
  α.2.1.continuous.integrable_of_hasCompactSupport α.2.2

def haarForm (μ : Measure G) [IsFiniteMeasureOnCompacts μ] : SB G →ₗ[ℂ] ℂ where
  toFun α := ∫ x, (α : G → ℂ) x ∂μ
  map_add' α β := integral_add (integrable_sb μ α) (integrable_sb μ β)
  map_smul' c α := integral_const_mul c (α : G → ℂ)

theorem haarForm_apply (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (α : SB G) :
    haarForm μ α = ∫ x, (α : G → ℂ) x ∂μ :=
  rfl

variable [LocallyCompactSpace G]

theorem integral_mul_right_real (hU : IsUnimod G) (μ : Measure G) [μ.IsHaarMeasure] (g : G)
    {u : G → ℝ} (hu : Continuous u) (hcu : HasCompactSupport u) :
    ∫ x, u (x * g) ∂μ = ∫ x, u x ∂μ := by
  have h := integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport (map (· * g) μ) μ hu hcu
  have h1 : modularCharacterFun g = 1 := hU g
  rw [integral_smul_nnreal_measure, ← modularCharacterFun_eq_haarScalarFactor μ g, h1, one_smul,
    integral_map (AEMeasurable.mul_const aemeasurable_id' _) hu.aestronglyMeasurable] at h
  exact h

theorem haarForm_right (hU : IsUnimod G) (μ : Measure G) [μ.IsHaarMeasure] (g : G) (α : SB G) :
    haarForm μ (pullHomeo (Homeomorph.mulRight g) α) = haarForm μ α := by
  have hc : Continuous (α : G → ℂ) := α.2.1.continuous
  have hcs : HasCompactSupport (α : G → ℂ) := α.2.2
  have hre := integral_mul_right_real hU μ g (u := fun x => RCLike.re ((α : G → ℂ) x))
    (RCLike.continuous_re.comp hc) (hcs.comp_left (g := RCLike.re) (map_zero _))
  have him := integral_mul_right_real hU μ g (u := fun x => RCLike.im ((α : G → ℂ) x))
    (RCLike.continuous_im.comp hc) (hcs.comp_left (g := RCLike.im) (map_zero _))
  rw [haarForm_apply, haarForm_apply,
    ← integral_re_add_im (integrable_sb μ (pullHomeo (Homeomorph.mulRight g) α)),
    ← integral_re_add_im (integrable_sb μ α)]
  simp only [pullHomeo_apply, Homeomorph.coe_mulRight]
  rw [hre, him]

theorem haarForm_ind_ne_zero (μ : Measure G) [μ.IsHaarMeasure] (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) : haarForm μ (ind K hK) ≠ 0 := by
  have e : haarForm μ (ind K hK) = ∫ x, Set.indicator (K : Set G) (fun _ => (1 : ℂ)) x ∂μ := rfl
  rw [e, integral_indicator_const (1 : ℂ) K.isOpen.measurableSet]
  have h0 : μ (K : Set G) ≠ 0 := (K.isOpen.measure_pos μ ⟨1, K.one_mem⟩).ne'
  have h1 : μ.real (K : Set G) ≠ 0 := by
    rw [Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨h0, hK.measure_lt_top.ne⟩
  simpa using h1

end Integral

theorem exists_eq_mul_integral :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
      [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G],
      IsUnimod G → ∀ (μ : Measure G) [μ.IsHaarMeasure] (L : SB G →ₗ[ℂ] ℂ),
      (∀ (g : G) (α : SB G), L (pullHomeo (Homeomorph.mulRight g) α) = L α) →
      ∃ c : ℂ, ∀ α : SB G, L α = c * ∫ x, (α : G → ℂ) x ∂μ := by
  intro G _ _ _ _ _ _ _ _ hU μ _ L hL
  obtain ⟨K₀, hK₀⟩ := GroundTheory.Automorphic.exists_compactOpenSubgroup (G := G)
  have hI := haarForm_right hU μ
  refine ⟨L (ind K₀ hK₀) / haarForm μ (ind K₀ hK₀), fun α => ?_⟩
  rw [← haarForm_apply]
  obtain ⟨K', hK'⟩ := exists_open_left_stab α.2
  have hKc : IsCompact ((K₀ ⊓ K' : OpenSubgroup G) : Set G) :=
    GroundTheory.Automorphic.isCompact_inf_left hK₀
  obtain ⟨s, hs⟩ := exists_coeff (K₀ ⊓ K') hKc α (fun k hk x => hK' k hk.2 x)
  obtain ⟨s₀, hs₀⟩ := exists_coeff (K₀ ⊓ K') hKc (ind K₀ hK₀)
    (fun k hk x => ind_left K₀ hK₀ hk.1 x)
  have hne := haarForm_ind_ne_zero μ (K₀ ⊓ K') hKc
  have hne₀ := haarForm_ind_ne_zero μ K₀ hK₀
  have h1 := hs L hL
  have h2 := hs _ hI
  have h3 := hs₀ L hL
  have h4 := hs₀ _ hI
  rw [h1, h2, h3, h4]
  have hs₀0 : s₀ ≠ 0 := fun h => hne₀ (by rw [h4, h, zero_mul])
  field_simp

end GlobalTheory.CompanionTheory.FrobHaarR
