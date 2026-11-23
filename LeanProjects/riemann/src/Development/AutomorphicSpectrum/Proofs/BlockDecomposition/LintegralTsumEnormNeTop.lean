import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralNonnegNormaliserEq

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Pointwise
open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.QuotUnfold

section Domain

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem exists_open_small (H : Subgroup G) [DiscreteTopology H] :
    ∃ W : Set G, IsOpen W ∧ (1 : G) ∈ W ∧ ∀ a ∈ W, ∀ b ∈ W, a * b⁻¹ ∈ H → a = b := by
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 (isOpen_discrete ({1} : Set H))
  have h1 : (1 : G) ∈ V := by
    have : (1 : H) ∈ (Subtype.val ⁻¹' V : Set H) := by rw [hV]; rfl
    simpa using this
  obtain ⟨W, hW, hWV⟩ := exists_nhds_split_inv (hVo.mem_nhds h1)
  refine ⟨interior W, isOpen_interior, mem_interior_iff_mem_nhds.2 hW, fun a ha b hb hab => ?_⟩
  have hv : a / b ∈ V := hWV a (interior_subset ha) b (interior_subset hb)
  have : (⟨a * b⁻¹, hab⟩ : H) ∈ (Subtype.val ⁻¹' V : Set H) := by
    simpa [div_eq_mul_inv] using hv
  rw [hV] at this
  have h2 : a * b⁻¹ = 1 := congrArg Subtype.val (Set.mem_singleton_iff.1 this)
  exact mul_inv_eq_one.1 h2

theorem exists_small_cover [SecondCountableTopology G] (H : Subgroup G) [DiscreteTopology H] :
    ∃ u : ℕ → Set G, (∀ i, IsOpen (u i)) ∧ (∀ g, ∃ i, g ∈ u i) ∧
      ∀ i, ∀ a ∈ u i, ∀ b ∈ u i, a * b⁻¹ ∈ H → a = b := by
  obtain ⟨W, hWo, hW1, hW⟩ := exists_open_small H
  let s : G → Set G := fun g => (fun x => x * g⁻¹) ⁻¹' W
  have hso : ∀ g, IsOpen (s g) := fun g => hWo.preimage (continuous_mul_right _)
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable s hso
  have hcov : ∀ g, ∃ t ∈ T, g ∈ s t := by
    intro g
    have : g ∈ ⋃ i, s i := mem_iUnion.2 ⟨g, by simpa [s] using hW1⟩
    rw [← hT] at this
    simpa using this
  have hne : T.Nonempty := by
    obtain ⟨t, ht, -⟩ := hcov 1
    exact ⟨t, ht⟩
  obtain ⟨e, rfl⟩ := hTc.exists_eq_range hne
  refine ⟨fun i => s (e i), fun i => hso _, fun g => ?_, fun i a ha b hb hab => ?_⟩
  · obtain ⟨t, ⟨i, rfl⟩, h⟩ := hcov g
    exact ⟨i, h⟩
  · have := hW _ ha _ hb (by simpa [mul_assoc] using hab)
    exact mul_right_cancel this

theorem exists_strict_domain [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) [Countable H] [DiscreteTopology H] :
    ∃ D : Set G, MeasurableSet D ∧ ∀ g : G, ∃! h : H, (h : G) * g ∈ D := by
  classical
  obtain ⟨u, huo, hcov, hu⟩ := exists_small_cover H
  let A : ℕ → Set G := fun i => {x | ∃ h : H, (h : G) * x ∈ u i}
  have hAm : ∀ i, MeasurableSet (A i) := by
    intro i
    have : A i = ⋃ h : H, (fun x => (h : G) * x) ⁻¹' u i := by
      ext x; simp [A]
    rw [this]
    exact MeasurableSet.iUnion fun h =>
      ((huo i).preimage (continuous_mul_left _)).measurableSet
  let D : Set G := ⋃ i, (u i ∩ ⋂ j : Fin i, (A j)ᶜ)
  have hD : MeasurableSet D := MeasurableSet.iUnion fun i =>
    (huo i).measurableSet.inter (MeasurableSet.iInter fun j => (hAm j).compl)
  have memD : ∀ x, x ∈ D ↔ ∃ i, x ∈ u i ∧ ∀ j < i, x ∉ A j := by
    intro x
    simp only [D, mem_iUnion, mem_inter_iff, mem_iInter, mem_compl_iff]
    exact exists_congr fun i => and_congr_right fun _ =>
      ⟨fun h j hj => h ⟨j, hj⟩, fun h j => h j j.2⟩
  have hAinv : ∀ i (h : H) x, (h : G) * x ∈ A i ↔ x ∈ A i := by
    intro i h x
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k * h, by simpa [mul_assoc] using hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k * h⁻¹, by simpa [mul_assoc] using hk⟩
  refine ⟨D, hD, fun g => ?_⟩
  have hex : ∃ i, g ∈ A i := by
    obtain ⟨i, hi⟩ := hcov g
    exact ⟨i, 1, by simpa using hi⟩
  have hmin := Nat.find_spec hex
  set m := Nat.find hex with hm
  obtain ⟨h, hh⟩ := hmin
  refine ⟨h, (memD _).2 ⟨m, hh, fun j hj hA => ?_⟩, fun h' hh' => ?_⟩
  · exact Nat.find_min hex hj ((hAinv j h g).1 hA)
  · obtain ⟨i, hi, hij⟩ := (memD _).1 hh'
    have hgi : g ∈ A i := ⟨h', hi⟩
    have hmi : m ≤ i := Nat.find_min' hex hgi
    have him : i = m := by
      by_contra hne
      have hlt : m < i := lt_of_le_of_ne hmi (Ne.symm hne)
      refine hij m hlt ((hAinv m h' g).2 ⟨h, hh⟩)
    subst him
    have hk : ((h' : G) * g) * ((h : G) * g)⁻¹ ∈ H := by
      have : ((h' : G) * g) * ((h : G) * g)⁻¹ = ((h' * h⁻¹ : H) : G) := by
        simp [mul_assoc]
      rw [this]
      exact Subtype.property _
    have := hu _ _ hi _ hh hk
    exact Subtype.ext (mul_right_cancel this)

theorem count_isInvInvariant [MeasurableSpace G] [MeasurableInv G]
    (H : Subgroup G) [Countable H] [MeasurableSingletonClass H] : (Measure.count : Measure H).IsInvInvariant := by
  have hmi : Measurable (fun h : H => h⁻¹) := measurable_of_countable _
  refine ⟨?_⟩
  ext s hs
  change Measure.map (fun h : H => h⁻¹) Measure.count s = _
  rw [Measure.map_apply hmi hs]
  have : (Inv.inv ⁻¹' s : Set H) = (fun h : H => h⁻¹) '' s := by
    ext x; simp
  rw [this, Measure.count_injective_image' inv_injective hs ((Set.to_countable _).measurableSet)]

end Domain

section Reindex

def reidx {K : Type*} [Group K] (S : Subgroup K) : (K ⧸ S) × S ≃ K where
  toFun p := (p.2 : K) * p.1.out⁻¹
  invFun γ := (((γ⁻¹ : K) : K ⧸ S), ⟨γ * (((γ⁻¹ : K) : K ⧸ S)).out, by
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' ((γ⁻¹ : K) : K ⧸ S)).symm
    simpa using this⟩)
  left_inv := by
    rintro ⟨q, s⟩
    have h1 : ((((s : K) * q.out⁻¹)⁻¹ : K) : K ⧸ S) = q := by
      rw [mul_inv_rev, inv_inv, QuotientGroup.mk_mul_of_mem _ (S.inv_mem s.2)]
      exact QuotientGroup.out_eq' q
    refine Prod.ext h1 (Subtype.ext ?_)
    simp only [h1, inv_mul_cancel_right]
  right_inv γ := by simp

theorem reidx_apply {K : Type*} [Group K] (S : Subgroup K) (q : K ⧸ S) (s : S) :
    reidx S (q, s) = (s : K) * q.out⁻¹ := rfl

theorem tsum_equiv_prod {K Q S : Type*} (e : Q × S ≃ K) (a : K → ℂ) (hs : Summable a) :
    ∑' k, a k = ∑' q, ∑' s, a (e (q, s)) := by
  rw [← e.tsum_eq a]
  exact (e.summable_iff.2 hs).tsum_prod

end Reindex

section Unfold

variable {G : Type*} [Group G] {Γ Γ₀ : Subgroup G} {D : Set G}

theorem existsUnique_subgroupOf (hle : Γ₀ ≤ Γ) (hD : ∀ g : G, ∃! h : Γ₀, (h : G) * g ∈ D) (y : G) :
    ∃! s : Γ₀.subgroupOf Γ, (((s : Γ) : G)) * y ∈ D := by
  obtain ⟨h, hh, hu⟩ := hD y
  refine ⟨⟨⟨h, hle h.2⟩, Subgroup.mem_subgroupOf.2 h.2⟩, hh, fun s hs => ?_⟩
  have := hu ⟨((s : Γ) : G), Subgroup.mem_subgroupOf.1 s.2⟩ hs
  have h2 : ((s : Γ) : G) = h := congrArg Subtype.val this
  exact Subtype.ext (Subtype.ext h2)

theorem tsum_indicator_eq {M : Type*} [AddCommMonoid M] [TopologicalSpace M] [T2Space M]
    (hle : Γ₀ ≤ Γ) (hD : ∀ g : G, ∃! h : Γ₀, (h : G) * g ∈ D) (f : G → M)
    (hf : ∀ h ∈ Γ₀, ∀ g, f (h * g) = f g) (y : G) :
    ∑' s : Γ₀.subgroupOf Γ, D.indicator f (((s : Γ) : G) * y) = f y := by
  obtain ⟨s₀, hs₀, hu⟩ := existsUnique_subgroupOf hle hD y
  rw [tsum_eq_single s₀ (fun s hs => indicator_of_notMem (fun hm => hs (hu s hm)) _),
    indicator_of_mem hs₀]
  exact hf _ (Subgroup.mem_subgroupOf.1 s₀.2) y

theorem tsum_enorm_eq (hle : Γ₀ ≤ Γ) (hD : ∀ g : G, ∃! h : Γ₀, (h : G) * g ∈ D) (f : G → ℝ≥0∞)
    (hf : ∀ h ∈ Γ₀, ∀ g, f (h * g) = f g) (x : G) :
    ∑' γ : Γ, D.indicator f ((γ : G) * x) =
      ∑' q : Γ ⧸ Γ₀.subgroupOf Γ, f (((q.out : Γ) : G)⁻¹ * x) := by
  rw [← (reidx (Γ₀.subgroupOf Γ)).tsum_eq, ENNReal.tsum_prod']
  refine tsum_congr fun q => ?_
  simp only [reidx_apply, Subgroup.coe_mul, InvMemClass.coe_inv, mul_assoc]
  exact tsum_indicator_eq hle hD f hf _

theorem tsum_complex_eq (hle : Γ₀ ≤ Γ) (hD : ∀ g : G, ∃! h : Γ₀, (h : G) * g ∈ D) (f : G → ℂ)
    (hf : ∀ h ∈ Γ₀, ∀ g, f (h * g) = f g) (x : G)
    (hs : Summable fun γ : Γ => D.indicator f ((γ : G) * x)) :
    ∑' γ : Γ, D.indicator f ((γ : G) * x) =
      ∑' q : Γ ⧸ Γ₀.subgroupOf Γ, f (((q.out : Γ) : G)⁻¹ * x) := by
  rw [tsum_equiv_prod (reidx (Γ₀.subgroupOf Γ)) _ hs]
  refine tsum_congr fun q => ?_
  simp only [reidx_apply, Subgroup.coe_mul, InvMemClass.coe_inv, mul_assoc]
  exact tsum_indicator_eq hle hD f hf _

end Unfold

section Main

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {Γ Γ₀ : Subgroup G} [Countable Γ] [DiscreteTopology Γ₀]
  {μ : Measure G} [μ.IsMulLeftInvariant] [SFinite μ] {Fd : Set G} {F : G → ℂ}

theorem quotIntegral_unfold (hle : Γ₀ ≤ Γ) (hFd : IsFundamentalDomain Γ Fd μ) (hF : Measurable F)
    (hFH : ∀ h ∈ Γ₀, ∀ g, F (h * g) = F g)
    (hint : ∫⁻ x in Fd, ∑' q : Γ ⧸ Γ₀.subgroupOf Γ, ‖F (((q.out : Γ) : G)⁻¹ * x)‖ₑ ∂μ ≠ ∞) :
    quotIntegral μ Γ₀ Measure.count F =
      ∫ x in Fd, ∑' q : Γ ⧸ Γ₀.subgroupOf Γ, F (((q.out : Γ) : G)⁻¹ * x) ∂μ := by
  classical
  haveI : Countable (Γ ⧸ Γ₀.subgroupOf Γ) :=
    Function.Surjective.countable (f := (QuotientGroup.mk : Γ → _)) QuotientGroup.mk_surjective
  haveI : Countable Γ₀ := (Subgroup.inclusion_injective hle).countable
  haveI : MeasurableSingletonClass Γ₀ := ⟨fun h => (isOpen_discrete ({h} : Set Γ₀)).measurableSet⟩
  haveI := count_isInvInvariant Γ₀
  obtain ⟨D, hDm, hD⟩ := exists_strict_domain Γ₀
  have hρ : IsQuotNormaliser Γ₀ Measure.count (D.indicator (1 : G → ℝ≥0∞)) := by
    refine ⟨measurable_one.indicator hDm, fun g => ?_⟩
    rw [lintegral_count]
    obtain ⟨h₀, h₁, hu⟩ := hD g
    rw [tsum_eq_single h₀ (fun h hh => indicator_of_notMem (fun hm => hh (hu h hm)) _),
      indicator_of_mem h₁]
    rfl
  rw [GlobalTheory.CompanionTheory.QuotNorm.quotIntegral_eq hF hFH hρ]
  have hfe : (fun g => F g * (((D.indicator (1 : G → ℝ≥0∞)) g).toReal : ℂ)) = D.indicator F := by
    funext g
    by_cases hg : g ∈ D <;> simp [hg]
  rw [hfe]
  have hfm : Measurable (D.indicator F) := hF.indicator hDm
  have hne : ∀ x, ‖D.indicator F x‖ₑ = D.indicator (fun g => ‖F g‖ₑ) x := by
    intro x
    by_cases hx : x ∈ D <;> simp [hx]
  have hFe : ∀ h ∈ Γ₀, ∀ g, ‖F (h * g)‖ₑ = ‖F g‖ₑ := fun h hh g => by rw [hFH h hh g]
  have hmγ : ∀ γ : Γ, Measurable fun x => D.indicator F ((γ : G) * x) := fun γ =>
    hfm.comp (measurable_const_mul _)
  have hl0 : ∫⁻ x, ‖D.indicator F x‖ₑ ∂μ = ∑' γ : Γ, ∫⁻ x in Fd, ‖D.indicator F ((γ : G) * x)‖ₑ ∂μ :=
    hFd.lintegral_eq_tsum'' (fun x => ‖D.indicator F x‖ₑ)
  have hl : ∫⁻ x, ‖D.indicator F x‖ₑ ∂μ =
      ∫⁻ x in Fd, ∑' q : Γ ⧸ Γ₀.subgroupOf Γ, ‖F (((q.out : Γ) : G)⁻¹ * x)‖ₑ ∂μ := by
    rw [hl0, ← lintegral_tsum fun γ => (hmγ γ).enorm.aemeasurable]
    refine lintegral_congr fun x => ?_
    simp only [hne]
    exact tsum_enorm_eq hle hD (fun g => ‖F g‖ₑ) hFe x
  have hfi : Integrable (D.indicator F) μ :=
    ⟨hfm.aestronglyMeasurable, by
      rw [hasFiniteIntegral_iff_enorm, hl]
      exact lt_top_iff_ne_top.2 hint⟩
  have hsum : ∑' γ : Γ, ∫⁻ x in Fd, ‖D.indicator F ((γ : G) * x)‖ₑ ∂μ ≠ ∞ := by
    rw [← hl0, hl]
    exact hint
  have key : ∫ x, D.indicator F x ∂μ = ∫ x in Fd, ∑' γ : Γ, D.indicator F ((γ : G) * x) ∂μ := by
    rw [integral_tsum (fun γ => (hmγ γ).aestronglyMeasurable) hsum, hFd.integral_eq_tsum'' _ hfi]
    rfl
  rw [key]
  refine integral_congr_ae ?_
  have hmq : Measurable fun x => ∑' q : Γ ⧸ Γ₀.subgroupOf Γ, ‖F (((q.out : Γ) : G)⁻¹ * x)‖ₑ :=
    Measurable.ennreal_tsum fun q => (hF.comp (measurable_const_mul _)).enorm
  filter_upwards [ae_lt_top hmq hint] with x hx
  refine tsum_complex_eq hle hD F hFH x ?_
  have h2 : ∑' γ : Γ, ‖D.indicator F ((γ : G) * x)‖ₑ ≠ ∞ := by
    simp only [hne]
    rw [tsum_enorm_eq hle hD (fun g => ‖F g‖ₑ) hFe x]
    exact hx.ne
  exact Summable.of_nnnorm (ENNReal.tsum_coe_ne_top_iff_summable.1 h2)

theorem integrableOn_unfold (hF : Measurable F)
    (hint : ∫⁻ x in Fd, ∑' q : Γ ⧸ Γ₀.subgroupOf Γ, ‖F (((q.out : Γ) : G)⁻¹ * x)‖ₑ ∂μ ≠ ∞) :
    IntegrableOn (fun x => ∑' q : Γ ⧸ Γ₀.subgroupOf Γ, F (((q.out : Γ) : G)⁻¹ * x)) Fd μ := by
  haveI : Countable (Γ ⧸ Γ₀.subgroupOf Γ) :=
    Function.Surjective.countable (f := (QuotientGroup.mk : Γ → _)) QuotientGroup.mk_surjective
  refine ⟨AEStronglyMeasurable.tsum fun q =>
    (hF.comp (measurable_const_mul _)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact lt_of_le_of_lt (lintegral_mono fun x => enorm_tsum_le_tsum_enorm)
    (lt_top_iff_ne_top.2 hint)

end Main

end GlobalTheory.CompanionTheory.QuotUnfold
