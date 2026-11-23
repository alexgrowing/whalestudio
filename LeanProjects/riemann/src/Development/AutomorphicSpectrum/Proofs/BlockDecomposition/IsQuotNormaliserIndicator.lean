import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotIntegralZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralNonnegNormaliserEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwConjOfIsTest
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralTsumEnormNeTop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMahlerBound

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Set
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.SliceFubini

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem isQuotNormaliser_indicator (H : Subgroup G) {D : Set G} (hDm : MeasurableSet D)
    (hD : ∀ g : G, ∃! h : H, (h : G) * g ∈ D) :
    IsQuotNormaliser H Measure.count (D.indicator (1 : G → ℝ≥0∞)) := by
  refine ⟨measurable_one.indicator hDm, fun g => ?_⟩
  rw [lintegral_count]
  obtain ⟨h₀, h₁, hu⟩ := hD g
  rw [tsum_eq_single h₀ (fun h hh => indicator_of_notMem (fun hm => hh (hu h hm)) _),
    indicator_of_mem h₁]
  rfl

theorem quotIntegral_eq_indicator {μ : Measure G} [μ.IsMulLeftInvariant] [SFinite μ] (H : Subgroup G)
    [Countable H] {D : Set G} (hDm : MeasurableSet D) (hD : ∀ g : G, ∃! h : H, (h : G) * g ∈ D)
    {f : G → ℂ} (hf : Measurable f) (hfH : ∀ h ∈ H, ∀ g, f (h * g) = f g) :
    quotIntegral μ H Measure.count f = ∫ x, D.indicator f x ∂μ := by
  haveI := GlobalTheory.CompanionTheory.QuotUnfold.count_isInvInvariant H
  rw [GlobalTheory.CompanionTheory.QuotNorm.quotIntegral_eq hf hfH (isQuotNormaliser_indicator H hDm hD)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  by_cases hg : g ∈ D <;> simp [hg]

theorem measure_domain_inter_le {μ : Measure G} [μ.IsMulLeftInvariant] (H : Subgroup G) [Countable H]
    {D S : Set G} (hDm : MeasurableSet D) (hD : ∀ g : G, ∃! h : H, (h : G) * g ∈ D) (hS : MeasurableSet S) :
    μ (D ∩ {x | ∃ h : H, (h : G)⁻¹ * x ∈ S}) ≤ μ S := by
  have hsub : D ∩ {x | ∃ h : H, (h : G)⁻¹ * x ∈ S} ⊆
      ⋃ h : H, (D ∩ (fun x => (h : G)⁻¹ * x) ⁻¹' S) := by
    rintro x ⟨hx, h, hh⟩
    exact mem_iUnion.2 ⟨h, hx, hh⟩
  have e : ∀ h : H, μ (D ∩ (fun x => (h : G)⁻¹ * x) ⁻¹' S) = μ ((fun x => (h : G) * x) ⁻¹' D ∩ S) := by
    intro h
    rw [← measure_preimage_mul μ (h : G) (D ∩ (fun x => (h : G)⁻¹ * x) ⁻¹' S)]
    congr 1
    ext x
    simp
  have hdisj : Pairwise (Function.onFun Disjoint fun h : H => (fun x => (h : G) * x) ⁻¹' D ∩ S) := by
    intro h h' hne
    refine Set.disjoint_left.2 fun x hx hx' => hne ?_
    obtain ⟨h₀, -, hu⟩ := hD x
    exact (hu h hx.1).trans (hu h' hx'.1).symm
  have hmeas : ∀ h : H, MeasurableSet ((fun x => (h : G) * x) ⁻¹' D ∩ S) := fun h =>
    (measurable_const_mul (h : G) hDm).inter hS
  calc μ (D ∩ {x | ∃ h : H, (h : G)⁻¹ * x ∈ S})
      ≤ μ (⋃ h : H, (D ∩ (fun x => (h : G)⁻¹ * x) ⁻¹' S)) := measure_mono hsub
    _ ≤ ∑' h : H, μ (D ∩ (fun x => (h : G)⁻¹ * x) ⁻¹' S) := measure_iUnion_le _
    _ = ∑' h : H, μ ((fun x => (h : G) * x) ⁻¹' D ∩ S) := by simp_rw [e]
    _ = μ (⋃ h : H, (fun x => (h : G) * x) ⁻¹' D ∩ S) := (measure_iUnion hdisj hmeas).symm
    _ ≤ μ S := measure_mono (iUnion_subset fun _ => inter_subset_right)

theorem quotIntegral_const_mul (μ : Measure G) (H : Subgroup G) (μH : Measure H) (c : ℂ) (f : G → ℂ) :
    quotIntegral μ H μH (fun x => c * f x) = c * quotIntegral μ H μH f := by
  unfold quotIntegral
  split_ifs
  · simp only [mul_assoc]
    exact integral_const_mul _ _
  · simp

end Abstract

section Pair

variable {G₁ G₂ : Type*} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [T2Space G₁]
  [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]
  [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [T2Space G₂]
  [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂]

theorem prod_domain {H₁ : Subgroup G₁} {H₂ : Subgroup G₂} {D₁ : Set G₁} {D₂ : Set G₂}
    (h₁ : ∀ g : G₁, ∃! h : H₁, (h : G₁) * g ∈ D₁) (h₂ : ∀ g : G₂, ∃! h : H₂, (h : G₂) * g ∈ D₂)
    (g : G₁ × G₂) : ∃! h : H₁.prod H₂, (h : G₁ × G₂) * g ∈ D₁ ×ˢ D₂ := by
  obtain ⟨a, ha, ua⟩ := h₁ g.1
  obtain ⟨b, hb, ub⟩ := h₂ g.2
  refine ⟨⟨((a : G₁), (b : G₂)), ⟨a.2, b.2⟩⟩, ⟨ha, hb⟩, ?_⟩
  rintro ⟨⟨x, y⟩, hx, hy⟩ ⟨m₁, m₂⟩
  have e₁ := ua ⟨x, hx⟩ m₁
  have e₂ := ub ⟨y, hy⟩ m₂
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact congrArg Subtype.val e₁
  · exact congrArg Subtype.val e₂

theorem quotIntegral_prod {μ₁ : Measure G₁} [μ₁.IsMulLeftInvariant] [SFinite μ₁]
    {μ₂ : Measure G₂} [μ₂.IsMulLeftInvariant] [SFinite μ₂]
    (H₁ : Subgroup G₁) (H₂ : Subgroup G₂) [Countable H₁] [Countable H₂] [DiscreteTopology H₁]
    [DiscreteTopology H₂] {F : G₁ × G₂ → ℂ} (hF : Measurable F)
    (i₁ : ∀ h ∈ H₁, ∀ x y, F (h * x, y) = F (x, y)) (i₂ : ∀ h ∈ H₂, ∀ x y, F (x, h * y) = F (x, y))
    {M : ℝ} (hM : ∀ z, ‖F z‖ ≤ M) {S₁ : Set G₁} {S₂ : Set G₂} (m₁ : MeasurableSet S₁)
    (m₂ : MeasurableSet S₂) (f₁ : μ₁ S₁ ≠ ∞) (f₂ : μ₂ S₂ ≠ ∞)
    (hS : ∀ x y, F (x, y) ≠ 0 → (∃ h : H₁, (h : G₁)⁻¹ * x ∈ S₁) ∧ ∃ h : H₂, (h : G₂)⁻¹ * y ∈ S₂) :
    quotIntegral (μ₁.prod μ₂) (H₁.prod H₂) Measure.count F =
        quotIntegral μ₂ H₂ Measure.count (fun y => quotIntegral μ₁ H₁ Measure.count fun x => F (x, y)) ∧
      quotIntegral (μ₁.prod μ₂) (H₁.prod H₂) Measure.count F =
        quotIntegral μ₁ H₁ Measure.count (fun x => quotIntegral μ₂ H₂ Measure.count fun y => F (x, y)) := by
  classical
  obtain ⟨D₁, d₁, u₁⟩ := GlobalTheory.CompanionTheory.QuotUnfold.exists_strict_domain H₁
  obtain ⟨D₂, d₂, u₂⟩ := GlobalTheory.CompanionTheory.QuotUnfold.exists_strict_domain H₂
  haveI : Countable (H₁.prod H₂) :=
    Function.Injective.countable (f := fun z : H₁.prod H₂ =>
      ((⟨z.1.1, z.2.1⟩ : H₁), (⟨z.1.2, z.2.2⟩ : H₂))) (by
        rintro ⟨⟨a, b⟩, h⟩ ⟨⟨c, d⟩, h'⟩ e
        simp only [Prod.mk.injEq, Subtype.mk.injEq] at e
        exact Subtype.ext (Prod.ext e.1 e.2))
  have hFx : ∀ y, Measurable fun x => F (x, y) := fun y => hF.comp measurable_prodMk_right
  have hFy : ∀ x, Measurable fun y => F (x, y) := fun x => hF.comp measurable_prodMk_left
  have hi : ∀ y, quotIntegral μ₁ H₁ Measure.count (fun x => F (x, y)) =
      ∫ x, D₁.indicator (fun x => F (x, y)) x ∂μ₁ := fun y =>
    quotIntegral_eq_indicator H₁ d₁ u₁ (hFx y) fun h hh x => i₁ h hh x y
  have hj : ∀ x, quotIntegral μ₂ H₂ Measure.count (fun y => F (x, y)) =
      ∫ y, D₂.indicator (fun y => F (x, y)) y ∂μ₂ := fun x =>
    quotIntegral_eq_indicator H₂ d₂ u₂ (hFy x) fun h hh y => i₂ h hh x y
  set f : G₁ × G₂ → ℂ := (D₁ ×ˢ D₂).indicator F with hf
  have hfm : Measurable f := hF.indicator (d₁.prod d₂)
  have hT : quotIntegral (μ₁.prod μ₂) (H₁.prod H₂) Measure.count F = ∫ z, f z ∂(μ₁.prod μ₂) :=
    quotIntegral_eq_indicator _ (d₁.prod d₂) (prod_domain u₁ u₂) hF fun h hh z => by
      obtain ⟨a, b⟩ := z
      obtain ⟨c, e⟩ := h
      show F (c * a, e * b) = _
      rw [i₁ c hh.1, i₂ e hh.2]
  have hint : Integrable f (μ₁.prod μ₂) := by
    set T₁ := D₁ ∩ {x | ∃ h : H₁, (h : G₁)⁻¹ * x ∈ S₁}
    set T₂ := D₂ ∩ {x | ∃ h : H₂, (h : G₂)⁻¹ * x ∈ S₂}
    have hsupp : Function.support f ⊆ T₁ ×ˢ T₂ := by
      rintro ⟨x, y⟩ hz
      have hz' : (x, y) ∈ D₁ ×ˢ D₂ := by
        by_contra hn
        exact hz (indicator_of_notMem hn _)
      have hne : F (x, y) ≠ 0 := by
        intro h0
        exact hz (by simp [hf, indicator_of_mem hz', h0])
      obtain ⟨p, q⟩ := hS x y hne
      exact ⟨⟨hz'.1, p⟩, ⟨hz'.2, q⟩⟩
    refine (integrableOn_iff_integrable_of_support_subset hsupp).1 ?_
    refine Measure.integrableOn_of_bounded (M := M) ?_ hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => (norm_indicator_le_norm_self _ _).trans (hM z))
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top
      (ne_top_of_le_ne_top f₁ (measure_domain_inter_le H₁ d₁ u₁ m₁))
      (ne_top_of_le_ne_top f₂ (measure_domain_inter_le H₂ d₂ u₂ m₂))
  have hA : Measurable fun y => ∫ x, D₁.indicator (fun x => F (x, y)) x ∂μ₁ := by
    have h0 : Measurable (fun z : G₁ × G₂ => D₁.indicator (fun x => F (x, z.2)) z.1) := by
      have : (fun z : G₁ × G₂ => D₁.indicator (fun x => F (x, z.2)) z.1) =
          (D₁ ×ˢ (univ : Set G₂)).indicator F := by
        funext z
        by_cases hz : z.1 ∈ D₁ <;> simp [indicator, hz]
      rw [this]
      exact hF.indicator (d₁.prod MeasurableSet.univ)
    exact (h0.stronglyMeasurable.integral_prod_left' (μ := μ₁)).measurable
  have hB : Measurable fun x => ∫ y, D₂.indicator (fun y => F (x, y)) y ∂μ₂ := by
    have h0 : Measurable (fun z : G₁ × G₂ => D₂.indicator (fun y => F (z.1, y)) z.2) := by
      have : (fun z : G₁ × G₂ => D₂.indicator (fun y => F (z.1, y)) z.2) =
          ((univ : Set G₁) ×ˢ D₂).indicator F := by
        funext z
        by_cases hz : z.2 ∈ D₂ <;> simp [indicator, hz]
      rw [this]
      exact hF.indicator (MeasurableSet.univ.prod d₂)
    exact (h0.stronglyMeasurable.integral_prod_right' (ν := μ₂)).measurable
  constructor
  · simp only [hi]
    rw [hT, quotIntegral_eq_indicator H₂ d₂ u₂ hA (fun h hh y => by simp only [i₂ h hh]),
      integral_prod_symm f hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ D₂
    · simp only [indicator_of_mem hy]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ D₁ <;> simp [hf, indicator, hx, hy]
    · simp [hf, indicator, hy]
  · simp only [hj]
    rw [hT, quotIntegral_eq_indicator H₁ d₁ u₁ hB (fun h hh x => by simp only [i₁ h hh]),
      integral_prod f hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ D₁
    · simp only [indicator_of_mem hx]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      by_cases hy : y ∈ D₂ <;> simp [hf, indicator, hx, hy]
    · simp [hf, indicator, hx]

end Pair

section Rational

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem thetaA_ratGL_eq (t : GL (Fin n) E) : thetaA E n (ratGL E n t) = ratGL E n (thetaE E n t) := by
  refine Units.ext ?_
  ext i j
  have hinv : ((ratGL E n t)⁻¹ : GA E n) = ratGL E n t⁻¹ := (map_inv _ _).symm
  rw [thetaR_val, hinv]
  exact conjAd_algebraMap _

theorem twConj_ratGL (γ d : GL (Fin n) E) :
    twConj (thetaA E n) (ratGL E n γ) (ratGL E n d) = ratGL E n (twConj (thetaE E n) γ d) := by
  simp only [twConj, map_mul, map_inv, thetaA_ratGL_eq]

theorem twConj_mul' {G : Type*} [Group G] (θ : Monoid.End G) (a b d : G) :
    twConj θ (a * b) d = twConj θ b (twConj θ a d) := by
  simp only [twConj, map_mul, _root_.mul_inv_rev, mul_assoc]

theorem twConj_ratCent (d : GL (Fin n) E) {h : GA E n} (hh : h ∈ ratCent d) (x : GA E n) :
    twConj (thetaA E n) (h * x) (ratGL E n d) = twConj (thetaA E n) x (ratGL E n d) := by
  obtain ⟨t, ht, rfl⟩ := hh
  refine twConj_mul_left _ _ ?_ x
  change twConj (thetaA E n) (ratGL E n t) (ratGL E n d) = ratGL E n d
  rw [twConj_ratGL]
  exact congrArg _ ht

theorem discreteTopology_ratCent (d : GL (Fin n) E) : DiscreteTopology (ratCent d) := by
  haveI := GlobalTheory.CompanionTheory.KerTwFin.discreteTopology_range (E := E) (n := n)
  exact DiscreteTopology.of_subset (s := ((ratGL E n).range : Set (GA E n)))
    GlobalTheory.CompanionTheory.KerTwFin.discreteTopology_range (by rintro _ ⟨t, -, rfl⟩; exact ⟨t, rfl⟩)

theorem countable_ratCent (d : GL (Fin n) E) : Countable (ratCent d) := by
  haveI := discreteTopology_ratCent d
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E n
  exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance

theorem continuous_twConj (δ : GA E n) : Continuous fun x : GA E n => twConj (thetaA E n) x δ :=
  (continuous_inv.mul continuous_const).mul GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA

theorem exists_compact_cover (hM : Mahler) (τ : ℝ) (d : GL (Fin n) E) {K : Set (GA E n)} (hK : IsCompact K) :
    ∃ S : Set (GA E n), IsCompact S ∧ ∀ x ∈ cutSet E n τ, twConj (thetaA E n) x (ratGL E n d) ∈ K →
      ∃ h : ratCent d, (h : GA E n)⁻¹ * x ∈ S := by
  classical
  obtain ⟨-, -, C, hC, hcov⟩ := hM E n τ
  have hKc : IsCompact (C * K * (thetaA E n '' C)⁻¹) :=
    (hC.mul hK).mul (hC.image GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA).inv
  have hfin := GlobalTheory.CompanionTheory.KerTwFin.finite_ratGL_mem hKc
  let pick : GL (Fin n) E → GL (Fin n) E := fun δ =>
    if h : ∃ γ, twConj (thetaE E n) γ d = δ then h.choose else 1
  refine ⟨⋃ δ ∈ {δ : GL (Fin n) E | ratGL E n δ ∈ C * K * (thetaA E n '' C)⁻¹},
    (fun c => ratGL E n (pick δ) * c) '' C,
    hfin.isCompact_biUnion fun δ _ => hC.image (continuous_const.mul continuous_id), ?_⟩
  intro x hx hxK
  obtain ⟨_, ⟨γ, rfl⟩, c, hc, rfl⟩ := Set.mem_mul.1 (hcov hx)
  set δ := twConj (thetaE E n) γ d with hδ
  have hk : twConj (thetaA E n) c (ratGL E n δ) ∈ K := by
    rw [hδ, ← twConj_ratGL, ← twConj_mul']
    exact hxK
  have hδK : ratGL E n δ ∈ C * K * (thetaA E n '' C)⁻¹ := by
    have e : ratGL E n δ = c * twConj (thetaA E n) c (ratGL E n δ) * (thetaA E n c)⁻¹ := by
      simp only [twConj]
      group
    rw [e]
    exact Set.mul_mem_mul (Set.mul_mem_mul hc hk) (Set.inv_mem_inv.2 (mem_image_of_mem _ hc))
  have hex : ∃ γ, twConj (thetaE E n) γ d = δ := ⟨γ, rfl⟩
  have hp : twConj (thetaE E n) (pick δ) d = δ := by
    simp only [pick, dif_pos hex]
    exact hex.choose_spec
  set p := pick δ with hpdef
  have ht : γ * p⁻¹ ∈ twCent (thetaE E n) d := by
    change twConj (thetaE E n) (γ * p⁻¹) d = d
    calc twConj (thetaE E n) (γ * p⁻¹) d = twConj (thetaE E n) p⁻¹ δ := twConj_mul' _ _ _ _
      _ = twConj (thetaE E n) p⁻¹ (twConj (thetaE E n) p d) := by rw [hp]
      _ = twConj (thetaE E n) (p * p⁻¹) d := (twConj_mul' _ _ _ _).symm
      _ = d := by simp [twConj]
  refine ⟨⟨ratGL E n (γ * p⁻¹), ⟨_, ht, rfl⟩⟩, ?_⟩
  refine mem_iUnion₂.2 ⟨δ, hδK, c, hc, ?_⟩
  simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv]
  group
  rfl

end Rational

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem chiT_ratGL (hM : Mahler) {n : ℕ} (τ : ℝ) (t : GL (Fin n) E) (x : GA E n) :
    chiT τ (ratGL E n t * x) = chiT τ x := by
  have h := (hM E n τ).2.1 t x
  by_cases hx : x ∈ cutSet E n τ
  · simp [chiT, hx, h.2 hx]
  · simp [chiT, hx, mt h.1 hx]

theorem sliceTerm_of (hM : Mahler) : SliceTerm := by
  intro E _ _ _ a b _ _ _ _ μ₁ _ μ₂ _ τ r φ d₁ d₂ hφ
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E a
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E b
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E a
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E b
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E a
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E b
  haveI := discreteTopology_ratCent d₁
  haveI := discreteTopology_ratCent d₂
  haveI := countable_ratCent d₁
  haveI := countable_ratCent d₂
  have c₁ : Measurable (chiT τ : GA E a → ℂ) :=
    measurable_one.indicator (hM E a τ).1.measurableSet
  have c₂ : Measurable (chiT τ : GA E b → ℂ) :=
    measurable_one.indicator (hM E b τ).1.measurableSet
  set t₁ : GA E a → GA E a := fun x => twConj (thetaA E a) x (ratGL E a d₁) with ht₁
  set t₂ : GA E b → GA E b := fun y => twConj (thetaA E b) y (ratGL E b d₂) with ht₂
  have ct₁ : Continuous t₁ := continuous_twConj _
  have ct₂ : Continuous t₂ := continuous_twConj _
  set F : GA E a × GA E b → ℂ := fun z => chiT τ z.1 * chiT τ z.2 * φ (t₁ z.1, t₂ z.2) with hFdef
  have hFm : Measurable F :=
    ((c₁.comp measurable_fst).mul (c₂.comp measurable_snd)).mul
      (hφ.cont.comp ((ct₁.comp continuous_fst).prodMk (ct₂.comp continuous_snd))).measurable
  have i₁ : ∀ h ∈ ratCent d₁, ∀ x y, F (h * x, y) = F (x, y) := by
    intro h hh x y
    have e₁ : chiT τ (h * x) = chiT τ x := by
      obtain ⟨t, -, rfl⟩ := hh
      exact chiT_ratGL hM τ t x
    simp only [hFdef, ht₁, e₁, twConj_ratCent d₁ hh x]
  have i₂ : ∀ h ∈ ratCent d₂, ∀ x y, F (x, h * y) = F (x, y) := by
    intro h hh x y
    have e₂ : chiT τ (h * y) = chiT τ y := by
      obtain ⟨t, -, rfl⟩ := hh
      exact chiT_ratGL hM τ t y
    simp only [hFdef, ht₂, e₂, twConj_ratCent d₂ hh y]
  obtain ⟨B, hB⟩ := hφ.supp.exists_bound_of_continuous hφ.cont
  have hchi : ∀ {n : ℕ} (x : GA E n), ‖chiT τ x‖ ≤ 1 := by
    intro n x
    by_cases hx : x ∈ cutSet E n τ <;> simp [chiT, hx]
  have hbd : ∀ z, ‖F z‖ ≤ B := by
    intro z
    simp only [hFdef, norm_mul]
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (t₁ z.1, t₂ z.2))
    calc ‖chiT τ z.1‖ * ‖chiT τ z.2‖ * ‖φ (t₁ z.1, t₂ z.2)‖ ≤ 1 * 1 * B := by
          gcongr
          · exact hchi _
          · exact hchi _
          · exact hB _
      _ = B := by ring
  have hK₁ : IsCompact (Prod.fst '' tsupport φ) := hφ.supp.isCompact.image continuous_fst
  have hK₂ : IsCompact (Prod.snd '' tsupport φ) := hφ.supp.isCompact.image continuous_snd
  obtain ⟨S₁, s₁, hS₁⟩ := exists_compact_cover hM τ d₁ hK₁
  obtain ⟨S₂, s₂, hS₂⟩ := exists_compact_cover hM τ d₂ hK₂
  have hS : ∀ x y, F (x, y) ≠ 0 →
      (∃ h : ratCent d₁, (h : GA E a)⁻¹ * x ∈ S₁) ∧ ∃ h : ratCent d₂, (h : GA E b)⁻¹ * y ∈ S₂ := by
    intro x y hne
    have hx : x ∈ cutSet E a τ := by
      by_contra hn
      exact hne (by simp [hFdef, chiT, hn])
    have hy : y ∈ cutSet E b τ := by
      by_contra hn
      exact hne (by simp [hFdef, chiT, hn])
    have hφ0 : φ (t₁ x, t₂ y) ≠ 0 := fun h0 => hne (by simp [hFdef, h0])
    have hmem := subset_tsupport _ hφ0
    exact ⟨hS₁ x hx ⟨_, hmem, rfl⟩, hS₂ y hy ⟨_, hmem, rfl⟩⟩
  have key := quotIntegral_prod (μ₁ := μ₁) (μ₂ := μ₂) (ratCent d₁) (ratCent d₂) hFm i₁ i₂ hbd
    s₁.isClosed.measurableSet s₂.isClosed.measurableSet s₁.measure_lt_top.ne s₂.measure_lt_top.ne hS
  refine ⟨key.1.trans ?_, key.2.trans ?_⟩
  · congr 1
    funext y
    rw [cutTerm, ← quotIntegral_const_mul]
    congr 1
    funext x
    simp only [hFdef]
    ring
  · congr 1
    funext x
    rw [cutTerm, ← quotIntegral_const_mul]
    congr 1
    funext y
    simp only [hFdef]
    ring

end Main

end GlobalTheory.CompanionTheory.SliceFubini

end
