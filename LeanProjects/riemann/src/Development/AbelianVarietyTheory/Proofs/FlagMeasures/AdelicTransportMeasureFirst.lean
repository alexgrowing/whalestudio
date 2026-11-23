import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsCuspHom
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentQuotientInvariantProbability
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryGroupModelsEquiv

noncomputable section

namespace GlobalTheory.CuspCompare

open MeasureTheory Matrix

section Measure

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
  [SecondCountableTopology H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]

theorem right_invariant (Γ : Subgroup H) [Countable Γ] (μ : Measure H) [μ.IsHaarMeasure] {D : Set H}
    (hDm : MeasurableSet D) (hD : ∀ x : H, ∃! γ : Γ, γ • x ∈ D) (htop : μ D ≠ ⊤) : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have hfd : IsFundamentalDomain Γ D μ := IsFundamentalDomain.mk' hDm.nullMeasurableSet hD
  have hfd' : IsFundamentalDomain Γ ((fun y => y * g) ⁻¹' D) μ :=
    IsFundamentalDomain.mk' ((measurable_mul_const g) hDm).nullMeasurableSet fun x => by
      have := hD (x * g)
      simpa [Subgroup.smul_def, mul_assoc] using this
  have h0 : μ D ≠ 0 := hfd.measure_ne_zero (NeZero.ne μ)
  have : IsFiniteMeasureOnCompacts (Measure.map (fun y => y * g) μ) := ⟨fun K hK => by
    rw [Measure.map_apply (measurable_mul_const g) hK.measurableSet]
    exact ((Homeomorph.mulRight g).isCompact_preimage.2 hK).measure_lt_top⟩
  have h := Measure.isMulLeftInvariant_eq_smul (Measure.map (fun y => y * g) μ) μ
  set c := (Measure.map (fun y => y * g) μ).haarScalarFactor μ
  have h1 : Measure.map (fun y => y * g) μ D = μ D := by
    rw [Measure.map_apply (measurable_mul_const g) hDm]
    exact hfd'.measure_eq hfd
  rw [h] at h1
  have h2 : (c : ENNReal) = 1 := by
    have : (c : ENNReal) * μ D = 1 * μ D := by simpa using h1
    exact (ENNReal.mul_left_inj h0 htop).1 this
  have h3 : c = 1 := by exact_mod_cast h2
  rw [h, h3, one_smul]

theorem quot_unique (Γ : Subgroup H) [Countable Γ]
    (hfin : ∀ K : Set H, IsCompact K → (K ∩ (Γ : Set H)).Finite) (μ : Measure H) [μ.IsHaarMeasure]
    {C D : Set H} (hC : IsCompact C) (hDm : MeasurableSet D) (hDC : D ⊆ C) (hD : ∀ x : H, ∃! γ : Γ, γ • x ∈ D)
    (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ f : H → ℂ, (∀ γ ∈ Γ, ∀ y, f (γ * y) = f y) → ∀ g : H, ∫ m, f (m * g) ∂ν = ∫ m, f m ∂ν) :
    ∃ c : NNReal, ∀ f : H → ℂ, Measurable f → (∀ γ ∈ Γ, ∀ y, f (γ * y) = f y) →
      ∫ m, f m ∂ν = c • ∫ m in D, f m ∂μ := by
  have := right_invariant Γ μ hDm hD (ne_top_of_le_ne_top hC.measure_lt_top.ne (measure_mono hDC))
  have hset : ∀ S : Set H, MeasurableSet S → (∀ γ ∈ Γ, ∀ y, γ * y ∈ S ↔ y ∈ S) → ∀ g : H,
      ν ((fun y => y * g) ⁻¹' S) = ν S := by
    intro S hS hi g
    have h1 := hν (S.indicator 1) (fun γ hγ y => by
      by_cases h : y ∈ S <;> simp [h, hi γ hγ y]) g
    have h2 : (fun m => S.indicator (1 : H → ℂ) (m * g)) = ((fun y => y * g) ⁻¹' S).indicator fun _ => 1 := by
      funext m; rfl
    rw [h2, integral_indicator_const _ (measurable_mul_const g hS), Pi.one_def, integral_indicator_const _ hS] at h1
    simp only [Complex.real_smul, mul_one, Complex.ofReal_inj] at h1
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h1
  have hlin : ∀ F : H → ENNReal, Measurable F → (∀ γ ∈ Γ, ∀ y, F (γ * y) = F y) → ∀ g : H,
      ∫⁻ m, F (m * g) ∂ν = ∫⁻ m, F m ∂ν := by
    intro F hF hi g
    have hF' : Measurable fun m => F (m * g) := hF.comp (measurable_mul_const g)
    have : ν.map (fun m => F (m * g)) = ν.map F := by
      ext B hB
      rw [Measure.map_apply hF' hB, Measure.map_apply hF hB]
      exact hset (F ⁻¹' B) (hF hB) (fun γ hγ y => by simp only [Set.mem_preimage, hi γ hγ y]) g
    exact (lintegral_map measurable_id hF').symm.trans (this ▸ lintegral_map measurable_id hF)
  set κ : Measure H := Measure.sum fun γ : Γ => ν.map fun y => (γ : H) * y with hκ
  have hκa : ∀ A, MeasurableSet A → κ A = ∑' γ : Γ, ν ((fun y => (γ : H) * y) ⁻¹' A) := fun A hA => by
    rw [hκ, Measure.sum_apply _ hA]
    exact tsum_congr fun γ => Measure.map_apply (measurable_const_mul _) hA
  have hκl : ∀ A, MeasurableSet A → κ A = ∫⁻ m, ∑' γ : Γ, A.indicator (1 : H → ENNReal) (γ * m) ∂ν := fun A hA => by
    rw [hκa A hA, lintegral_tsum (f := fun (γ : Γ) m => A.indicator (1 : H → ENNReal) (γ * m)) fun γ =>
      ((measurable_one.indicator hA).comp (measurable_const_mul (γ : H))).aemeasurable]
    exact tsum_congr fun γ => (lintegral_indicator_one (measurable_const_mul (γ : H) hA)).symm
  have hR : κ.IsMulRightInvariant := ⟨fun g => by
    ext A hA
    rw [Measure.map_apply (measurable_mul_const g) hA, hκl _ hA, hκl _ (measurable_mul_const g hA),
      ← hlin (fun m => ∑' γ : Γ, A.indicator (1 : H → ENNReal) (γ * m)) _ _ g]
    · refine lintegral_congr fun m => tsum_congr fun γ => ?_
      rw [← mul_assoc]; rfl
    · exact Measurable.ennreal_tsum fun γ => (measurable_one.indicator hA).comp (measurable_const_mul (γ : H))
    · intro δ hδ y
      rw [← (Equiv.mulRight (⟨δ, hδ⟩ : Γ)).tsum_eq fun γ : Γ => A.indicator (1 : H → ENNReal) (γ * y)]
      exact tsum_congr fun γ => by rw [← mul_assoc]; rfl⟩
  have hkey : ∀ D' : Set H, MeasurableSet D' → (∀ x : H, ∃! γ : Γ, γ • x ∈ D') → ∀ S, MeasurableSet S →
      (∀ γ ∈ Γ, ∀ y, γ * y ∈ S ↔ y ∈ S) → κ (S ∩ D') = ν S := by
    intro D' hm hD' S hS hi
    rw [hκa _ (hS.inter hm), ← measure_iUnion _ fun γ : Γ => measurable_const_mul (γ : H) (hS.inter hm)]
    · congr 1
      ext y
      simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_inter_iff]
      exact ⟨fun ⟨γ, h, _⟩ => (hi γ γ.2 y).1 h, fun h =>
        let ⟨γ, h1, _⟩ := hD' y
        ⟨γ, (hi γ γ.2 y).2 h, h1⟩⟩
    · intro γ δ hne
      exact Set.disjoint_left.2 fun y h1 h2 => hne ((hD' y).unique h1.2 h2.2)
  have hK : IsFiniteMeasureOnCompacts κ := ⟨fun K hK => by
    have hF := hfin _ ((hC.prod hK).image (f := fun p : H × H => p.1 * p.2⁻¹) (by fun_prop))
    have hF' := hF.preimage (f := (Subtype.val : Γ → H)) Subtype.val_injective.injOn
    refine (measure_mono (t := ⋃ δ ∈ _, (fun y => ((δ : Γ) : H) * y) ⁻¹' D) fun y hy => ?_).trans_lt
      (measure_biUnion_lt_top hF' fun δ _ => ?_)
    · obtain ⟨δ, h, -⟩ := hD y
      exact Set.mem_biUnion (x := δ) ⟨⟨((δ : H) * y, y), ⟨hDC h, hy⟩, by simp⟩, δ.2⟩ h
    · have := hkey ((fun y => (δ : H) * y) ⁻¹' D) (measurable_const_mul _ hDm) (fun x => by
        obtain ⟨γ, h1, h2⟩ := hD x
        refine ⟨δ⁻¹ * γ, ?_, fun ε hε => ?_⟩
        · show (δ : H) * (((δ : H)⁻¹ * γ) * x) ∈ D
          rw [← mul_assoc, mul_inv_cancel_left]; exact h1
        · rw [← h2 (δ * ε) (by
            show ((δ : H) * ε) * x ∈ D
            rw [mul_assoc]; exact hε), inv_mul_cancel_left]) Set.univ MeasurableSet.univ (by simp)
      rw [Set.univ_inter] at this
      rw [this]; exact measure_lt_top _ _⟩
  have : μ.inv.IsHaarMeasure := {}
  have h := Measure.isMulLeftInvariant_eq_smul κ.inv μ.inv
  set c := κ.inv.haarScalarFactor μ.inv
  have h' : κ = c • μ := by
    have := congrArg Measure.inv h
    rw [Measure.inv_inv] at this
    rw [this]
    conv_rhs => rw [← Measure.inv_inv μ]
    exact Measure.map_smul _ _ _
  refine ⟨c, fun f hf hi => ?_⟩
  have e : ν.map f = (κ.restrict D).map f := by
    ext B hB
    rw [Measure.map_apply hf hB, Measure.map_apply hf hB, Measure.restrict_apply (hf hB),
      hkey D hDm hD _ (hf hB) fun γ hγ y => by simp only [Set.mem_preimage, hi γ hγ y]]
  have e1 := integral_map (μ := ν) hf.aemeasurable (f := id) measurable_id.aestronglyMeasurable
  have e2 := integral_map (μ := κ.restrict D) hf.aemeasurable (f := id) measurable_id.aestronglyMeasurable
  rw [e, e2, h', Measure.restrict_smul, integral_smul_nnreal_measure] at e1
  exact e1.symm

theorem constTerm_iff {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (ι : H →* G) (hι : Topology.IsClosedEmbedding ι) (Γ N : Set G) (hN : N = Set.range ι) (hΓc : Γ.Countable)
    (hfin : ∀ K : Set G, IsCompact K → (K ∩ Γ).Finite) (Λ : Subgroup H) (hΛ : ∀ h, h ∈ Λ ↔ ι h ∈ Γ)
    (C : Set G) (hC : IsCompact C) (hcov : ∀ m ∈ N, ∃ γ ∈ Γ ∩ N, γ⁻¹ * m ∈ C)
    (μG : Measure G) [μG.IsOpenPosMeasure] (f : G → ℂ) (hf : Continuous f) (hi : ∀ γ ∈ Γ, ∀ y, f (γ * y) = f y) :
    (∀ (μ : Measure H) (𝓕 : Set H), μ.IsHaarMeasure → IsFundamentalDomain Λ 𝓕 μ →
        ∀ g, ∫ n in 𝓕, f (ι n * g) ∂μ = 0) ↔
      ∀ ν : Measure G, (IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν Nᶜ = 0 ∧
        ∀ f : G → ℂ, (∀ γ ∈ Γ ∩ N, ∀ y, f (γ * y) = f y) → ∀ n₀ ∈ N, ∫ m, f (m * n₀) ∂ν = ∫ m, f m ∂ν) →
        ∀ᵐ x ∂μG, ∫ m, f (m * x) ∂ν = 0 := by
  subst hN
  have hemb : MeasurableEmbedding ι := hι.measurableEmbedding
  have : Countable Λ := by
    refine (hΓc.preimage_of_injOn (f := ι) hι.injective.injOn).mono (s₁ := (Λ : Set H)) fun h hh => (hΛ h).1 hh
  have hfin' : ∀ K : Set H, IsCompact K → (K ∩ (Λ : Set H)).Finite := fun K hK =>
    ((hfin _ (hK.image hι.continuous)).preimage (f := ι) hι.injective.injOn).subset
      fun x hx => ⟨⟨x, hx.1, rfl⟩, (hΛ x).1 hx.2⟩
  have hC' := hι.isCompact_preimage hC
  obtain ⟨D, hDm, hDC, hD⟩ := GlobalTheory.UnipQuot.exists_domain Λ hfin' _ hC' fun m => by
    obtain ⟨_, ⟨h1, γ, rfl⟩, h2⟩ := hcov _ ⟨m, rfl⟩
    exact ⟨γ⁻¹, Λ.inv_mem ((hΛ γ).2 h1), by simpa using h2⟩
  have hinv : ∀ x, ∀ γ ∈ Λ, ∀ y, f (ι (γ * y) * x) = f (ι y * x) := fun x γ hγ y => by
    rw [map_mul, mul_assoc, hi _ ((hΛ γ).1 hγ)]
  constructor
  · rintro h ν ⟨h1, -, h2, h3⟩
    refine Filter.Eventually.of_forall fun x => ?_
    have e : (ν.comap ι).map ι = ν := by
      rw [hemb.map_comap]
      exact Measure.restrict_eq_self_of_ae_mem h2
    have : IsFiniteMeasure (ν.comap ι) := ⟨by
      rw [hemb.comap_apply]; exact measure_lt_top _ _⟩
    obtain ⟨c, hc⟩ := quot_unique Λ hfin' Measure.haar hC' hDm hDC hD (ν.comap ι) fun u hu g => by
      have := h3 (Function.extend ι u 0) ?_ (ι g) ⟨g, rfl⟩
      · rw [← e, hemb.integral_map, hemb.integral_map] at this
        simpa only [← map_mul, hι.injective.extend_apply] using this
      · rintro _ ⟨hγ, γ, rfl⟩ y
        by_cases hy : ∃ a, ι a = y
        · obtain ⟨a, rfl⟩ := hy
          rw [← map_mul, hι.injective.extend_apply, hι.injective.extend_apply, hu _ ((hΛ γ).2 hγ)]
        · rw [Function.extend_apply' _ _ _ hy, Function.extend_apply']
          · rfl
          · rintro ⟨a, ha⟩
            exact hy ⟨γ⁻¹ * a, by rw [map_mul, ha, map_inv, inv_mul_cancel_left]⟩
    rw [← e, hemb.integral_map, hc (fun m => f (ι m * x))
      (hf.comp (hι.continuous.mul continuous_const)).measurable (hinv x),
      h _ D inferInstance (IsFundamentalDomain.mk' hDm.nullMeasurableSet hD), smul_zero]
  · intro h μ 𝓕 hμ h𝓕 g
    have hfd : IsFundamentalDomain Λ D μ := IsFundamentalDomain.mk' hDm.nullMeasurableSet hD
    have htop : μ D < ⊤ := (measure_mono hDC).trans_lt hC'.measure_lt_top
    have := right_invariant Λ μ hDm hD htop.ne
    have : IsFiniteMeasure (μ.restrict D) := ⟨by simpa using htop⟩
    have h1 := h ((μ.restrict D).map ι) ⟨inferInstance, ?_, ?_, ?_⟩
    · simp only [hemb.integral_map] at h1
      have hc : Continuous fun x => ∫ m in D, f (ι m * x) ∂μ := by
        have := continuous_parametric_integral_of_continuous (μ := μ.restrict D)
          (f := fun (x : G) (m : H) => f (ι m * x))
          (hf.comp ((hι.continuous.comp continuous_snd).mul continuous_fst)) hC'
        rwa [Measure.restrict_restrict hC'.measurableSet, Set.inter_eq_right.2 hDC] at this
      have h2 := (hc.ae_eq_iff_eq μG continuous_zero).1 h1
      rw [h𝓕.setIntegral_eq hfd fun γ y => hinv g γ γ.2 y]
      exact congrFun h2 g
    · intro h0
      have := congrArg (fun m : Measure G => m Set.univ) h0
      simp only [hemb.map_apply] at this
      exact hfd.measure_ne_zero (NeZero.ne μ) (by simpa using this)
    · rw [hemb.map_apply]; simp
    · rintro u hu _ ⟨g, rfl⟩
      rw [hemb.integral_map, hemb.integral_map]
      have hfd' : IsFundamentalDomain Λ ((fun y => y * g⁻¹) ⁻¹' D) μ :=
        IsFundamentalDomain.mk' ((measurable_mul_const g⁻¹) hDm).nullMeasurableSet fun x => by
          have := hD (x * g⁻¹)
          simpa [Subgroup.smul_def, mul_assoc] using this
      have h1 := (measurableEmbedding_mulRight g).setIntegral_map (μ := μ) (fun m => u (ι m))
        ((fun y => y * g⁻¹) ⁻¹' D)
      have h2 : (fun y : H => y * g) ⁻¹' ((fun y => y * g⁻¹) ⁻¹' D) = D := by
        ext y; simp
      rw [map_mul_right_eq_self μ g, h2] at h1
      simp only [← map_mul]
      rw [← h1]
      exact hfd'.setIntegral_eq hfd fun γ x => by
        show u (ι ((γ : H) * x)) = _
        rw [map_mul, hu _ ⟨(hΛ γ).1 γ.2, γ, rfl⟩]

end Measure

section Algebra

variable {E A : Type} [CommRing E] [CommRing A] (ι : E →+* A) {n r : ℕ}
  {C R : Matrix (Fin n) (Fin r) E} {B L : Matrix (Fin r) (Fin n) E}

def UnipEq (C R : Matrix (Fin n) (Fin r) E) (B L : Matrix (Fin r) (Fin n) E) (m : Matrix (Fin n) (Fin n) A) : Prop :=
  m * C.map ι = 0 ∧ B.map ι * m = 0 ∧ (1 - C * L).map ι * m * (1 - R * B).map ι = 0

theorem map_one_sub (C : Matrix (Fin n) (Fin r) E) (L : Matrix (Fin r) (Fin n) E) :
    (1 - C * L).map ι = 1 - C.map ι * L.map ι := by
  rw [Matrix.map_sub _ (map_sub ι), Matrix.map_mul, Matrix.map_one _ (map_zero ι) (map_one ι)]

theorem col_iff (hL : L * C = 1) (y : Fin n → A) : (∃ a, y = C.map ι *ᵥ a) ↔ (1 - C * L).map ι *ᵥ y = 0 := by
  have h : L.map ι * C.map ι = 1 := by rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero ι) (map_one ι)]
  rw [map_one_sub, sub_mulVec, one_mulVec, sub_eq_zero]
  constructor
  · rintro ⟨a, rfl⟩
    rw [mulVec_mulVec, Matrix.mul_assoc, h, Matrix.mul_one]
  · exact fun e => ⟨_, e.trans (mulVec_mulVec _ _ _).symm⟩

theorem ker_fix {y : Fin n → A} (hy : B.map ι *ᵥ y = 0) : (1 - R * B).map ι *ᵥ y = y := by
  rw [map_one_sub, sub_mulVec, one_mulVec, ← mulVec_mulVec, hy, mulVec_zero, sub_zero]

theorem perp_cond (hL : L * C = 1) (hR : B * R = 1) (m : Matrix (Fin n) (Fin n) A) :
    ((∀ y, B.map ι *ᵥ y = 0 → ∃ a, m *ᵥ y = C.map ι *ᵥ a) ↔ (1 - C * L).map ι * m * (1 - R * B).map ι = 0) ∧
    ((∀ x : Fin n → E, B *ᵥ x = 0 → ∃ a, m *ᵥ (fun i => ι (x i)) = C.map ι *ᵥ a) ↔
      (1 - C * L).map ι * m * (1 - R * B).map ι = 0) := by
  have h1 : (1 - C * L).map ι * m * (1 - R * B).map ι = 0 →
      ∀ y, B.map ι *ᵥ y = 0 → ∃ a, m *ᵥ y = C.map ι *ᵥ a := fun h y hy => by
    rw [col_iff ι hL, ← ker_fix ι (R := R) hy, mulVec_mulVec, mulVec_mulVec, h, zero_mulVec]
  have h2 : (∀ y, B.map ι *ᵥ y = 0 → ∃ a, m *ᵥ y = C.map ι *ᵥ a) →
      ∀ x : Fin n → E, B *ᵥ x = 0 → ∃ a, m *ᵥ (fun i => ι (x i)) = C.map ι *ᵥ a := fun h x hx => by
    refine h _ (funext fun i => ?_)
    have := RingHom.map_mulVec ι B x i
    rw [hx] at this
    simpa [Function.comp_def] using this.symm
  have h3 : (∀ x : Fin n → E, B *ᵥ x = 0 → ∃ a, m *ᵥ (fun i => ι (x i)) = C.map ι *ᵥ a) →
      (1 - C * L).map ι * m * (1 - R * B).map ι = 0 := fun h => by
    have h0 : B * (1 - R * B) = 0 := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hR, Matrix.mul_one, Matrix.one_mul, sub_self]
    ext i j
    have := (col_iff ι hL _).1 (h (fun k => (1 - R * B : Matrix (Fin n) (Fin n) E) k j) (funext fun k => congrFun (congrFun h0 k) j))
    rw [mulVec_mulVec] at this
    exact congrFun this i
  exact ⟨⟨fun h => h3 (h2 h), h1⟩, h3, fun h => h2 (h1 h)⟩

theorem UnipEq.map {A' : Type} [CommRing A'] {ι' : E →+* A'} (ψ : A →+* A') (hψ : ∀ x, ψ (ι x) = ι' x)
    {m : Matrix (Fin n) (Fin n) A} (h : UnipEq ι C R B L m) : UnipEq ι' C R B L (m.map ψ) := by
  obtain rfl : ι' = ψ.comp ι := RingHom.ext fun x => (hψ x).symm
  obtain ⟨h1, h2, h3⟩ := h
  simp only [UnipEq, RingHom.coe_comp, ← Matrix.map_map, ← Matrix.map_mul, h1, h2, h3, Matrix.map_zero _ (map_zero ψ),
    and_self]

theorem UnipEq.of_map {J A' A'' : Type} [CommRing A'] [CommRing A''] {ι' : J → E →+* A'} {ι'' : E →+* A''}
    (ψ : J → A →+* A') (χ : A →+* A'') (hψ : ∀ j x, ψ j (ι x) = ι' j x) (hχ : ∀ x, χ (ι x) = ι'' x)
    (hinj : ∀ z, (∀ j, ψ j z = 0) → χ z = 0 → z = 0)
    {m : Matrix (Fin n) (Fin n) A} (h : ∀ j, UnipEq (ι' j) C R B L (m.map (ψ j)))
    (h' : UnipEq ι'' C R B L (m.map χ)) : UnipEq ι C R B L m := by
  obtain rfl : ι' = fun j => (ψ j).comp ι := funext fun j => RingHom.ext fun x => (hψ j x).symm
  obtain rfl : ι'' = χ.comp ι := RingHom.ext fun x => (hχ x).symm
  simp only [UnipEq, RingHom.coe_comp, ← Matrix.map_map, ← Matrix.map_mul] at h h'
  refine ⟨?_, ?_, ?_⟩ <;> ext a b
  exacts [hinj _ (fun j => congrFun (congrFun (h j).1 a) b) (congrFun (congrFun h'.1 a) b),
    hinj _ (fun j => congrFun (congrFun (h j).2.1 a) b) (congrFun (congrFun h'.2.1 a) b),
    hinj _ (fun j => congrFun (congrFun (h j).2.2 a) b) (congrFun (congrFun h'.2.2 a) b)]

theorem mem_span_iff (C : Matrix (Fin n) (Fin r) E) (y : Fin n → A) :
    y ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (Submodule.span E (Set.range C.col) : Set _)) ↔
      ∃ a, y = C.map ι *ᵥ a := by
  have key : Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) ''
      (Submodule.span E (Set.range C.col) : Set _)) = (C.map ι).mulVecLin.range := by
    apply le_antisymm
    · rw [Submodule.span_le, ← Matrix.range_mulVecLin]
      rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨ι ∘ a, funext fun i => (RingHom.map_mulVec ι C a i).symm⟩
    · rw [Matrix.range_mulVecLin]
      refine Submodule.span_mono ?_
      rintro _ ⟨k, rfl⟩
      exact ⟨Cᵀ k, Submodule.subset_span ⟨k, rfl⟩, rfl⟩
  rw [key]
  exact ⟨fun ⟨a, h⟩ => ⟨a, h.symm⟩, fun ⟨a, h⟩ => ⟨a, h.symm⟩⟩

open Formalism.UG in
theorem hform_mulVec (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (C : Matrix (Fin n) (Fin r) A) (a : Fin r → A)
    (y : Fin n → A) : hform s J (C *ᵥ a) y = (s ∘ a) ⬝ᵥ ((cT s C * J) *ᵥ y) := by
  have h1 : ∀ x, hform s J x y = (s ∘ x) ⬝ᵥ (J *ᵥ y) := fun x => by
    simp only [hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc, Function.comp_apply]
  have h2 : s ∘ (C *ᵥ a) = C.map s *ᵥ (s ∘ a) := funext fun i => RingHom.map_mulVec s C a i
  rw [h1, h2, ← mulVec_mulVec, dotProduct_mulVec _ (cT s C), cT, vecMul_transpose]

open Formalism.UG in
theorem perp_iff (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (C : Matrix (Fin n) (Fin r) A) (y : Fin n → A) :
    (∀ x, (∃ a, x = C *ᵥ a) → hform s J x y = 0) ↔ (cT s C * J) *ᵥ y = 0 := by
  constructor
  · intro h
    funext k
    have := h _ ⟨Pi.single k 1, rfl⟩
    rw [hform_mulVec] at this
    have e : s ∘ (Pi.single k 1 : Fin r → A) = Pi.single k 1 := funext fun j => by
      by_cases hj : j = k <;> simp [hj]
    rwa [e, single_one_dotProduct] at this
  · rintro h _ ⟨a, rfl⟩
    rw [hform_mulVec, h, dotProduct_zero]

theorem forall_mulVec_eq_zero {p q : ℕ} (m : Matrix (Fin p) (Fin q) A) : (∀ a, m *ᵥ a = 0) ↔ m = 0 :=
  ⟨fun h => by
    ext i j
    simpa using congrFun (h (Pi.single j 1)) i, fun h a => by rw [h, zero_mulVec]⟩

end Algebra

open Formalism.MainNotions.S Formalism.UG NumberField
open scoped TensorProduct

theorem inUnipRad_iff (I : AutInst) {A : Type} [CommRing A] (ι : I.E →+* A) (s : A →+* A)
    (hs : ∀ x, s (ι x) = ι (star x)) {r : ℕ} {C R : Matrix (Fin I.n) (Fin r) I.E} {L : Matrix (Fin r) (Fin I.n) I.E}
    (hL : L * C = 1) (hR : cT (starRingEnd I.E) C * I.J * R = 1) (g : Matrix (Fin I.n) (Fin I.n) A) :
    I.InUnipRad s (I.J.map ι) (Submodule.span A ((fun w : Fin I.n → I.E => fun i => ι (w i)) ''
      (Submodule.span I.E (Set.range C.col) : Set _))) g ↔
      UnipEq ι C R (cT (starRingEnd I.E) C * I.J) L (g - 1) := by
  have e : cT s (C.map ι) * I.J.map ι = (cT (starRingEnd I.E) C * I.J).map ι := by
    rw [Matrix.map_mul]
    congr 1
    ext a b
    exact hs _
  simp only [AutInst.InUnipRad, mem_span_iff, Set.mem_setOf_eq, perp_iff, e, UnipEq]
  refine and_congr ?_ (and_comm.trans (and_congr ?_ (perp_cond ι hL hR _).1))
  · rw [← forall_mulVec_eq_zero]
    exact ⟨fun h a => by rw [← mulVec_mulVec]; exact h _ ⟨a, rfl⟩, fun h => by
      rintro _ ⟨a, rfl⟩; rw [mulVec_mulVec]; exact h a⟩
  · simp only [mulVec_mulVec, forall_mulVec_eq_zero]

theorem exists_inverses {E : Type} [Field E] (σ : E →+* E) {n r : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) {C : Matrix (Fin n) (Fin r) E} (hC : LinearIndependent E Cᵀ) :
    ∃ (L : Matrix (Fin r) (Fin n) E) (R : Matrix (Fin n) (Fin r) E), L * C = 1 ∧ cT σ C * J * R = 1 := by
  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' C)
    (LinearMap.ker_eq_bot.2 (Matrix.mulVec_injective_iff.2 hC))
  have h : LinearMap.toMatrix' l * C = 1 := by
    have := congrArg LinearMap.toMatrix' hl
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  refine ⟨_, J⁻¹ * cT σ (LinearMap.toMatrix' l), h, ?_⟩
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hJ.isUnit, ← cT_mul, h, cT_one]

theorem adele_tens_eq_zero {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] (z : (A × B) ⊗[F] E)
    (a : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z = 0)
    (b : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z = 0) : z = 0 := by
  have hz : ∀ z : (A × B) ⊗[F] E, z = LinearMap.rTensor E (LinearMap.inl F A B)
        (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
      LinearMap.rTensor E (LinearMap.inr F A B)
        (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul x y => simp [← TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add]
      rw [add_add_add_comm, ← hx, ← hy]
  rw [hz z, a, b, map_zero, map_zero, add_zero]

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (HA AF Ainf inclR fstA sndA) in

theorem mem_NA_iff (I : AutInst) (θ : InfinitePlace I.F → (Ainf I.F ⊗[I.F] I.E →+* ℂ))
    (hθ : ∀ v, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) (θ v)) (h : HA (AF I.F) I.cm.sig I.J) (x : I.GA)
    (hf : I.fmat x.2 = (Formalism.MainNotions.StandardLattice.finMat I.cm.sig I.J h).map (Algebra.TensorProduct.comm I.F _ _))
    (hi : ∀ v, I.P v * uMat (x.1 v) * (I.P v)⁻¹ = Formalism.MainNotions.StandardLattice.infMat I.cm.sig I.J (θ v) h)
    {r : ℕ} {C R : Matrix (Fin I.n) (Fin r) I.E} {L : Matrix (Fin r) (Fin I.n) I.E}
    (hL : L * C = 1) (hR : cT (starRingEnd I.E) C * I.J * R = 1) :
    x ∈ I.NA (Submodule.span I.E (Set.range C.col)) ↔
      UnipEq (inclR (F := I.F) (AF I.F)) C R (cT (starRingEnd I.E) C * I.J) L ((HA.mat _ _ _ h).1 - 1) := by
  have hcm := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND I.F I.E I.cm).1
  obtain ⟨e, he, -⟩ := GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv I.F I.E I.cm.sig _ I.φ θ hcm
    (GlobalTheory.GaussDecay.isCMFam_of_over _ hcm I.φ I.φ_over) hθ
  let p : ∀ v : InfinitePlace I.F, AF I.F ⊗[I.F] I.E →+* ℂ := fun v =>
    (θ v).comp (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E)).toRingHom
  let q : AF I.F ⊗[I.F] I.E →+* I.E ⊗[I.F] Af I.F :=
    (Algebra.TensorProduct.comm I.F _ _).toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.map (sndA I.F) (AlgHom.id I.F I.E)).toRingHom
  have hp : ∀ v x, p v (inclR (F := I.F) (AF I.F) x) = I.φ v x := fun v x => by
    rw [← (hθ v).1]
    change θ v (Algebra.TensorProduct.map _ _ ((1 : AF I.F) ⊗ₜ[I.F] x)) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  have hq : ∀ x, q (inclR (F := I.F) (AF I.F) x) = inclE (F := I.F) (Af I.F) x := fun x => by
    change Algebra.TensorProduct.comm I.F _ _ (Algebra.TensorProduct.map _ _ ((1 : AF I.F) ⊗ₜ[I.F] x)) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  have e1 : ∀ v, I.P v * uMat (x.1 v) * (I.P v)⁻¹ - 1 = ((HA.mat _ _ _ h).1 - 1).map (p v) := fun v => by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), hi]
    rfl
  have e2 : I.fmat x.2 - 1 = ((HA.mat _ _ _ h).1 - 1).map q := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), hf]
    rfl
  unfold AutInst.NA
  rw [Set.mem_setOf_eq, inUnipRad_iff I (inclE (F := I.F) (Af I.F)) _ (fun _ => rfl) hL hR, e2,
    forall_congr' fun v => inUnipRad_iff I (I.φ v) _ (fun y => (hcm.2.2.2 (I.φ v) y).symm) hL hR _]
  simp only [e1]
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun H => ⟨fun v => H.map _ _ (hp v), H.map _ _ hq⟩⟩
  refine UnipEq.of_map _ p q hp hq (fun z hz hz' => ?_) h1 h2
  refine adele_tens_eq_zero (A := Ainf I.F) (B := Af I.F) z ?_ ?_
  · refine e.injective (funext fun v => ?_)
    rw [he, he, map_zero]
    exact hz v
  · exact (Algebra.TensorProduct.comm I.F _ _).injective (hz'.trans (map_zero _).symm)

theorem isIsot_iff (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) :
    I.IsIsot W ↔ ∃ (r : ℕ) (C : Matrix (Fin I.n) (Fin r) I.E), (0 < r ∧ LinearIndependent I.E Cᵀ ∧
      cT (starRingEnd I.E) C * I.J * C = 0) ∧ Submodule.span I.E (Set.range C.col) = W := by
  have key : ∀ (r : ℕ) (C : Matrix (Fin I.n) (Fin r) I.E),
      (∀ x ∈ Submodule.span I.E (Set.range C.col), ∀ y ∈ Submodule.span I.E (Set.range C.col),
        hform (starRingEnd I.E) I.J x y = 0) ↔ cT (starRingEnd I.E) C * I.J * C = 0 := fun r C => by
    rw [← Matrix.range_mulVecLin, ← forall_mulVec_eq_zero]
    constructor
    · intro h a
      rw [← mulVec_mulVec, ← perp_iff]
      rintro _ ⟨b, rfl⟩
      exact h _ ⟨b, rfl⟩ _ ⟨a, rfl⟩
    · rintro h _ ⟨b, rfl⟩ _ ⟨a, rfl⟩
      exact (perp_iff _ _ C _).2 ((mulVec_mulVec _ _ _).trans (h a)) _ ⟨b, rfl⟩
  constructor
  · rintro ⟨h1, h2⟩
    let b := Module.finBasis I.E W
    let C : Matrix (Fin I.n) (Fin (Module.finrank I.E W)) I.E := fun i k => (b k).1 i
    have e : Submodule.span I.E (Set.range C.col) = W := by
      have : Set.range C.col = W.subtype '' Set.range b := by rw [← Set.range_comp]; rfl
      rw [this, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
    refine ⟨_, C, ⟨Nat.pos_of_ne_zero fun h => h1 (Submodule.finrank_eq_zero.1 h),
      b.linearIndependent.map' W.subtype W.ker_subtype, (key _ C).1 (by rw [e]; exact h2)⟩, e⟩
  · rintro ⟨r, C, ⟨h1, h2, h3⟩, rfl⟩
    refine ⟨fun h => ?_, (key r C).2 h3⟩
    exact h2.ne_zero ⟨0, h1⟩ (Submodule.span_eq_bot.1 h _ ⟨⟨0, h1⟩, rfl⟩)

theorem mem_closure_iff_of_equiv {G G' : Type} [Group G] [Group G'] (T : G' ≃* G) {A : Set G}
    (hA : ∃ N : Subgroup G, (N : Set G) = A) {S : Set G'} (hS : ∀ g, g ∈ S ↔ T g ∈ A) (h : G') :
    h ∈ Subgroup.closure S ↔ T h ∈ A := by
  obtain ⟨N, rfl⟩ := hA
  have e : S = (N.comap T.toMonoidHom : Set G') := Set.ext hS
  rw [e, Subgroup.closure_eq]
  exact Iff.rfl

theorem constTerm_iff_inst (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf]
    {G' : Type} [Group G'] [TopologicalSpace G'] [MeasurableSpace G'] [BorelSpace G'] (T : G' ≃* I.GA)
    (hT : Continuous T ∧ Continuous T.symm) (Q N : Subgroup G') (hQ : ∀ h, h ∈ Q ↔ T h ∈ I.GFset)
    (W : Submodule I.E (Fin I.n → I.E)) (hW : I.IsIsot W) (hm : ∀ h, h ∈ N ↔ T h ∈ I.NA W)
    (f : I.GA → ℂ) (hf : Continuous f) (hi : ∀ γ ∈ I.GFset, ∀ y, f (γ * y) = f y) :
    (∀ (μ : Measure N) (𝓕 : Set N), μ.IsHaarMeasure → IsFundamentalDomain (Q.subgroupOf N) 𝓕 μ →
        ∀ g, ∫ n in 𝓕, f (T ((n : G') * g)) ∂μ = 0) ↔
      ∀ ν, I.IsNQuotMeas W ν → ∀ᵐ x ∂(I.muA μf), ∫ m, f (m * x) ∂ν = 0 := by
  obtain ⟨hT2, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology I
  have : BorelSpace I.GA := inferInstance
  have : (Measure.pi fun v => Formalism.REAL.muG (I.ε v)).IsHaarMeasure := Measure.pi.isHaarMeasure _
  have : (I.muA μf).IsHaarMeasure := Measure.prod.instIsHaarMeasure _ _
  obtain ⟨Γ, hΓ, hΓc, hfin, -⟩ := GlobalTheory.T.rationalUnitaryPoints_discrete_fundamentalDomain I
  let T' : G' ≃ₜ I.GA := ⟨T.toEquiv, hT.1, hT.2⟩
  have : IsTopologicalGroup G' := T'.isInducing.topologicalGroup T
  obtain ⟨-, hcl, -, -, K, hK, -, hcov⟩ := GlobalTheory.T.strong_approximation_unitaryUnipotentRadical I W hW
  have hcl' : IsClosed (N : Set G') := by
    have e : (N : Set G') = T ⁻¹' I.NA W := Set.ext hm
    rw [e]
    exact hcl.preimage hT.1
  have hι : Topology.IsClosedEmbedding (T.toMonoidHom.comp N.subtype) :=
    T'.isClosedEmbedding.comp hcl'.isClosedEmbedding_subtypeVal
  have := hι.locallyCompactSpace
  have := hι.isEmbedding.secondCountableTopology
  have := hι.isEmbedding.t2Space
  refine Iff.trans ?_ (constTerm_iff _ hι I.GFset _ ?_ (hΓ ▸ Set.countable_coe_iff.1 hΓc) hfin (Q.subgroupOf N)
    (fun h => hQ h) K hK hcov _ f hf hi)
  · refine forall₄_congr fun μ 𝓕 _ _ => ?_
    rw [← T.toEquiv.forall_congr_right]
    simp only [map_mul]
    rfl
  · ext y
    obtain ⟨h, rfl⟩ := T.surjective y
    exact ⟨fun hh => ⟨⟨h, (hm h).2 hh⟩, rfl⟩, fun ⟨k, hk⟩ => hk ▸ (hm k).1 k.2⟩

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev
open scoped InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.CuspCompare
