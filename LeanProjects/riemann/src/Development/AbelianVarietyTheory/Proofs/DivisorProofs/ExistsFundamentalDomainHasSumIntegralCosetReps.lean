import Mathlib
open MeasureTheory
open scoped Pointwise

namespace GlobalTheory

theorem exists_fundamentalDomain_hasSum_integral_cosetReps :
    ∀ {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) [μ.IsMulLeftInvariant], (∀ g : G, Measurable (fun x => g * x)) →
    ∀ (Γ Q : Subgroup G), Countable Γ → Q ≤ Γ → ∀ D₀ : Set G, IsFundamentalDomain Γ D₀ μ →
    ∀ {ι : Type} [Countable ι] (m : ι → G), (∀ i, m i ∈ Γ) → (∀ δ ∈ Γ, ∃! i, δ * (m i)⁻¹ ∈ Q) →
    ∃ D₁ : Set G, IsFundamentalDomain Q D₁ μ ∧ ∀ f : G → ℂ, AEStronglyMeasurable f μ →
      (∀ i, IntegrableOn (fun g => ‖f (m i * g)‖) D₀ μ) → Summable (fun i => ∫ g in D₀, ‖f (m i * g)‖ ∂μ) →
      IntegrableOn f D₁ μ ∧ HasSum (fun i => ∫ g in D₀, f (m i * g) ∂μ) (∫ g in D₁, f g ∂μ) := by
  intro G _ _ μ _ hm Γ Q hΓ hQΓ D₀ hD₀ ι _ γ hγ hbij
  have hmp : ∀ g : G, MeasurePreserving (fun x => g * x) μ μ := fun g =>
    ⟨hm g, Measure.IsMulLeftInvariant.map_mul_left_eq_self g⟩
  haveI : MeasurableConstSMul G G := ⟨fun g => hm g⟩
  have hemb : ∀ g : G, MeasurableEmbedding (fun x => g * x) := fun g =>
    measurableEmbedding_const_smul (α := G) g
  have hI1 : ∀ H : Subgroup G, MeasurableConstSMul H G := fun H => ⟨fun g => hm (g : G)⟩
  have hI2 : ∀ H : Subgroup G, SMulInvariantMeasure H G μ := fun H =>
    ⟨fun g s hs => (hmp (g : G)).measure_preimage hs.nullMeasurableSet⟩
  haveI := hI1 Γ
  haveI := hI1 Q
  haveI := hI2 Γ
  haveI := hI2 Q
  set s : ι → Set G := fun i => (⟨γ i, hγ i⟩ : Γ) • D₀ with hs
  have hsim : ∀ i, s i = (fun x => γ i * x) '' D₀ := fun i => rfl
  have hnull : ∀ i, NullMeasurableSet (s i) μ := fun i => hD₀.nullMeasurableSet_smul _
  have hkey : ∀ (q q' : Q) (i j : ι), (q : G) * γ i = q' * γ j → q = q' ∧ i = j := by
    intro q q' i j h
    have hij : i = j := by
      obtain ⟨k, -, hk⟩ := hbij (γ i) (hγ i)
      have h1 := hk i (by simp)
      have h2 := hk j (by
        have : γ i * (γ j)⁻¹ = (q : G)⁻¹ * q' := by
          rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← h, inv_mul_cancel_left]
        show γ i * (γ j)⁻¹ ∈ Q
        rw [this]
        exact Q.mul_mem (Q.inv_mem q.2) q'.2)
      rw [h1, h2]
    subst hij
    exact ⟨Subtype.ext (mul_right_cancel h), rfl⟩
  have hsm : ∀ (q : Q) (i : ι),
      q • s i = (⟨(q : G) * γ i, Γ.mul_mem (hQΓ q.2) (hγ i)⟩ : Γ) • D₀ := by
    intro q i
    show (fun x => (q : G) * x) '' ((fun x => γ i * x) '' D₀) =
      (fun x => ((q : G) * γ i) * x) '' D₀
    rw [Set.image_image]
    simp only [mul_assoc]
  have hdisj : Pairwise (Function.onFun (AEDisjoint μ) s) := by
    intro i j hij
    refine hD₀.aedisjoint (fun h => hij ?_)
    exact (hkey 1 1 i j (by simpa using congrArg Subtype.val h)).2
  have hD₁ : IsFundamentalDomain Q (⋃ i, s i) μ := by
    refine ⟨NullMeasurableSet.iUnion hnull, ?_, ?_⟩
    · filter_upwards [hD₀.ae_covers] with x hx
      obtain ⟨δ, hδ⟩ := hx
      obtain ⟨i, hi, -⟩ := hbij (δ : G)⁻¹ (Γ.inv_mem δ.2)
      refine ⟨⟨_, Q.inv_mem hi⟩, Set.mem_iUnion.2 ⟨i, ⟨δ • x, hδ, ?_⟩⟩⟩
      show γ i * ((δ : G) * x) = ((δ : G)⁻¹ * (γ i)⁻¹)⁻¹ * x
      simp [mul_assoc]
    · intro q q' hqq
      show AEDisjoint μ (q • ⋃ i, s i) (q' • ⋃ i, s i)
      rw [Set.smul_set_iUnion, Set.smul_set_iUnion, AEDisjoint.iUnion_left_iff]
      intro i
      rw [AEDisjoint.iUnion_right_iff]
      intro j
      rw [hsm, hsm]
      refine hD₀.aedisjoint (fun h => hqq ?_)
      exact (hkey q q' i j (congrArg Subtype.val h)).1
  refine ⟨⋃ i, s i, hD₁, ?_⟩
  intro f hf hint hsum
  have hnorm_i : ∀ i, IntegrableOn (fun x => ‖f x‖) (s i) μ := fun i => by
    rw [hsim]
    exact ((hmp (γ i)).integrableOn_image (hemb (γ i))).2 (hint i)
  have hfi : ∀ i, IntegrableOn f (s i) μ := fun i =>
    (integrable_norm_iff hf.restrict).1 (hnorm_i i)
  have heq : ∀ i, ∫ x in s i, f x ∂μ = ∫ g in D₀, f (γ i * g) ∂μ := fun i => by
    rw [hsim, (hmp (γ i)).setIntegral_image_emb (hemb (γ i))]
  have heqn : ∀ i, ∫ x in s i, ‖f x‖ ∂μ = ∫ g in D₀, ‖f (γ i * g)‖ ∂μ := fun i => by
    rw [hsim, (hmp (γ i)).setIntegral_image_emb (hemb (γ i))]
  have hfU : IntegrableOn f (⋃ i, s i) μ :=
    integrableOn_iUnion_of_summable_integral_norm hfi (by simpa only [heqn] using hsum)
  refine ⟨hfU, ?_⟩
  have := hasSum_integral_iUnion_ae hnull hdisj hfU
  simpa only [heq] using this

end GlobalTheory
