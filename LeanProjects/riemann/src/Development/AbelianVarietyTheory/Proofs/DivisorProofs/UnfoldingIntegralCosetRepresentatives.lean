import Mathlib
open MeasureTheory
open scoped Pointwise

namespace GlobalTheory

theorem integral_tsum_cosetReps_eq_integral_fundamentalDomain :
    ∀ {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) [μ.IsMulLeftInvariant],
    (∀ g : G, Measurable (fun x => g * x)) →
    ∀ (Γ Q : Subgroup G), Countable Γ → Q ≤ Γ → ∀ (D₀ D : Set G),
    IsFundamentalDomain Γ D₀ μ → IsFundamentalDomain Q D μ →
    ∀ {ι : Type} [Countable ι] (γ : ι → G), (∀ i, γ i ∈ Γ) → (∀ δ ∈ Γ, ∃! i, δ * (γ i)⁻¹ ∈ Q) →
    ∀ f : G → ℂ, (∀ q ∈ Q, ∀ g, f (q * g) = f g) → IntegrableOn f D μ →
      ∫ g in D₀, ∑' i, f (γ i * g) ∂μ = ∫ g in D, f g ∂μ := by
  intro G _ _ μ _ hm Γ Q hΓ hQΓ D₀ D hD₀ hD ι _ γ hγ hbij f hf hfi
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
  haveI : Countable Q := (Subgroup.inclusion_injective hQΓ).countable
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
  have hf' : ∀ (q : Q) (x : G), f (q • x) = f x := fun q x => hf q q.2 x
  have hfi₁ : IntegrableOn f (⋃ i, s i) μ := (hD.integrableOn_iff hD₁ hf').1 hfi
  rw [hD.setIntegral_eq hD₁ hf', integral_iUnion_ae hnull hdisj hfi₁]
  have hint : ∀ i, IntegrableOn (fun g => f (γ i * g)) D₀ μ := fun i =>
    ((hmp (γ i)).integrableOn_image (hemb (γ i))).1
      (hsim i ▸ hfi₁.mono_set (Set.subset_iUnion s i))
  rw [integral_tsum (fun i => (hint i).aestronglyMeasurable)]
  · refine tsum_congr fun i => ?_
    rw [hsim, (hmp (γ i)).setIntegral_image_emb (hemb (γ i))]
  · have h1 : ∑' i, ∫⁻ a in D₀, ‖f (γ i * a)‖ₑ ∂μ = ∫⁻ a in ⋃ i, s i, ‖f a‖ₑ ∂μ := by
      rw [lintegral_iUnion₀ hnull hdisj]
      refine tsum_congr fun i => ?_
      rw [hsim]
      exact (hmp (γ i)).setLIntegral_comp_emb (hemb (γ i)) (fun a => ‖f a‖ₑ) D₀
    rw [h1]
    exact hfi₁.2.ne

end GlobalTheory
