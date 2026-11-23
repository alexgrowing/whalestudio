import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMulRightInvariantOfCovolumeOne
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise

namespace GlobalTheory.UnipAvg

section Covolume

variable {U : Type*} [Group U] [MeasurableSpace U] [MeasurableMul₂ U] [MeasurableInv U]

theorem measurePreserving_mulEquiv_of_covolume_one (ν : Measure U) [SigmaFinite ν] [ν.IsMulLeftInvariant]
    (U₀ : Subgroup U) [Countable U₀] {D : Set U} (hD : IsFundamentalDomain U₀ D ν) (hνD : ν D = 1)
    (c : U ≃* U) (hc : Measurable c) (hc' : Measurable c.symm)
    (h₁ : ∀ b ∈ U₀, c b ∈ U₀) (h₂ : ∀ b ∈ U₀, c.symm b ∈ U₀) : MeasurePreserving c ν ν := by
  haveI : SMulInvariantMeasure U₀ U ν := ⟨fun γ s _ => measure_preimage_mul ν (γ : U) s⟩
  let e : U ≃ᵐ U := ⟨c.toEquiv, hc, hc'⟩
  haveI : SigmaFinite (ν.map c) := e.sigmaFinite_map
  haveI : (ν.map c).IsMulLeftInvariant := ⟨fun g => by
    rw [map_map (measurable_const_mul g) hc]
    conv_rhs => rw [← map_mul_left_eq_self ν (c.symm g), map_map hc (measurable_const_mul _)]
    congr 1
    ext x
    simp⟩
  have h := measure_eq_div_smul (ν.map c) ν (s := D) (by rw [hνD]; exact one_ne_zero)
    (by rw [hνD]; exact ENNReal.one_ne_top)
  have hq : QuasiMeasurePreserving c ν ν := ⟨hc, by rw [h]; exact smul_absolutelyContinuous⟩
  have hD' : IsFundamentalDomain U₀ (c ⁻¹' D) ν :=
    hD.preimage_of_equiv hq (e := fun b : U₀ => (⟨c.symm b, h₂ b b.2⟩ : U₀))
      ⟨fun b b' hb => Subtype.ext (c.symm.injective (congrArg Subtype.val hb)),
        fun b => ⟨⟨c b, h₁ b b.2⟩, Subtype.ext (c.symm_apply_apply b)⟩⟩
      (fun b x => by
        change c (c.symm b * x) = b * c x
        simp)
  have h1 : (ν.map c) D = 1 := by
    have : (ν.map c) D = ν (c ⁻¹' D) := e.map_apply (μ := ν) D
    rw [this, hD'.measure_eq hD, hνD]
  refine ⟨hc, ?_⟩
  rw [h, h1, hνD]; simp

theorem setLIntegral_mul_right_of_covolume_one (ν : Measure U) [SigmaFinite ν] [ν.IsMulLeftInvariant]
    (U₀ : Subgroup U) [Countable U₀] {D : Set U} (hD : IsFundamentalDomain U₀ D ν) (hνD : ν D = 1)
    (f : U → ℝ≥0∞) (hf : ∀ b ∈ U₀, ∀ u, f (b * u) = f u) (v : U) :
    ∫⁻ u in D, f (u * v) ∂ν = ∫⁻ u in D, f u ∂ν := by
  haveI : SMulInvariantMeasure U₀ U ν := ⟨fun γ s _ => measure_preimage_mul ν (γ : U) s⟩
  haveI := isMulRightInvariant_of_covolume_one ν U₀ hD hνD
  have hD' : IsFundamentalDomain U₀ ((· * v) ⁻¹' D) ν :=
    hD.preimage_of_equiv (quasiMeasurePreserving_mul_right ν v) (e := id) Function.bijective_id
      (fun g x => mul_assoc (g : U) x v)
  rw [hD.setLIntegral_eq hD' (fun u => f (u * v)) (fun b x => by
    change f ((b : U) * x * v) = _
    rw [mul_assoc, hf _ b.2])]
  exact (measurePreserving_mul_right ν v).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.mulRight v).measurableEmbedding f D

end Covolume

theorem setLIntegral_add_left_of_periodic {A : Type*} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A]
    (ν : Measure A) [ν.IsAddLeftInvariant] (A₀ : AddSubgroup A) [Countable A₀] {D : Set A}
    (hD : IsAddFundamentalDomain A₀ D ν) (f : A → ℝ≥0∞) (hf : ∀ b ∈ A₀, ∀ y, f (b + y) = f y) (t : A) :
    ∫⁻ y in D, f (t + y) ∂ν = ∫⁻ y in D, f y ∂ν := by
  haveI : VAddInvariantMeasure A₀ A ν := ⟨fun γ s _ => measure_preimage_add ν (γ : A) s⟩
  have hD' : IsAddFundamentalDomain A₀ ((t + ·) ⁻¹' D) ν :=
    hD.preimage_of_equiv (measurePreserving_add_left ν t).quasiMeasurePreserving (e := id) Function.bijective_id
      (fun g x => add_left_comm t (g : A) x)
  rw [hD.setLIntegral_eq hD' (fun u => f (t + u)) (fun b x => by
    change f (t + ((b : A) + x)) = _
    rw [add_left_comm, hf _ b.2])]
  exact (measurePreserving_add_left ν t).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.addLeft t).measurableEmbedding f D

theorem exists_covolume_one_of_cocompact {U : Type*} [Group U] [TopologicalSpace U] [IsTopologicalGroup U]
    [LocallyCompactSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U]
    (U₀ : Subgroup U) [DiscreteTopology U₀] {K : Set U} (hK : IsCompact K) (hcov : ∀ u, ∃ b ∈ U₀, b * u ∈ K) :
    ∃ (ν : Measure U) (D : Set U), SigmaFinite ν ∧ ν.IsMulLeftInvariant ∧ IsFundamentalDomain U₀ D ν ∧ ν D = 1 := by
  haveI := countable_of_discrete_subgroup U₀
  obtain ⟨D, -, -, hD⟩ := exists_isFundamentalDomain_subgroup U₀
  let m : Measure U := haar
  haveI : SMulInvariantMeasure U₀ U m := ⟨fun γ s _ => measure_preimage_mul m (γ : U) s⟩
  have h0 : m D ≠ 0 := (hD m).measure_ne_zero (NeZero.ne m)
  have h1 : m D ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt ?_ (hK.measure_lt_top (μ := m)))
    rw [(hD m).measure_eq_tsum K]
    refine le_trans (measure_mono fun u hu => ?_) (measure_iUnion_le _)
    obtain ⟨b, hb, hbu⟩ := hcov u
    exact mem_iUnion.2 ⟨(⟨b, hb⟩ : U₀)⁻¹, mem_inv_smul_set_iff.2 hbu, hu⟩
  haveI : ((m D)⁻¹ • m).IsHaarMeasure := IsHaarMeasure.smul m (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0)
  exact ⟨(m D)⁻¹ • m, D, inferInstance, inferInstance, hD _, by
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 h1]⟩

theorem setLIntegral_average_abelian_quotient : ∀ (G A : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableNeg A] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (Γ U : Subgroup G) [DiscreteTopology Γ], IsClosed (U : Set G) → (∀ γ ∈ Γ, ∀ u ∈ U, γ⁻¹ * u * γ ∈ U) → (∃ K : Set G, IsCompact K ∧ ∀ u ∈ U, ∃ γ ∈ Γ, γ ∈ U ∧ γ * u ∈ K) → ∀ (ι : A → G), (∀ x y, ι (x + y) = ι x * ι y) → Measurable ι → (∀ x, ι x ∈ U) → ∀ (ν : Measure A) [SigmaFinite ν] [ν.IsAddLeftInvariant] (A₀ : AddSubgroup A) [Countable A₀], (∀ b ∈ A₀, ι b ∈ Γ) → ∀ (D : Set A), IsAddFundamentalDomain A₀ D ν → ν D = 1 → ∀ (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (Φ : G → ENNReal), Measurable Φ → (∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) → (∀ u ∈ U, ∃ y : A, ∀ g, Φ (u * g) = Φ (ι y * g)) → ∫⁻ g in 𝓕, Φ g ∂μ = ∫⁻ g in 𝓕, ∫⁻ y in D, Φ (ι y * g) ∂ν ∂μ := by
  intro G A _ _ _ _ _ _ _ _ _ _ _ _ μ _ _ Γ U _ hU hnorm ⟨K, hK, hcov⟩ ι hadd hιm hιU ν _ _ A₀ _ hA₀ D hD hνD 𝓕 h𝓕
    Φ hΦ hinv hact
  haveI := countable_of_discrete_subgroup Γ
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  haveI : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology (U : Set G)
  haveI : DiscreteTopology (Γ.subgroupOf U) :=
    DiscreteTopology.of_continuous_injective (f := fun b : Γ.subgroupOf U => (⟨(b : U), b.2⟩ : Γ))
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      (fun b b' h => Subtype.ext (Subtype.ext (congrArg (fun z : Γ => (z : G)) h)))
  haveI := countable_of_discrete_subgroup (Γ.subgroupOf U)
  obtain ⟨m, E, _, _, hE, hmE⟩ := exists_covolume_one_of_cocompact (Γ.subgroupOf U)
    (hU.isClosedEmbedding_subtypeVal.isCompact_preimage hK) (fun u => by
      obtain ⟨γ, h1, h2, h3⟩ := hcov u u.2
      exact ⟨⟨γ, h2⟩, h1, h3⟩)
  have hconj : ∀ a ∈ (Γ : Set G), ∃ c : U → U, MeasurePreserving c m m ∧
      ∀ u, U.subtype (c u) = a⁻¹ * U.subtype u * a := by
    intro a ha
    have ha' : ∀ u ∈ U, a * u * a⁻¹ ∈ U := fun u hu => by simpa using hnorm a⁻¹ (Γ.inv_mem ha) u hu
    let c : U ≃* U :=
      { toFun := fun u => ⟨a⁻¹ * u * a, hnorm a ha u u.2⟩
        invFun := fun u => ⟨a * u * a⁻¹, ha' u u.2⟩
        left_inv := fun u => Subtype.ext (by simp only; group)
        right_inv := fun u => Subtype.ext (by simp only; group)
        map_mul' := fun u v => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
    exact ⟨c, measurePreserving_mulEquiv_of_covolume_one m _ hE hmE c
      (((measurable_subtype_coe.const_mul _).mul_const _).subtype_mk)
      (((measurable_subtype_coe.const_mul _).mul_const _).subtype_mk)
      (fun b hb => Γ.mul_mem (Γ.mul_mem (Γ.inv_mem ha) hb) ha)
      (fun b hb => Γ.mul_mem (Γ.mul_mem ha hb) (Γ.inv_mem ha)), fun _ => rfl⟩
  rw [setLIntegral_average U.subtype Subtype.val_injective measurable_subtype_coe μ m Γ (Γ.subgroupOf U)
    (fun b hb => hb) Γ (fun γ hγ => ⟨γ, hγ, 1, one_mem _, by simp⟩) hconj hE hmE h𝓕 Φ hΦ hinv]
  refine lintegral_congr fun g => ?_
  calc ∫⁻ u in E, Φ (U.subtype u * g) ∂m = ∫⁻ _y in D, ∫⁻ u in E, Φ ((u : G) * g) ∂m ∂ν := by simp [hνD]
    _ = ∫⁻ y in D, ∫⁻ u in E, Φ ((u : G) * (ι y * g)) ∂m ∂ν := by
        refine lintegral_congr fun y => ?_
        rw [← setLIntegral_mul_right_of_covolume_one m _ hE hmE (fun u => Φ ((u : G) * g))
          (fun b hb u => by rw [Subgroup.coe_mul, mul_assoc, hinv (b : G) hb]) ⟨ι y, hιU y⟩]
        simp only [Subgroup.coe_mul, mul_assoc]
    _ = ∫⁻ u in E, ∫⁻ y in D, Φ ((u : G) * (ι y * g)) ∂ν ∂m :=
        lintegral_lintegral_swap (hΦ.comp ((measurable_subtype_coe.comp measurable_snd).mul
          ((hιm.comp measurable_fst).mul_const g))).aemeasurable
    _ = ∫⁻ _u in E, ∫⁻ y in D, Φ (ι y * g) ∂ν ∂m := by
        refine lintegral_congr fun u => ?_
        obtain ⟨t, ht⟩ := hact u u.2
        rw [← setLIntegral_add_left_of_periodic ν A₀ hD (fun y => Φ (ι y * g))
          (fun b hb y => by rw [hadd, mul_assoc, hinv _ (hA₀ b hb)]) t]
        simp only [ht, hadd, mul_assoc]
    _ = ∫⁻ y in D, Φ (ι y * g) ∂ν := by simp [hmE]

end GlobalTheory.UnipAvg
