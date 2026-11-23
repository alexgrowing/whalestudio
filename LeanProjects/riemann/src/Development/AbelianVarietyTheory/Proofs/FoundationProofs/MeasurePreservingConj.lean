import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal Pointwise

noncomputable section

namespace GlobalTheory.Cusp.Stages

section Alg

variable {G : Type} [Group G] (Γ : Subgroup G) {N N' : Subgroup G}

def pairs (hn : ∀ p ∈ N, ∀ n ∈ N', p * n * p⁻¹ ∈ N') : Subgroup (N × N) where
  carrier := {p | (p.1 : G) ∈ Γ ∧ (p.2 : G) ∈ Γ ∧ (p.1 : G) * (p.2 : G)⁻¹ ∈ N'}
  one_mem' := ⟨one_mem _, one_mem _, by simp⟩
  mul_mem' := fun {p q} hp hq => ⟨mul_mem hp.1 hq.1, mul_mem hp.2.1 hq.2.1, by
    simpa [mul_assoc] using mul_mem (hn _ p.1.2 _ hq.2.2) hp.2.2⟩
  inv_mem' := fun {p} hp => ⟨inv_mem hp.1, inv_mem hp.2.1, by
    simpa [mul_assoc] using hn _ (inv_mem p.1.2) _ (inv_mem hp.2.2)⟩

variable {Γ} {hn : ∀ p ∈ N, ∀ n ∈ N', p * n * p⁻¹ ∈ N'}

instance : MulAction (pairs Γ hn) (N' × N) where
  smul p z := (⟨p.1.1 * z.1 * (p.1.2 : G)⁻¹, by
    simpa [mul_assoc] using mul_mem p.2.2.2 (hn _ p.1.2.2 _ z.1.2)⟩, p.1.2 * z.2)
  one_smul z := Prod.ext (Subtype.ext (by
    change ((1 : N) : G) * _ * ((1 : N) : G)⁻¹ = _; simp)) (one_mul _)
  mul_smul p q z := Prod.ext (Subtype.ext (by
    change ((p.1.1 * q.1.1 : N) : G) * _ * ((p.1.2 * q.1.2 : N) : G)⁻¹ =
      p.1.1 * (q.1.1 * z.1 * (q.1.2 : G)⁻¹) * (p.1.2 : G)⁻¹
    simp [mul_assoc])) (mul_assoc _ _ _)

theorem smul_fst (p : pairs Γ hn) (z : N' × N) : ((p • z).1 : G) = p.1.1 * z.1 * (p.1.2 : G)⁻¹ := rfl

theorem smul_snd (p : pairs Γ hn) (z : N' × N) : (p • z).2 = p.1.2 * z.2 := rfl

theorem existsUnique_prod (hle : N' ≤ N) {A : Set N'} {B : Set N}
    (hA : ∀ m : N', ∃! δ : Γ.subgroupOf N', (δ : N') * m ∈ A)
    (hB : ∀ n : N, ∃! γ : Γ.subgroupOf N, (γ : N) * n ∈ B) (z : N' × N) :
    ∃! p : pairs Γ hn, p • z ∈ A ×ˢ B := by
  obtain ⟨b, hb, hb'⟩ := hB z.2
  obtain ⟨d, hd, hd'⟩ := hA ⟨(b.1 : G) * z.1 * (b.1 : G)⁻¹, hn _ b.1.2 _ z.1.2⟩
  refine ⟨⟨(⟨d.1.1, hle d.1.2⟩ * b.1, b.1), Γ.mul_mem (show d.1.1 ∈ Γ from d.2) (show b.1.1 ∈ Γ from b.2), b.2, by simp⟩, ⟨?_, hb⟩, fun q hq => ?_⟩
  · convert hd using 1
    exact Subtype.ext (by simp [smul_fst, mul_assoc])
  · have e : q.1.2 = b.1 := congrArg Subtype.val (hb' ⟨q.1.2, q.2.2.1⟩ hq.2)
    have e' := hd' ⟨⟨_, q.2.2.2⟩, mul_mem q.2.1 (inv_mem q.2.2.1)⟩ (by
      convert hq.1 using 1
      exact Subtype.ext (by simp [smul_fst, mul_assoc, e]))
    refine Subtype.ext (Prod.ext (Subtype.ext ?_) e)
    simp [← e', e]

theorem existsUnique_shear (hle : N' ≤ N) {A : Set N'} {B : Set N}
    (hA : ∀ m : N', ∃! δ : Γ.subgroupOf N', (δ : N') * m ∈ A)
    (hB : ∀ n : N, ∃! γ : Γ.subgroupOf N, (γ : N) * n ∈ B) (z : N' × N) :
    ∃! p : pairs Γ hn, p • z ∈ (fun z : N' × N => (z.1, Subgroup.inclusion hle z.1 * z.2)) ⁻¹' (A⁻¹ ×ˢ B) := by
  let s : pairs Γ hn → pairs Γ hn := fun p => ⟨p.1.swap, p.2.2.1, p.2.1, by simpa using inv_mem p.2.2.2⟩
  have hs : ∀ p : pairs Γ hn, p • z ∈ (fun z : N' × N => (z.1, Subgroup.inclusion hle z.1 * z.2)) ⁻¹' (A⁻¹ ×ˢ B) ↔
      s p • (z.1⁻¹, Subgroup.inclusion hle z.1 * z.2) ∈ A ×ˢ B := fun p => by
    refine and_congr (Iff.of_eq (congrArg (· ∈ A) (Subtype.ext ?_))) (Iff.of_eq (congrArg (· ∈ B) (Subtype.ext ?_)))
    · simp [smul_fst, s, mul_assoc]
    · simp [smul_fst, smul_snd, s, mul_assoc]
  obtain ⟨p, hp, hp'⟩ := existsUnique_prod (hn := hn) hle hA hB (z.1⁻¹, Subgroup.inclusion hle z.1 * z.2)
  exact ⟨s p, (hs _).2 hp, fun q hq => congrArg s (hp' _ ((hs q).1 hq))⟩

end Alg

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ N N' : Subgroup G} [DiscreteTopology Γ] [LocallyCompactSpace N]
  [LocallyCompactSpace N']

theorem constTermOn_eq' {μ : Measure N} [μ.IsHaarMeasure] {𝓕 : Set N} (h : IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ)
    {φ : G → ℂ} {x : G} (hφ : LeftInv (Γ.subgroupOf N) fun n : N => φ (n * x)) :
    constTermOn Γ N φ x = (μ.real 𝓕)⁻¹ • ∫ n in 𝓕, φ (n * x) ∂μ := by
  rw [constTermOn, probMeasure_eq μ, integral_smul_measure, quotMeasure_univ h, integral_quotMeasure h,
    ENNReal.toReal_inv, measureReal_def]
  exact congrArg _ (integral_congr_ae (.of_forall hφ.descend_mk))

theorem measurePreserving_conj (hc : Cocompact Γ N) (μ : Measure N) [μ.IsHaarMeasure] {γ : G} (hγ : γ ∈ Γ)
    (h1 : ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (h2 : ∀ n ∈ N, γ⁻¹ * n * γ⁻¹⁻¹ ∈ N) :
    MeasurePreserving (fun n : N => (⟨γ * n * γ⁻¹, h1 _ n.2⟩ : N)) μ μ := by
  let e : N ≃ₜ* N :=
    { toFun := fun n => ⟨γ * n * γ⁻¹, h1 _ n.2⟩
      invFun := fun n => ⟨γ⁻¹ * n * γ, by simpa using h2 _ n.2⟩
      left_inv := fun n => by simp [mul_assoc]
      right_inv := fun n => by simp [mul_assoc]
      map_mul' := fun a b => by simp [mul_assoc]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hm : Measurable e := e.continuous.measurable
  have h := isFundamentalDomain_stdDom (Γ.subgroupOf N) μ
  have he := Measure.isMulLeftInvariant_eq_smul (μ.map e) μ
  have h' : IsFundamentalDomain (Γ.subgroupOf N) (e ⁻¹' stdDom (Γ.subgroupOf N)) μ :=
    h.preimage_of_equiv ⟨hm, he ▸ Measure.smul_absolutelyContinuous⟩
      (e := fun δ => ⟨e.symm δ, mul_mem (mul_mem (inv_mem hγ) δ.2) hγ⟩)
      ⟨fun a b hab => Subtype.ext (e.symm.injective (congrArg Subtype.val hab)),
        fun δ => ⟨⟨e δ, mul_mem (mul_mem hγ δ.2) (inv_mem hγ)⟩, Subtype.ext (e.symm_apply_apply _)⟩⟩
      fun δ n => (map_mul e _ _).trans (congrArg (· * e n) (e.apply_symm_apply _))
  have h1 := h'.measure_eq h
  rw [← Measure.map_apply hm (measurableSet_stdDom _), he, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul, ENNReal.mul_eq_right (h.measure_ne_zero (NeZero.ne μ)) (hc.measure_ne_top h), ENNReal.coe_eq_one] at h1
  refine ⟨hm, ?_⟩
  change μ.map e = μ
  rw [he, h1, one_smul]

theorem integral_integral (hle : N' ≤ N) (hn : ∀ p ∈ N, ∀ n ∈ N', p * n * p⁻¹ ∈ N') (hc : Cocompact Γ N)
    (hc' : Cocompact Γ N') (μ : Measure N) [μ.IsHaarMeasure] (μ' : Measure N') [μ'.IsHaarMeasure]
    {φ : G → ℂ} (hφ : LeftInv Γ φ) (hφc : Continuous φ) (x : G) :
    ∫ n in stdDom (Γ.subgroupOf N), ∫ m in stdDom (Γ.subgroupOf N'), φ (m * (n * x)) ∂μ' ∂μ =
      μ'.real (stdDom (Γ.subgroupOf N'))⁻¹ • ∫ n in stdDom (Γ.subgroupOf N), φ (n * x) ∂μ := by
  have hp : ∀ p : pairs Γ hn, MeasurePreserving (fun z : N' × N => p • z) (μ'.prod μ) (μ'.prod μ) := fun p => by
    have := ((measurePreserving_mul_left μ' ⟨_, p.2.2.2⟩).comp (measurePreserving_conj hc' μ' p.2.2.1
      (hn _ p.1.2.2) (hn _ (inv_mem p.1.2.2)))).prod (measurePreserving_mul_left μ p.1.2)
    convert this using 1
    funext z
    exact Prod.ext (Subtype.ext (by simp [smul_fst, mul_assoc])) rfl
  have : MeasurableConstSMul (pairs Γ hn) (N' × N) := ⟨fun p => (hp p).measurable⟩
  have : SMulInvariantMeasure (pairs Γ hn) (N' × N) (μ'.prod μ) :=
    ⟨fun p s hs => (hp p).measure_preimage hs.nullMeasurableSet⟩
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : Countable (pairs Γ hn) :=
    Function.Injective.countable (f := fun p : pairs Γ hn => ((⟨_, p.2.1⟩, ⟨_, p.2.2.1⟩) : Γ × Γ)) fun p q h =>
      Subtype.ext (Prod.ext (Subtype.ext (congrArg (fun z : Γ × Γ => z.1.1) h))
        (Subtype.ext (congrArg (fun z : Γ × Γ => z.2.1) h)))
  have hA := measurableSet_stdDom (Γ.subgroupOf N')
  have hB := measurableSet_stdDom (Γ.subgroupOf N)
  have hi : Continuous (Subgroup.inclusion hle) := continuous_subtype_val.subtype_mk _
  have ht : MeasurePreserving (fun z : N' × N => (z.1, Subgroup.inclusion hle z.1 * z.2)) (μ'.prod μ) (μ'.prod μ) :=
    (MeasurePreserving.id μ').skew_product (g := fun m n => Subgroup.inclusion hle m * n)
      (Continuous.measurable (by fun_prop)) (.of_forall fun m => map_mul_left_eq_self μ _)
  have d1 := IsFundamentalDomain.mk' (μ := μ'.prod μ) (hA.prod hB).nullMeasurableSet
    (existsUnique_prod (hn := hn) hle (existsUnique_stdDom _) (existsUnique_stdDom _))
  have d2 := IsFundamentalDomain.mk' (μ := μ'.prod μ) (ht.measurable (hA.inv.prod hB)).nullMeasurableSet
    (existsUnique_shear (hn := hn) hle (existsUnique_stdDom _) (existsUnique_stdDom _))
  have e := d1.setIntegral_eq d2 (f := fun z : N' × N => φ (z.1 * (z.2 * x))) fun p z => by
    rw [smul_fst, smul_snd, ← hφ _ p.2.1 (z.1 * (z.2 * x))]
    simp [mul_assoc]
  have : IsFiniteMeasure (μ.restrict (stdDom (Γ.subgroupOf N))) :=
    isFiniteMeasure_restrict.2 (hc.measure_ne_top (isFundamentalDomain_stdDom _ _))
  have : IsFiniteMeasure (μ'.restrict (stdDom (Γ.subgroupOf N'))) :=
    isFiniteMeasure_restrict.2 (hc'.measure_ne_top (isFundamentalDomain_stdDom _ _))
  obtain ⟨K, hK, hs⟩ := id hc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := fun n : N => φ (n * x)) (by fun_prop)
  have hb : ∀ n : N, ‖φ (n * x)‖ ≤ C := fun n =>
    let ⟨γ, hγ, hk⟩ := hs n
    (congrArg norm (leftInv_integrand hφ x γ hγ n)).ge.trans (hC _ hk)
  rw [← Measure.prod_restrict, integral_prod_symm _ (.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) C
    (.of_forall fun z => by simpa [mul_assoc] using hb (Subgroup.inclusion hle z.1 * z.2)))] at e
  have e2 := integral_map (f := fun z : N' × N => φ (z.2 * x))
    (ht.restrict_preimage (hA.inv.prod hB)).aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))
  rw [(ht.restrict_preimage (hA.inv.prod hB)).map_eq, ← Measure.prod_restrict,
    integral_fun_snd (fun n : N => φ (n * x)), measureReal_restrict_apply_univ] at e2
  rw [e, e2]
  simp [mul_assoc]

theorem constTermOn_stages (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (Γ N N' : Subgroup G) [DiscreteTopology Γ] [LocallyCompactSpace N] [LocallyCompactSpace N'] (hle : N' ≤ N)
    (hn : ∀ p ∈ N, ∀ n ∈ N', p * n * p⁻¹ ∈ N') (hc : Cocompact Γ N) (hc' : Cocompact Γ N') (φ : G → ℂ)
    (hφ : LeftInv Γ φ) (hφc : Continuous φ) (x : G) :
    constTermOn Γ N φ x = constTermOn Γ N (constTermOn Γ N' φ) x := by
  have h := isFundamentalDomain_stdDom (Γ.subgroupOf N) Measure.haar
  have h' := isFundamentalDomain_stdDom (Γ.subgroupOf N') Measure.haar
  have h0 := ENNReal.toReal_ne_zero.2 ⟨h.measure_ne_zero (NeZero.ne _), hc.measure_ne_top h⟩
  have h0' := ENNReal.toReal_ne_zero.2 ⟨h'.measure_ne_zero (NeZero.ne _), hc'.measure_ne_top h'⟩
  rw [← measureReal_def] at h0 h0'
  have e1 := integral_integral hle hn hc hc' Measure.haar Measure.haar (φ := fun _ => 1) (fun _ _ _ => rfl)
    continuous_const x
  have e2 : Measure.haar.real (stdDom (Γ.subgroupOf N'))⁻¹ = Measure.haar.real (stdDom (Γ.subgroupOf N')) := by
    simp only [integral_const, measureReal_restrict_apply_univ, smul_smul] at e1
    have := smul_left_injective ℝ (one_ne_zero (α := ℂ)) e1
    rw [mul_comm] at this
    exact (mul_right_cancel₀ h0 this).symm
  rw [constTermOn_eq h hφ, constTermOn_eq' h fun γ hγ n => by
    simp only [Subgroup.coe_mul, mul_assoc]
    exact constTermOn_mul_left_of_normalizer hφ hγ
      (fun m => ⟨hn _ γ.2 m, fun hm => by simpa [mul_assoc] using hn _ (inv_mem γ.2) _ hm⟩) _]
  simp only [constTermOn_eq h' hφ]
  rw [integral_smul, integral_integral hle hn hc hc' _ _ hφ hφc, e2, inv_smul_smul₀ h0']

end GlobalTheory.Cusp.Stages

end
