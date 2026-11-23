import Mathlib

open MeasureTheory

namespace GlobalTheory.UnipotentFibration

variable {G : Type} [Group G]

def pairGroup (P N : Subgroup G) (hnorm : ∀ p ∈ P, ∀ n ∈ N, p * n * p⁻¹ ∈ N) :
    Subgroup (P × P) where
  carrier := {g | (g.1 : G) * (g.2 : G)⁻¹ ∈ N}
  one_mem' := by simp [N.one_mem]
  mul_mem' := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h1 h2
    have := N.mul_mem (hnorm a a.2 _ h2) h1
    simp only [Set.mem_setOf_eq, Prod.mk_mul_mk, Subgroup.coe_mul] at *
    convert this using 1
    group
  inv_mem' := by
    rintro ⟨a, b⟩ h
    have := hnorm _ (P.inv_mem a.2) _ (N.inv_mem h)
    simp only [Set.mem_setOf_eq, Prod.inv_mk, Subgroup.coe_inv] at *
    convert this using 1
    group

variable {P N : Subgroup G} {hnorm : ∀ p ∈ P, ∀ n ∈ N, p * n * p⁻¹ ∈ N}

lemma pair_mem (g : pairGroup P N hnorm) : (g.1.1 : G) * (g.1.2 : G)⁻¹ ∈ N := g.2

lemma pair_act_mem (g : pairGroup P N hnorm) (n : N) :
    (g.1.1 : G) * n.1 * (g.1.2 : G)⁻¹ ∈ N := by
  have := N.mul_mem (pair_mem g) (hnorm _ g.1.2.2 _ n.2)
  convert this using 1
  group

instance pairAction : MulAction (pairGroup P N hnorm) (N × G) where
  smul g z := (⟨(g.1.1 : G) * z.1.1 * (g.1.2 : G)⁻¹, pair_act_mem g z.1⟩, (g.1.2 : G) * z.2)
  one_smul z := by
    change ((⟨_, _⟩, _) : N × G) = z
    ext <;> simp
  mul_smul g h z := by
    change ((⟨_, _⟩, _) : N × G) = (⟨(g.1.1 : G) * ((h.1.1 : G) * z.1.1 * (h.1.2 : G)⁻¹) * (g.1.2 : G)⁻¹, _⟩, (g.1.2 : G) * ((h.1.2 : G) * z.2))
    ext <;> simp [mul_assoc]

lemma pair_smul_fst (g : pairGroup P N hnorm) (z : N × G) :
    ((g • z).1 : G) = (g.1.1 : G) * z.1.1 * (g.1.2 : G)⁻¹ := rfl

lemma pair_smul_snd (g : pairGroup P N hnorm) (z : N × G) :
    (g • z).2 = (g.1.2 : G) * z.2 := rfl

def pairSwap (g : pairGroup P N hnorm) : pairGroup P N hnorm :=
  ⟨(g.1.2, g.1.1), by
    have := N.inv_mem (pair_mem g)
    change (g.1.2 : G) * (g.1.1 : G)⁻¹ ∈ N
    convert this using 1
    group⟩

lemma pairSwap_involutive : Function.Involutive (pairSwap (hnorm := hnorm)) := fun _ => rfl

def flipMap (N : Subgroup G) (z : N × G) : N × G := (z.1⁻¹, z.1.1 * z.2)

lemma flipMap_involutive : Function.Involutive (flipMap N) := by
  intro z
  ext <;> simp [flipMap]

lemma flipMap_smul (g : pairGroup P N hnorm) (z : N × G) :
    flipMap N (g • z) = pairSwap g • flipMap N z := by
  ext
  · simp [flipMap, pair_smul_fst, pairSwap, mul_assoc]
  · simp [flipMap, pair_smul_fst, pair_smul_snd, pairSwap, mul_assoc]

theorem setIntegral_eq_zero_of_fibre : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (P N : Subgroup G) [Countable P],
    IsClosed (N : Set G) → ∀ (hnorm : ∀ p ∈ P, ∀ n ∈ N, p * n * p⁻¹ ∈ N) (ν : MeasureTheory.Measure N) [ν.IsHaarMeasure],
    (∀ (p : G) (hp : p ∈ P), MeasureTheory.Measure.map (fun n : N => (⟨p * n.1 * p⁻¹, hnorm p hp n.1 n.2⟩ : N)) ν = ν) →
    MeasureTheory.Measure.map (fun n : N => n⁻¹) ν = ν →
    ∀ (𝓕N : Set N), MeasureTheory.IsFundamentalDomain (P.subgroupOf N) 𝓕N ν → ν 𝓕N = 1 →
    ∀ (𝓕P : Set G), MeasureTheory.IsFundamentalDomain P 𝓕P μ →
    ∀ (Φ : G → ℂ), Continuous Φ → (∀ p ∈ P, ∀ x, Φ (p * x) = Φ x) → MeasureTheory.IntegrableOn Φ 𝓕P μ →
    (∀ x, ∫ n in 𝓕N, Φ (n.1 * x) ∂ν = 0) → ∫ x in 𝓕P, Φ x ∂μ = 0 := by
  intro G _ _ _ _ _ _ _ _ μ _ P N _ hN hnorm ν _ hconj hinv FN hFN hone FP hFP Φ hΦ hΦP hint h0
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set G)
  haveI : SigmaFinite ν := inferInstance
  have hc : ∀ (p : G) (hp : p ∈ P), MeasurePreserving
      (fun n : N => (⟨p * n.1 * p⁻¹, hnorm p hp n.1 n.2⟩ : N)) ν ν := fun p hp =>
    ⟨(Continuous.subtype_mk (by fun_prop) _).measurable, hconj p hp⟩
  have hmp : ∀ g : pairGroup P N hnorm,
      MeasurePreserving (fun z : N × G => g • z) (ν.prod μ) (ν.prod μ) := by
    intro g
    have h1 := ((measurePreserving_mul_left ν (⟨_, pair_mem g⟩ : N)).comp (hc _ g.1.2.2)).prod
      (measurePreserving_mul_left μ (g.1.2 : G))
    convert h1 using 1
    funext z
    ext
    · simp [pair_smul_fst, mul_assoc]
    · simp [pair_smul_snd]
  haveI : MeasurableConstSMul (pairGroup P N hnorm) (N × G) := ⟨fun g => (hmp g).measurable⟩
  haveI : SMulInvariantMeasure (pairGroup P N hnorm) (N × G) (ν.prod μ) :=
    ⟨fun g s hs => (hmp g).measure_preimage hs.nullMeasurableSet⟩
  have hD : IsFundamentalDomain (pairGroup P N hnorm) (FN ×ˢ FP) (ν.prod μ) := by
    refine IsFundamentalDomain.mk'' (hFN.nullMeasurableSet.prod hFP.nullMeasurableSet) ?_ ?_
      (fun g => (hmp g).quasiMeasurePreserving)
    · have h1 : ∀ᵐ n ∂ν, ∀ b : P, ∃ l : P.subgroupOf N,
          l • (⟨b.1 * n.1 * b.1⁻¹, hnorm b.1 b.2 n.1 n.2⟩ : N) ∈ FN := by
        rw [ae_all_iff]
        intro b
        exact (hc b.1 b.2).quasiMeasurePreserving.ae hFN.ae_covers
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1,
        Measure.quasiMeasurePreserving_snd.ae hFP.ae_covers] with z hz1 hz2
      obtain ⟨b, hb⟩ := hz2
      obtain ⟨l, hl⟩ := hz1 b
      refine ⟨⟨(⟨l.1.1, l.2⟩ * b, b), ?_⟩, ?_, hb⟩
      · change ((l.1.1 : G) * b.1) * b.1⁻¹ ∈ N
        simp
      · convert hl using 1
        ext
        rw [pair_smul_fst]
        change ((l.1.1 : G) * b.1) * z.1.1 * b.1⁻¹ = l.1.1 * (b.1 * z.1.1 * b.1⁻¹)
        group
    · rintro ⟨⟨a, b⟩, hab⟩ hg
      by_cases hb : b = 1
      · subst hb
        have ha : (a : G) ∈ N := by
          have : (a : G) * ((1 : P) : G)⁻¹ ∈ N := hab
          simpa using this
        let l : P.subgroupOf N := ⟨⟨a, ha⟩, a.2⟩
        have hl : l ≠ 1 := by
          intro h
          apply hg
          have : (a : G) = 1 := congrArg (fun x : P.subgroupOf N => (x.1 : G)) h
          ext <;> simp [this]
        have h2 := hFN.aedisjoint hl
        have h3 := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := μ)).preimage_null h2
        refine measure_mono_null ?_ h3
        rintro z ⟨⟨w, hw, rfl⟩, hz⟩
        refine ⟨⟨w.1, hw.1, ?_⟩, ⟨_, hz.1, one_smul _ _⟩⟩
        ext
        rw [pair_smul_fst]
        change (a : G) * w.1.1 = _
        simp
      · have h2 := hFP.aedisjoint hb
        have h3 := (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := μ)).preimage_null h2
        refine measure_mono_null ?_ h3
        rintro z ⟨⟨w, hw, rfl⟩, hz⟩
        exact ⟨⟨w.2, hw.2, rfl⟩, ⟨_, hz.2, one_smul _ _⟩⟩
  have hflip : MeasurePreserving (flipMap N) (ν.prod μ) (ν.prod μ) := by
    refine MeasurePreserving.skew_product (f := fun n : N => n⁻¹) (g := fun (n : N) (h : G) => n.1 * h)
      ⟨measurable_inv, hinv⟩ ?_ (Filter.Eventually.of_forall fun n => map_mul_left_eq_self μ _)
    exact (by fun_prop : Continuous (fun z : N × G => z.1.1 * z.2)).measurable
  let e : N × G ≃ᵐ N × G :=
    { toEquiv := flipMap_involutive.toPerm
      measurable_toFun := hflip.measurable
      measurable_invFun := hflip.measurable }
  have hemb : MeasurableEmbedding (flipMap N) := e.measurableEmbedding
  have hD' : IsFundamentalDomain (pairGroup P N hnorm) (flipMap N ⁻¹' (FN ×ˢ FP)) (ν.prod μ) :=
    hD.preimage_of_equiv hflip.quasiMeasurePreserving (e := pairSwap)
      pairSwap_involutive.bijective (fun g z => by
        have := flipMap_smul (pairSwap g) z
        rw [pairSwap_involutive] at this
        exact this)
  let Ψ : N × G → ℂ := fun z => Φ z.2
  let Θ : N × G → ℂ := fun z => Φ (z.1.1 * z.2)
  have hΨ : ∀ (g : pairGroup P N hnorm) z, Ψ (g • z) = Ψ z := fun g z => hΦP _ g.1.2.2 _
  have hΘ : Ψ ∘ flipMap N = Θ := rfl
  haveI : IsFiniteMeasure (ν.restrict FN) := ⟨by simp [hone]⟩
  have hi1 : IntegrableOn Ψ (FN ×ˢ FP) (ν.prod μ) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact Integrable.comp_snd hint _
  have hi2 : IntegrableOn Ψ (flipMap N ⁻¹' (FN ×ˢ FP)) (ν.prod μ) :=
    (hD.integrableOn_iff hD' hΨ).1 hi1
  have hpre : flipMap N ⁻¹' (flipMap N ⁻¹' (FN ×ˢ FP)) = FN ×ˢ FP :=
    flipMap_involutive.preimage _
  have hi3 : IntegrableOn Θ (FN ×ˢ FP) (ν.prod μ) := by
    rw [← hpre, ← hΘ]
    exact (hflip.integrableOn_comp_preimage hemb).2 hi2
  have e1 : ∫ z in FN ×ˢ FP, Ψ z ∂(ν.prod μ) = ∫ x in FP, Φ x ∂μ := by
    rw [← Measure.prod_restrict, integral_fun_snd]
    simp [Measure.real, hone]
  have e2 : ∫ z in FN ×ˢ FP, Θ z ∂(ν.prod μ) = 0 := by
    rw [IntegrableOn, ← Measure.prod_restrict] at hi3
    rw [← Measure.prod_restrict, integral_prod_symm _ hi3]
    simp [Θ, h0]
  rw [← e1, hD.setIntegral_eq hD' hΨ, ← hflip.setIntegral_preimage_emb hemb, hpre]
  exact e2

end GlobalTheory.UnipotentFibration
