import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHL

noncomputable section

namespace PI.VolStabSW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW

theorem measure_eq_relIndex_mul {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V]
    (μ : Measure V) [μ.IsAddLeftInvariant] (Λ L : AddSubgroup V) (hΛL : Λ ≤ L)
    (hL : MeasurableSet (L : Set V)) (hΛ : MeasurableSet (Λ : Set V)) (hfin : Λ.relIndex L ≠ 0) :
    μ L = (Λ.relIndex L : ENNReal) * μ Λ := by
  have emb : MeasurableEmbedding ((↑) : L → V) := MeasurableEmbedding.subtype_coe hL
  have hadd : ∀ g : L, Measurable (fun x : L => g + x) := fun g =>
    ((measurable_const_add (g : V)).comp measurable_subtype_coe).subtype_mk
  have : MeasurableAdd L := ⟨hadd, fun g =>
    ((measurable_add_const (g : V)).comp measurable_subtype_coe).subtype_mk⟩
  have : (Λ.addSubgroupOf L).FiniteIndex := ⟨hfin⟩
  have : (μ.comap ((↑) : L → V)).IsAddLeftInvariant := by
    refine ⟨fun g => ?_⟩
    ext s hs
    rw [Measure.map_apply (hadd g) hs, emb.comap_apply, emb.comap_apply]
    have e : ((↑) : L → V) '' ((fun x : L => g + x) ⁻¹' s) =
        (fun x : V => (g : V) + x) ⁻¹' (((↑) : L → V) '' s) := by
      ext x
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨g + y, hy, rfl⟩
      · rintro ⟨z, hz, hzx⟩
        have hxL : x ∈ L := by
          have : x = (z : V) - g := by rw [hzx]; abel
          rw [this]
          exact L.sub_mem z.2 g.2
        refine ⟨⟨x, hxL⟩, ?_, rfl⟩
        have : g + (⟨x, hxL⟩ : L) = z := Subtype.ext (by simp [hzx])
        rw [this]
        exact hz
    rw [e, measure_preimage_add]
  have key := AddSubgroup.index_mul_measure (Λ.addSubgroupOf L)
    (measurable_subtype_coe hΛ) (μ.comap ((↑) : L → V))
  rw [emb.comap_apply, emb.comap_apply, Set.image_univ, Subtype.range_coe] at key
  have e2 : ((↑) : L → V) '' ((Λ.addSubgroupOf L : AddSubgroup L) : Set L) = Λ := by
    ext x
    simp only [Set.mem_image, SetLike.mem_coe, AddSubgroup.mem_addSubgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hΛL hx⟩, hx, rfl⟩
  rw [e2] at key
  rw [← key]
  rfl

theorem smul_mem_hermO {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)
    {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F) {S : HermR (Fv F v) σ a}
    (hS : S ∈ hermO b v σ a) : s • S ∈ hermO b v σ a := by
  have hS' : ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr
      ((S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) k ∈ v.adicCompletionIntegers F := hS
  show ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr
      (((s • S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) k ∈
        v.adicCompletionIntegers F
  intro i j k
  rw [coe_hermSMul]
  simp only [Matrix.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem hs (hS' i j k)

def IdxL : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J), SWa1 F E σ M J → SWc1 F E σ M J →
    ∀ (a : ℕ), 1 ≤ a → a + 2 ≤ M → ∀ (X0 : Fin a → Fin M → E)
    (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)),
      (lamF b v a M 0).relIndex (latSub b v a M) = Nat.card (𝓞 F ⧸ v.asIdeal) ^ (2 * M * a)

def IdxH : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J), SWa1 F E σ M J → SWc1 F E σ M J →
    ∀ (a : ℕ), 1 ≤ a → a + 2 ≤ M → ∀ (X0 : Fin a → Fin M → E)
    (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v in cofinite,
      (hF b v σ a 0).relIndex (hermO b v σ a) = Nat.card (𝓞 F ⧸ v.asIdeal) ^ (a ^ 2)

theorem idxAA_of (hL : IdxL) (hH : IdxH) : IdxAA := by
  intro F E _ _ _ _ _ σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet d b
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  filter_upwards [hH F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet d b] with v hv
  intro μ ν hμ hν
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  obtain ⟨l1, -, -, l4, l5, -, -⟩ := latFacts_holds F E σ d b a M v
  have hq : Nat.card (𝓞 F ⧸ v.asIdeal) ≠ 0 := by
    have : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
    exact Nat.card_pos.ne'
  have hLi := hL F E σ hCM M J hJ hSa hSc a ha1 ha2 X0 hT hdet d b v
  refine ⟨?_, ?_⟩
  · have e := measure_eq_relIndex_mul μ (lamF b v a M 0) (latSub b v a M) l4
      (PositiveNearLattice.isClopen_latV b v a M).isOpen.measurableSet (l1 0).measurableSet
      (by rw [hLi]; exact pow_ne_zero _ hq)
    rw [hLi, Nat.cast_pow] at e
    exact e
  · have e := measure_eq_relIndex_mul ν (hF b v σ a 0) (hermO b v σ a)
      (by intro x hx
          simp only [hF, mem_smulSub] at hx
          obtain ⟨p, hp, rfl⟩ := hx
          exact smul_mem_hermO b v σ a (pow_mem (unifV_spec v).2.2 _) hp)
      (LatFactsW.isOpen_hermO b v σ a).measurableSet (l5 0).measurableSet
      (by rw [hv]; exact pow_ne_zero _ hq)
    rw [hv, Nat.cast_pow] at e
    exact e

end PI.VolStabSW
