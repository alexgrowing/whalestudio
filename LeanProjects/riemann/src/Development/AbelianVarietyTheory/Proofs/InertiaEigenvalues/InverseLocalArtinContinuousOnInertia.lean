import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ArtinInvCont

theorem absoluteGaloisAbelianization_t2Space (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] :
    T2Space (GlobalTheory.HeckeGal.Gab E Ω) := by
  unfold GlobalTheory.HeckeGal.Gab TopologicalAbelianization
  haveI : IsClosed (((commutator (G E Ω)).topologicalClosure : Subgroup (G E Ω)) : Set (G E Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  infer_instance

theorem continuous_localIdele' (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    Continuous (Neutral.B1.localIdele E v) := by
  classical
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 E))) ≤ Filter.principal ({v}ᶜ : Set _) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion E → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E)
      (fun w => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) (Filter.principal ({v}ᶜ : Set _)) :=
    fun x => ⟨Pi.mulSingle v x, by
      rw [Filter.eventually_principal]
      intro w hw
      have h' : w ≠ v := hw
      rw [Pi.mulSingle_eq_of_ne h']
      exact one_mem _⟩
  have hf : Continuous f := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_mulSingle (A := fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E) v
  have hs : Continuous (Neutral.B1.finiteSingle E v) := (RestrictedProduct.continuous_inclusion hle).comp hf
  apply Continuous.units_map
  exact Continuous.prodMk continuous_const hs

theorem isCompact_valOne (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    IsCompact {x : (w.adicCompletion E)ˣ | Valued.v (x : w.adicCompletion E) = 1} := by
  rw [Units.isEmbedding_val₀.isInducing.isCompact_iff]
  have e : (Units.val '' {x : (w.adicCompletion E)ˣ | Valued.v (x : w.adicCompletion E) = 1}) =
      {y : w.adicCompletion E | Valued.v y = 1} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      have h0 : y ≠ 0 := by
        rintro rfl
        simp at hy
      exact ⟨Units.mk0 y h0, hy, rfl⟩
  rw [e]
  have hK : IsCompact (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers E w)
  refine hK.of_isClosed_subset ?_ ?_
  · have h1 : IsClosed {y : w.adicCompletion E | Valued.v y ≤ 1} := by
      have : {y : w.adicCompletion E | Valued.v y ≤ 1} = (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
        ext y
        exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).symm
      rw [this]
      exact hK.isClosed
    have h2 : IsOpen {y : w.adicCompletion E | Valued.v y < 1} := by
      rw [isOpen_iff_mem_nhds]
      intro y hy
      rw [Valued.mem_nhds]
      refine ⟨1, fun z hz => ?_⟩
      have hz' : Valued.v (z - y) < 1 := by simpa using hz
      have : z = (z - y) + y := by ring
      show Valued.v z < 1
      rw [this]
      exact Valuation.map_add_lt _ hz' hy
    have e2 : {y : w.adicCompletion E | Valued.v y = 1} =
        {y : w.adicCompletion E | Valued.v y ≤ 1} ∩ {y : w.adicCompletion E | Valued.v y < 1}ᶜ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_lt]
      exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩
    rw [e2]
    exact h1.inter h2.isClosed_compl
  · intro y hy
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).2 (le_of_eq hy)

theorem continuous_inv_on_ine : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω) (a : Weil h →* (w.adicCompletion E)ˣ), GlobalTheory.HeckeGal.IsGlobalArtin art → (∀ σ, ord (w.adicCompletion E) (a σ) = -deg σ) → (∀ σ : Weil h, art (Neutral.B1.localIdele E w (a σ)) = GlobalTheory.HeckeGal.toAb E Ω σ) → Continuous fun σ : Ine (F := E) A => a (ineIncl h σ) := by
  intro E Ω _ _ _ _ _ A w h art a ha hord hart
  haveI := absoluteGaloisAbelianization_t2Space E Ω
  let K : Set (w.adicCompletion E)ˣ := {x | Valued.v (x : w.adicCompletion E) = 1}
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_valOne E w)
  let f : K → GlobalTheory.HeckeGal.Gab E Ω := fun x => art (Neutral.B1.localIdele E w x.1)
  have hf : Continuous f :=
    (ha.quot.continuous.comp (continuous_localIdele' E w)).comp continuous_subtype_val
  have hinj : Function.Injective f := fun x y hxy =>
    Subtype.ext (GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art ha w hxy)
  have hemb := hf.isClosedEmbedding hinj
  have hmem : ∀ σ : Ine (F := E) A, a (ineIncl h σ) ∈ K := by
    intro σ
    have hd : deg (ineIncl h σ) = 0 := by
      rw [deg_eq (a := 0) (b := 0) (actsAs_zero_iff.mpr σ.2)]
      simp
    have ho := hord (ineIncl h σ)
    rw [hd, neg_zero, GlobalTheory.SmGL.SphCompletion.ord_completion, neg_eq_zero] at ho
    show Valued.v ((a (ineIncl h σ) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1
    rw [← WithZero.exp_log (by simp : Valued.v ((a (ineIncl h σ) : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≠ 0),
      ho, WithZero.exp_zero]
  let g : Ine (F := E) A → K := fun σ => ⟨a (ineIncl h σ), hmem σ⟩
  have hg : Continuous g := by
    rw [hemb.isInducing.continuous_iff]
    have e : f ∘ g = fun σ : Ine (F := E) A => GlobalTheory.HeckeGal.toAb E Ω (σ : G E Ω) :=
      funext fun σ => hart (ineIncl h σ)
    rw [e]
    exact continuous_quot_mk.comp continuous_subtype_val
  exact continuous_subtype_val.comp hg

end GlobalTheory.ArtinInvCont
