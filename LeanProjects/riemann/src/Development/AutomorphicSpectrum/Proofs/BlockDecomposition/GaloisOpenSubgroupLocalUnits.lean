import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

namespace GlobalTheory.CompanionTheory.InertOpen

section Local

variable {L : Type} [Field L] [NumberField L]

theorem continuous_finiteSingle (v : HeightOneSpectrum (𝓞 L)) : Continuous (Neutral.B1.finiteSingle L v) := by
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 L))) ≤ Filter.principal ({v}ᶜ : Set _) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion L → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) (Filter.principal ({v}ᶜ : Set _)) :=
    fun x => ⟨Function.update (fun _ => 1) v x, by
      rw [Filter.eventually_principal]
      intro w hw
      have h' : w ≠ v := hw
      rw [Function.update_of_ne h']
      exact one_mem _⟩
  have hf : Continuous f := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_const.update v continuous_id
  exact (RestrictedProduct.continuous_inclusion hle).comp hf

theorem continuous_localIdele' (v : HeightOneSpectrum (𝓞 L)) : Continuous (localIdele L v) := by
  apply Continuous.units_map
  exact Continuous.prodMk continuous_const (continuous_finiteSingle v)

theorem isOpen_valued_lt_one (w : HeightOneSpectrum (𝓞 L)) :
    IsOpen {x : w.adicCompletion L | Valued.v x < 1} := by
  have := Valued.isOpen_ball (w.adicCompletion L) 1
  simpa [Valuation.restrict_lt_one_iff] using this

theorem isCompact_setOf_isUnitAt (w : HeightOneSpectrum (𝓞 L)) :
    IsCompact {x : (w.adicCompletion L)ˣ | IsUnitAt w x} := by
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have e : ((↑) : (w.adicCompletion L)ˣ → w.adicCompletion L) '' {x | IsUnitAt w x} =
      (w.adicCompletionIntegers L : Set (w.adicCompletion L)) \ {x | Valued.v x < 1} := by
    ext y
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_diff, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, not_lt, IsUnitAt]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx.le, hx.ge⟩
    · rintro ⟨h1, h2⟩
      have hy : Valued.v y = 1 := le_antisymm h1 h2
      have h0 : y ≠ 0 := by
        rintro rfl
        simp at hy
      exact ⟨Units.mk0 y h0, hy, rfl⟩
  rw [e]
  exact (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers L w).diff (isOpen_valued_lt_one w)

end Local

section Gal

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem continuous_toAb' : Continuous (toAb E Ω) := continuous_quot_mk

theorem hausdorff_absolute_galois_abelianization : T2Space (Gab E Ω) := by
  haveI : Algebra.IsIntegral E Ω := (IsAlgClosure.isAlgebraic (R := E) (K := Ω)).isIntegral
  haveI : T2Space (G E Ω) := krullTopology_t2
  haveI : IsClosed (((commutator (G E Ω)).topologicalClosure : Subgroup (G E Ω)) : Set (G E Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  infer_instance

end Gal

end GlobalTheory.CompanionTheory.InertOpen

namespace GlobalTheory.CompanionTheory.InertOpen

theorem exists_openSubgroup_ine_art_units : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (U : Subgroup (w.adicCompletion E)ˣ), IsOpen (U : Set (w.adicCompletion E)ˣ) → (∀ x ∈ U, IsUnitAt w x) →
    ∃ V : Subgroup (G E Ω), IsOpen (V : Set (G E Ω)) ∧
      ∀ σ ∈ V, σ ∈ Ine (F := E) A → ∃ x ∈ U, art (localIdele E w x) = toAb E Ω σ := by
  intro E Ω _ _ _ _ _ l _ art hart w A hA U hUo _
  haveI := hausdorff_absolute_galois_abelianization (E := E) (Ω := Ω)
  let f : (w.adicCompletion E)ˣ →* Gab E Ω := art.comp (localIdele E w)
  have hf : Continuous f := hart.quot.continuous.comp (continuous_localIdele' w)
  let K : Set (w.adicCompletion E)ˣ := {y | ∃ u ∈ U, f u = f y}
  have hK : IsOpen K := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨u, hu, hux⟩
    refine ⟨{y | x⁻¹ * y ∈ U}, ?_, hUo.preimage (continuous_const.mul continuous_id), ?_⟩
    · intro y hy
      refine ⟨u * (x⁻¹ * y), U.mul_mem hu hy, ?_⟩
      rw [map_mul, hux, ← map_mul, mul_inv_cancel_left]
    · show x⁻¹ * x ∈ U
      rw [inv_mul_cancel]
      exact U.one_mem
  let C : Set (Gab E Ω) := f '' ({x | IsUnitAt w x} \ K)
  have hC : IsClosed C := (((isCompact_setOf_isUnitAt w).diff hK).image hf).isClosed
  have h1 : (1 : Gab E Ω) ∉ C := by
    rintro ⟨y, ⟨-, hyK⟩, hy⟩
    exact hyK ⟨1, U.one_mem, by rw [map_one, hy]⟩
  have hW : (toAb E Ω) ⁻¹' Cᶜ ∈ nhds (1 : G E Ω) :=
    (hC.isOpen_compl.preimage continuous_toAb').mem_nhds (by simpa using h1)
  obtain ⟨M, hM, hMs⟩ := (krullTopology_mem_nhds_one_iff E Ω _).1 hW
  refine ⟨M.fixingSubgroup, M.fixingSubgroup_isOpen, fun σ hσV hσI => ?_⟩
  obtain ⟨x, hxu, hx⟩ := (hart.ine w A hA (toAb E Ω σ)).2 ⟨σ, hσI, rfl⟩
  have hnot : toAb E Ω σ ∉ C := hMs hσV
  by_contra hne
  apply hnot
  refine ⟨x, ⟨hxu, ?_⟩, hx⟩
  rintro ⟨u, hu, hux⟩
  exact hne ⟨u, hu, hux.trans hx⟩

end GlobalTheory.CompanionTheory.InertOpen
