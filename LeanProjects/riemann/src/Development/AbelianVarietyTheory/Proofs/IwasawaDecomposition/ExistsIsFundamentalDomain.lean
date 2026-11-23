import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
import Formalism.LocalRingCardinality.DataExtra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteCountableGQ
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FundDomDiscrete

open Topology Filter in

theorem exists_measurable_section {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] :
    ∃ F : Set G, MeasurableSet F ∧ ∀ x : G, ∃! γ : Γ, γ • x ∈ F := by
  classical
  obtain ⟨W, hWo, hW⟩ : ∃ W : Set G, IsOpen W ∧ ((↑) : Γ → G) ⁻¹' W = {1} :=
    isOpen_induced_iff.1 (isOpen_discrete ({1} : Set Γ))
  have h1W : (1 : G) ∈ W := by
    have : (1 : Γ) ∈ ((↑) : Γ → G) ⁻¹' W := by rw [hW]; rfl
    simpa using this
  obtain ⟨V0, hV0, hVW⟩ := exists_nhds_split_inv (hWo.mem_nhds h1W)
  obtain ⟨V, hVV0, hVo, h1V⟩ := mem_nhds_iff.1 hV0
  let U : G → Set G := fun g => {x | x * g⁻¹ ∈ V}
  have hUo : ∀ g, IsOpen (U g) := fun g => hVo.preimage (by fun_prop)
  have hUinj : ∀ g (γ : Γ) (x : G), x ∈ U g → (γ : G) * x ∈ U g → γ = 1 := by
    intro g γ x hx hγ
    have h := hVW _ (hVV0 hγ) _ (hVV0 hx)
    have h2 : (γ : G) * x * g⁻¹ / (x * g⁻¹) = γ := by
      rw [div_eq_mul_inv]; group
    rw [h2] at h
    have : γ ∈ ((↑) : Γ → G) ⁻¹' W := h
    rw [hW] at this
    exact this
  obtain ⟨s, hsc, hs⟩ := TopologicalSpace.countable_cover_nhds (f := U)
    (fun g => (hUo g).mem_nhds (by simpa [U] using h1V))
  have hsne : s.Nonempty := by
    have : (1 : G) ∈ ⋃ x ∈ s, U x := by rw [hs]; trivial
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, -⟩ := this
    exact ⟨i, hi⟩
  obtain ⟨e, rfl⟩ := hsc.exists_eq_range hsne
  have hcov : ∀ x : G, ∃ n, x ∈ U (e n) := by
    intro x
    have : x ∈ ⋃ y ∈ Set.range e, U y := by rw [hs]; trivial
    simp only [Set.mem_iUnion] at this
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ := this
    exact ⟨n, hn⟩
  let S : ℕ → Set G := fun n => ⋃ γ : Γ, {x | (γ : G) * x ∈ U (e n)}
  have hSo : ∀ n, IsOpen (S n) := fun n =>
    isOpen_iUnion fun γ => (hUo _).preimage (continuous_const.mul continuous_id)
  have hSmem : ∀ n x, x ∈ S n ↔ ∃ γ : Γ, (γ : G) * x ∈ U (e n) := by
    intro n x; simp [S]
  have hSinv : ∀ n (δ : Γ) x, (δ : G) * x ∈ S n ↔ x ∈ S n := by
    intro n δ x
    rw [hSmem, hSmem]
    constructor
    · rintro ⟨γ, h⟩
      exact ⟨γ * δ, by simpa [mul_assoc] using h⟩
    · rintro ⟨γ, h⟩
      exact ⟨γ * δ⁻¹, by simpa [mul_assoc] using h⟩
  refine ⟨⋃ n, (U (e n) ∩ ⋂ k, ⋂ _ : k < n, (S k)ᶜ), ?_, ?_⟩
  · exact MeasurableSet.iUnion fun n => (hUo _).measurableSet.inter
      (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => (hSo k).measurableSet.compl)
  · intro x
    have hex : ∃ n, x ∈ S n := by
      obtain ⟨n, hn⟩ := hcov x
      exact ⟨n, (hSmem n x).2 ⟨1, by simpa using hn⟩⟩
    have key : ∀ γ : Γ, γ • x ∈ (⋃ n, (U (e n) ∩ ⋂ k, ⋂ _ : k < n, (S k)ᶜ)) ↔
        (γ : G) * x ∈ U (e (Nat.find hex)) := by
      intro γ
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff,
        Subgroup.smul_def, smul_eq_mul, hSinv]
      constructor
      · rintro ⟨n, hn, hk⟩
        have : Nat.find hex = n := by
          rw [Nat.find_eq_iff]
          exact ⟨(hSmem n x).2 ⟨γ, hn⟩, hk⟩
        rw [this]; exact hn
      · intro h
        exact ⟨_, h, fun k hk => Nat.find_min hex hk⟩
    obtain ⟨γ, hγ⟩ := (hSmem _ x).1 (Nat.find_spec hex)
    refine ⟨γ, (key γ).2 hγ, fun δ hδ => ?_⟩
    have hδ' := (key δ).1 hδ
    have := hUinj _ (δ * γ⁻¹) _ hγ (by simpa [mul_assoc] using hδ')
    exact mul_inv_eq_one.1 this

theorem exists_isFundamentalDomain {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) :
    ∃ F : Set G, IsFundamentalDomain Γ F μ := by
  obtain ⟨F, hF, h⟩ := exists_measurable_section Γ
  exact ⟨F, IsFundamentalDomain.mk' hF.nullMeasurableSet h⟩

theorem exists_fundDom : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)), μ.IsHaarMeasure →
    ∃ 𝓕 : Set (GA D V), IsFundamentalDomain (GQ V) 𝓕 μ := by
  intro D V μ _
  have := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).2.1
  have := (GlobalTheory.RationalCountable.discrete_countable_GQ D V).1
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  exact exists_isFundamentalDomain (GQ V) μ

end GlobalTheory.FundDomDiscrete
