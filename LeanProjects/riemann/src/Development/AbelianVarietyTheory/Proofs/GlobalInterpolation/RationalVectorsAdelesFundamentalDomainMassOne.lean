import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ.RatLattice

variable {F : Type} [Field F] [NumberField F]

theorem closure_range_rat (N : ℕ) :
    AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))) =
      AddSubgroup.pi Set.univ fun _ : Fin N => (algebraMap F (AF F)).range.toAddSubgroup := by
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨ξ, rfl⟩ l _
    exact ⟨ξ l, rfl⟩
  · intro u hu
    choose ξ hξ using fun l => hu l trivial
    have : u = rat ξ := funext fun l => (hξ l).symm
    rw [this]
    exact AddSubgroup.subset_closure ⟨ξ, rfl⟩

theorem mem_closure_iff (N : ℕ) (u : Fin N → AF F) :
    u ∈ AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))) ↔ ∃ ξ, u = rat ξ := by
  rw [closure_range_rat]
  constructor
  · intro hu
    choose ξ hξ using fun l => hu l trivial
    exact ⟨ξ, funext fun l => (hξ l).symm⟩
  · rintro ⟨ξ, rfl⟩ l _
    exact ⟨ξ l, rfl⟩

theorem rat_injective (N : ℕ) : Function.Injective (rat : (Fin N → F) → (Fin N → AF F)) := by
  haveI : Nontrivial (AF F) := by
    show Nontrivial (AdeleRing (𝓞 F) F)
    unfold AdeleRing
    infer_instance
  intro ξ η h
  funext l
  exact (algebraMap F (AF F)).injective (congrFun h l)

theorem isFD_pi {Y : Type} [AddCommGroup Y] [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν]
    {A : AddSubgroup Y} {D : Set Y} (hF : IsAddFundamentalDomain A D ν) (n : ℕ) :
    IsAddFundamentalDomain (AddSubgroup.pi Set.univ fun _ : Fin n => A) (Set.univ.pi fun _ : Fin n => D)
      (Measure.pi fun _ : Fin n => ν) := by
  have hq (i : Fin n) := Measure.quasiMeasurePreserving_eval (fun _ : Fin n => ν) i
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.univ_pi_eq_iInter]
    exact NullMeasurableSet.iInter fun i => hF.nullMeasurableSet.preimage (hq i)
  · have := (ae_all_iff (μ := (Measure.pi fun _ : Fin n => ν))).2 fun i => (hq i).ae hF.ae_covers
    filter_upwards [this] with z hz
    choose a ha using hz
    exact ⟨⟨fun i => a i, fun i _ => (a i).2⟩, fun i _ => ha i⟩
  · intro a b hab
    obtain ⟨i, hi⟩ : ∃ i, a.1 i ≠ b.1 i := by
      by_contra! h
      exact hab (Subtype.ext (funext h))
    have h := hF.aedisjoint (i := ⟨a.1 i, a.2 i trivial⟩) (j := ⟨b.1 i, b.2 i trivial⟩)
      fun e => hi (congrArg Subtype.val e)
    refine measure_mono_null ?_ ((hq i).preimage_null h)
    rintro z ⟨⟨u, hu, hu'⟩, ⟨v, hv, hv'⟩⟩
    exact ⟨⟨u i, hu i trivial, congrFun hu' i⟩, ⟨v i, hv i trivial, congrFun hv' i⟩⟩

end GlobalTheory.SWQ.RatLattice

open GlobalTheory.SWQ.RatLattice in
theorem GlobalTheory.SWQ.rat_lattice_fundamentalDomain : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ν : Measure (AF F)), IsCov1 ν → (muV N ν).IsAddHaarMeasure ∧ (∀ u : (Fin N → AF F), u ∈ (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) ↔ ∃ ξ, u = rat ξ) ∧ Function.Injective (rat : (Fin N → F) → (Fin N → AF F)) ∧ (∃ K : Set (Fin N → AF F), IsCompact K ∧ ∀ u, ∃ ξ, u - rat ξ ∈ K) ∧ ∃ D : Set (Fin N → AF F), MeasurableSet D ∧ IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) D (muV N ν) ∧ muV N ν D = 1 := by
  intro F _ _ N ν hν
  obtain ⟨hH, D₀, hD₀m, hD₀, hD₀1⟩ := hν
  haveI := hH
  refine ⟨?_, mem_closure_iff N, rat_injective N, ?_, ?_⟩
  · unfold muV
    infer_instance
  · obtain ⟨K, hK, hKc⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
    refine ⟨Set.univ.pi fun _ => K, isCompact_univ_pi fun _ => hK, fun u => ?_⟩
    choose ξ hξ using fun l => hKc (u l)
    exact ⟨ξ, fun l _ => hξ l⟩
  · refine ⟨Set.univ.pi fun _ => D₀, MeasurableSet.univ_pi fun _ => hD₀m, ?_, ?_⟩
    · rw [closure_range_rat]
      exact isFD_pi ν hD₀ N
    · unfold muV
      rw [Measure.pi_pi]
      simp [hD₀1]
