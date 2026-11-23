import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPoissonSummationAnyHaar
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourierInversion
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelesHaarMeasureCovolumeOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NullOfFiniteCurve
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

open GlobalTheory.SWQ GlobalTheory.PoissonReindex in

theorem GlobalTheory.SWLit.tamagawa_eq_map_pi : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (N : ℕ) (e : κ ≃ Fin N) (ν : Measure (AF F)), GlobalTheory.SWQ.IsCov1 ν → ∀ μ : Measure (κ → AF F), IsTamagawa F κ μ → μ = Measure.map (GlobalTheory.PoissonReindex.reidx (F := F) e) (GlobalTheory.SWQ.muV N ν) := by
  intro F _ _ κ _ N e ν hν μ ⟨hμ, 𝓕, h𝓕1, h𝓕⟩
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨hHaar, hmem, -, -, D, hDm, hD, hD1⟩ := GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hν
  haveI := hHaar
  haveI := hμ
  let T : (Fin N → AF F) ≃ₜ+ (κ → AF F) := reidx e
  let Tm : (Fin N → AF F) ≃ᵐ (κ → AF F) := T.toHomeomorph.toMeasurableEquiv
  haveI hm : (Measure.map Tm (muV N ν)).IsAddHaarMeasure := T.isAddHaarMeasure_map (muV N ν)
  have hr := Measure.isAddLeftInvariant_eq_smul μ (Measure.map Tm (muV N ν))
  set r := μ.addHaarScalarFactor (Measure.map Tm (muV N ν))
  let L := (AddMonoidHom.compLeft (algebraMap F (AF F)).toAddMonoidHom κ).range
  let L' := AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))
  have hmap : ∀ g : L', T g.1 ∈ L := by
    intro g
    obtain ⟨ξ, hξ⟩ := (hmem g.1).1 g.2
    exact ⟨fun i => ξ (e i), by rw [hξ]; rfl⟩
  let φ : L' → L := fun g => ⟨T g.1, hmap g⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b h => Subtype.ext (T.injective (congrArg Subtype.val h)), ?_⟩
    rintro ⟨_, η, rfl⟩
    refine ⟨⟨rat fun j => η (e.symm j), (hmem _).2 ⟨_, rfl⟩⟩, Subtype.ext ?_⟩
    funext i
    show algebraMap F (AF F) (η (e.symm (e i))) = algebraMap F (AF F) (η i)
    rw [e.symm_apply_apply]
  have hmp : MeasurePreserving Tm.symm (Measure.map Tm (muV N ν)) (muV N ν) :=
    MeasurePreserving.symm Tm ⟨Tm.measurable, rfl⟩
  have hD' : IsAddFundamentalDomain L (Tm.symm ⁻¹' D) (Measure.map Tm (muV N ν)) := by
    refine hD.preimage_of_equiv hmp.quasiMeasurePreserving hφ fun g x => ?_
    show T.symm (T g.1 + x) = g.1 + T.symm x
    rw [map_add, T.symm_apply_apply]
  have hD'1 : Measure.map Tm (muV N ν) (Tm.symm ⁻¹' D) = 1 := by
    rw [hmp.measure_preimage hDm.nullMeasurableSet, hD1]
  have hac : μ ≪ Measure.map Tm (muV N ν) := by
    rw [hr]
    exact Measure.smul_absolutelyContinuous
  haveI : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm
  haveI : Countable L := by
    have : Countable (Set.range (AddMonoidHom.compLeft (algebraMap F (AF F)).toAddMonoidHom κ)) :=
      (Set.countable_range _).to_subtype
    exact this
  have h1 : μ (Tm.symm ⁻¹' D) = 1 := by
    rw [← h𝓕1]
    exact (hD'.mono hac).measure_eq h𝓕
  have hr1 : r = 1 := by
    rw [hr, Measure.smul_apply, hD'1] at h1
    simpa using h1
  rw [hr1, one_smul] at hr
  exact hr
