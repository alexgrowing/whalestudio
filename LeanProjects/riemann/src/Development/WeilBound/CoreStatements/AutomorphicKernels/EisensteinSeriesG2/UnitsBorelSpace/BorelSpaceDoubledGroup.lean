import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2

noncomputable section

namespace GlobalTheory.EisBL.Borel

open Topology MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

theorem units_borelSpace (M : Type*) [Monoid M] [TopologicalSpace M] [T2Space M] [ContinuousMul M]
    [LocallyCompactSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] :
    BorelSpace Mˣ := by
  have hce := Units.isClosedEmbedding_embedProduct (α := M)
  haveI : LocallyCompactSpace Mˣ := hce.locallyCompactSpace
  haveI : SecondCountableTopology Mᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := M)).symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology Mˣ := hce.isEmbedding.secondCountableTopology
  refine ⟨le_antisymm ?_ ?_⟩
  · show MeasurableSpace.comap Units.val ‹MeasurableSpace M› ≤ borel Mˣ
    rw [BorelSpace.measurable_eq (α := M)]
    rw [← @borel_comap Mˣ M Units.val _]
    exact borel_anti (continuous_iff_le_induced.mp Units.continuous_val)
  · rw [borel_eq_generateFrom_isClosed]
    refine MeasurableSpace.generateFrom_le fun C hC => ?_
    have key : C = Units.val ⁻¹' (⋃ n, Units.val '' (C ∩ compactCovering Mˣ n)) := by
      ext u
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
      constructor
      · intro hu
        have hmem : u ∈ ⋃ n, compactCovering Mˣ n := by
          rw [iUnion_compactCovering]
          trivial
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hmem
        exact ⟨n, u, ⟨hu, hn⟩, rfl⟩
      · rintro ⟨n, v, ⟨hv, _⟩, hvu⟩
        rwa [← Units.ext hvu]
    rw [key]
    refine ⟨_, MeasurableSet.iUnion fun n => ?_, rfl⟩
    exact (((isCompact_compactCovering Mˣ n).inter_left hC).image Units.continuous_val).isClosed.measurableSet

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

instance borelAE : BorelSpace (AE F E) := ⟨rfl⟩

instance borelMatAE {ι : Type} [Fintype ι] : BorelSpace (Matrix ι ι (AE F E)) :=
  inferInstanceAs (BorelSpace (ι → ι → AE F E))

instance borelGL {ι : Type} [Fintype ι] [DecidableEq ι] : BorelSpace (GL ι (AE F E)) := by
  have : LocallyCompactSpace (Matrix ι ι (AE F E)) := inferInstanceAs (LocallyCompactSpace (ι → ι → AE F E))
  have : SecondCountableTopology (Matrix ι ι (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (ι → ι → AE F E))
  exact units_borelSpace _

instance borelSpace_doubled_group {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n} : BorelSpace (G2 σ Y) := Subtype.borelSpace _

end GlobalTheory.EisBL.Borel
