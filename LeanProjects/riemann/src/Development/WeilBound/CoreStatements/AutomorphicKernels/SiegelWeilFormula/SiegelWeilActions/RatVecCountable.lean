import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.CtSplitOfParts
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.AddFDOfCover
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incV_add {k : ℕ} (x y : Fin k → E) :
    GlobalTheory.ThK.incV F (x + y) = GlobalTheory.ThK.incV F x + GlobalTheory.ThK.incV F y := by
  funext i
  simp [GlobalTheory.ThK.incV, map_add]

theorem incV_zero {k : ℕ} : GlobalTheory.ThK.incV F (0 : Fin k → E) = 0 := by
  funext i
  simp [GlobalTheory.ThK.incV]

theorem incV_neg {k : ℕ} (x : Fin k → E) : GlobalTheory.ThK.incV F (-x) = -GlobalTheory.ThK.incV F x := by
  funext i
  simp [GlobalTheory.ThK.incV, map_neg]

theorem mem_ratVec {k : ℕ} {v : Fin k → AE F E} :
    v ∈ AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin k → E) → _)) ↔ ∃ x, GlobalTheory.ThK.incV F x = v := by
  constructor
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, incV_zero⟩
    | add x y _ _ hx hy =>
      obtain ⟨X, rfl⟩ := hx
      obtain ⟨Z, rfl⟩ := hy
      exact ⟨X + Z, incV_add X Z⟩
    | neg x _ hx =>
      obtain ⟨X, rfl⟩ := hx
      exact ⟨-X, incV_neg X⟩
  · rintro ⟨X, rfl⟩
    exact AddSubgroup.subset_closure ⟨X, rfl⟩

theorem ratVec_cocompact (k : ℕ) : ∃ K : Set (Fin k → AE F E), IsCompact K ∧
    ∀ v, ∃ γ ∈ AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin k → E) → _)), γ + v ∈ K := by
  obtain ⟨C, hC, hCx⟩ := kfour.exists_compact_AE (F := F) (E := E)
  refine ⟨Set.univ.pi fun _ => C, isCompact_univ_pi fun _ => hC, fun v => ?_⟩
  choose X hX using fun i => hCx (v i)
  exact ⟨GlobalTheory.ThK.incV F X, mem_ratVec.2 ⟨X, rfl⟩, fun i _ => hX i⟩

theorem ratVec_discrete (k : ℕ) :
    DiscreteTopology (AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin k → E) → (Fin k → AE F E)))) := by
  obtain ⟨V, hV, hV0⟩ := kfour.exists_nhds_inclR (F := F) (E := E)
  have hW : (⋂ i, (fun v : Fin k → AE F E => v i) ⁻¹' V) ∈ 𝓝 (0 : Fin k → AE F E) := by
    refine Filter.iInter_mem.2 fun i => ?_
    exact (continuous_apply i).continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨O, hOW, hO, h0⟩ := mem_nhds_iff.1 hW
  refine discreteTopology_of_isOpen_singleton_zero ?_
  convert hO.preimage continuous_subtype_val using 1
  ext ⟨x, hx⟩
  constructor
  · intro h
    have h1 : x = 0 := congrArg Subtype.val (Set.mem_singleton_iff.1 h)
    subst h1
    exact h0
  · intro h
    obtain ⟨X, rfl⟩ := mem_ratVec.1 hx
    have h2 : X = 0 := by
      funext i
      exact hV0 _ (Set.mem_iInter.1 (hOW h) i)
    subst h2
    exact Set.mem_singleton_iff.2 (Subtype.ext incV_zero)

theorem ratVec_countable (k : ℕ) :
    Countable (AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin k → E) → (Fin k → AE F E)))) := by
  haveI := kfour.countable_E (E := E)
  have h : (AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin k → E) → (Fin k → AE F E))) :
      Set (Fin k → AE F E)).Countable := by
    refine (Set.countable_range (GlobalTheory.ThK.incV F : (Fin k → E) → (Fin k → AE F E))).mono fun v hv => ?_
    obtain ⟨X, rfl⟩ := mem_ratVec.1 hv
    exact ⟨X, rfl⟩
  exact h.to_subtype

end PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity

end
