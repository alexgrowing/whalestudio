import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Formalism.DoubleCosetMeasures.LatticeCoset
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoAF
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint

noncomputable section

namespace GlobalTheory.HaarMat

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD Topology

variable {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))

theorem intMat_eq_pi (n m : ℕ) : intMat (OP P) n m = Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ
      fun _ : Fin m => ((P.adicCompletionIntegers L : Set (P.adicCompletion L)))) := by
  ext y
  exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩

theorem isCompact_intMat (n m : ℕ) : IsCompact (intMat (OP P) n m) := by
  rw [intMat_eq_pi]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers P

theorem isOpen_intMat (n m : ℕ) : IsOpen (intMat (OP P) n m) := by
  rw [intMat_eq_pi]
  exact isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _

def intMatK (n m : ℕ) : TopologicalSpace.PositiveCompacts (Matrix (Fin n) (Fin m) (P.adicCompletion L)) where
  carrier := intMat (OP P) n m
  isCompact' := isCompact_intMat P n m
  interior_nonempty' := by
    rw [(isOpen_intMat P n m).interior_eq]
    exact ⟨0, fun i j => (OP P).zero_mem⟩

theorem exists_haar_intMat : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (n m : ℕ),
    letI : MeasurableSpace (P.adicCompletion L) := borel _;
    ∃ ν : Measure (Matrix (Fin n) (Fin m) (P.adicCompletion L)),
      ν.IsAddLeftInvariant ∧ SFinite ν ∧ ν (intMat (OP P) n m) = 1 := by
  intro L _ _ P n m
  letI : MeasurableSpace (P.adicCompletion L) := borel _
  haveI : BorelSpace (P.adicCompletion L) := ⟨rfl⟩
  haveI : BorelSpace (Matrix (Fin n) (Fin m) (P.adicCompletion L)) :=
    inferInstanceAs (BorelSpace (Fin n → Fin m → P.adicCompletion L))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin m) (P.adicCompletion L)) :=
    (isCompact_intMat P n m).locallyCompactSpace_of_mem_nhds_of_addGroup
      ((isOpen_intMat P n m).mem_nhds fun i j => (OP P).zero_mem)
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin m) (P.adicCompletion L)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin m → P.adicCompletion L))
  haveI : SigmaCompactSpace (Matrix (Fin n) (Fin m) (P.adicCompletion L)) := inferInstance
  haveI : SigmaFinite (Measure.addHaarMeasure (intMatK P n m)) := inferInstance
  refine ⟨Measure.addHaarMeasure (intMatK P n m), inferInstance, inferInstance,
    Measure.addHaarMeasure_self⟩

end GlobalTheory.HaarMat
