import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
set_option linter.style.haveILetI false
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem meas_herm_top'_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsTopologicalAddGroup (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) ∧
    LocallyCompactSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) ∧ SecondCountableTopology (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) ∧
    BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) ∧ Countable (MeasP.ratHerm F E σ d.n) := by
  have hCM : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ := d.ok.good.cm
  obtain ⟨⟨hLC, hSC, hT2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hLC; haveI := hSC; haveI := hT2
  obtain ⟨hTR, hLC', hSC', hT2', -, -, -, -, hcl, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := hTR; haveI := hLC'; haveI := hSC'; haveI := hT2'
  haveI : LocallyCompactSpace (Matrix (Fin d.n) (Fin d.n) (AF F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin d.n → Fin d.n → AF F ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin d.n) (Fin d.n) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin d.n → Fin d.n → AF F ⊗[F] E))
  haveI : Countable E := meas_countableE
  haveI : Countable (Matrix (Fin d.n) (Fin d.n) E) := inferInstanceAs (Countable (Fin d.n → Fin d.n → E))
  refine ⟨inferInstance, (hcl d.n).locallyCompactSpace,
    inferInstanceAs (SecondCountableTopology ((HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n : Set (Matrix (Fin d.n) (Fin d.n) (AF F ⊗[F] E))))),
    ⟨rfl⟩, ?_⟩
  have hc : (Set.range (AddMonoidHom.mapMatrix (HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (E := E) (AF F)).toAddMonoidHom :
      Matrix (Fin d.n) (Fin d.n) E → Matrix (Fin d.n) (Fin d.n) (AF F ⊗[F] E))).Countable := Set.countable_range _
  haveI := hc.to_subtype
  refine Function.Injective.countable (f := fun x : MeasP.ratHerm F E σ d.n =>
    (⟨x.1.1, AddMonoidHom.mem_range.mp (AddSubgroup.mem_comap.mp x.2)⟩ : Set.range _)) ?_
  intro x y hxy
  have h := congrArg Subtype.val hxy
  exact Subtype.ext (Subtype.ext h)
theorem meas_mx_top'_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsTopologicalAddGroup (Mx F E d.m d.n) ∧ LocallyCompactSpace (Mx F E d.m d.n) ∧
    SecondCountableTopology (Mx F E d.m d.n) ∧ BorelSpace (Mx F E d.m d.n) ∧ Countable d.ratM := by
  have hCM : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ := d.ok.good.cm
  obtain ⟨⟨hLC, hSC, hT2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hLC; haveI := hSC; haveI := hT2
  obtain ⟨hTR, hLC', hSC', hT2', -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := hTR; haveI := hLC'; haveI := hSC'; haveI := hT2'
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : Countable E := meas_countableE
  haveI : Countable (Matrix (Fin d.m) (Fin d.n) E) := inferInstanceAs (Countable (Fin d.m → Fin d.n → E))
  refine ⟨inferInstance, inferInstanceAs (LocallyCompactSpace (Fin d.m → Fin d.n → AE F E)),
    inferInstanceAs (SecondCountableTopology (Fin d.m → Fin d.n → AE F E)),
    ⟨(inferInstance : BorelSpace (Fin d.m → Fin d.n → AE F E)).measurable_eq⟩, ?_⟩
  let K : AddSubgroup (Mx F E d.m d.n) :=
    (AddMonoidHom.mapMatrix (inclR (F := F) (E := E) (AF F)).toAddMonoidHom).range
  have hle : d.ratM ≤ K := by
    refine (AddSubgroup.closure_le K).mpr ?_
    rintro _ ⟨X, rfl⟩
    exact ⟨X, rfl⟩
  have hc : (Set.range (AddMonoidHom.mapMatrix (inclR (F := F) (E := E) (AF F)).toAddMonoidHom :
      Matrix (Fin d.m) (Fin d.n) E → Mx F E d.m d.n)).Countable := Set.countable_range _
  haveI := hc.to_subtype
  refine Function.Injective.countable (f := fun x : d.ratM =>
    (⟨x.1, AddMonoidHom.mem_range.mp (hle x.2)⟩ : Set.range _)) ?_
  intro x y hxy
  have h := congrArg Subtype.val hxy
  exact Subtype.ext h
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
