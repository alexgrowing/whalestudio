import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SplitG

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

instance isModuleTopology_tensP : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩

instance borelSpace_tensP : BorelSpace (R ⊗[F] E) := ⟨rfl⟩

instance isTopologicalRing_tensP : IsTopologicalRing (R ⊗[F] E) :=
  IsModuleTopology.isTopologicalRing R (R ⊗[F] E)

theorem exists_homeomorph_tensP :
    ∃ (ι : Type) (_ : Fintype ι), Nonempty (R ⊗[F] E ≃ₜ (ι → R)) := by
  classical
  let b := Module.Free.chooseBasis R (R ⊗[F] E)
  let e : (R ⊗[F] E) ≃ₗ[R] (Module.Free.ChooseBasisIndex R (R ⊗[F] E) → R) := b.equivFun
  refine ⟨Module.Free.ChooseBasisIndex R (R ⊗[F] E), inferInstance, ⟨?_⟩⟩
  exact
    { toEquiv := e.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

instance secondCountable_tensP [SecondCountableTopology R] :
    SecondCountableTopology (R ⊗[F] E) := by
  obtain ⟨ι, _, ⟨h⟩⟩ := exists_homeomorph_tensP (F := F) (E := E) R
  exact h.isInducing.secondCountableTopology

end Top

instance secondCountable_completionP (F : Type) [Field F] [NumberField F] (v : InfinitePlace F) :
    SecondCountableTopology v.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding (v := v)).isEmbedding.isInducing.secondCountableTopology

instance secondCountable_AinfP (F : Type) [Field F] [NumberField F] : SecondCountableTopology (InfiniteAdeleRing F) :=
  inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))

theorem fd_of {D : D7} (X : HidaSetting D) : FiniteDimensional X.B.I.F X.B.I.E := inferInstance

theorem continuous_smul_tupI {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :
    Continuous (fun y : TupI X => g • y) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  refine continuous_pi fun a => ?_
  change Continuous fun y : TupI X =>
    ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) _).mulVec (y a)
  exact continuous_const.matrix_mulVec (continuous_apply a)

theorem continuous_orbM {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : Continuous (orbM X u') := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  refine continuous_pi fun a => ?_
  change Continuous fun h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J =>
    ((HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J h : GL (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E)).mulVec
        (ratTup (Ainf X.B.I.F) (tupH (frameOf X u')) a)
  exact (MassDataMassesW.SplitW.continuous_matHA X.B.I.cm.sig X.B.I.J (Ainf X.B.I.F)).matrix_mulVec
    continuous_const

theorem measurable_smul_tupI {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :
    Measurable (fun y : TupI X => g • y) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  exact (continuous_smul_tupI X g).measurable

theorem measurable_orbM {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : Measurable (orbM X u') := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  exact (continuous_orbM X u').measurable

theorem measurable_mul_leftHA {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :
    Measurable (fun h : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J => g * h) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  have : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  haveI : ContinuousMul (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    inferInstanceAs (ContinuousMul (HR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J))
  exact (continuous_const_mul g).measurable

theorem invPush_holds : InvPush := by
  intro D X u' ψ hT μinf νinf fibInf _ g
  have : X.measG.μGinf.IsHaarMeasure := X.measG_norm.2.1
  rw [Measure.map_map (measurable_smul_tupI X g) (measurable_orbM X u')]
  have e : (fun y : TupI X => g • y) ∘ orbM X u' = orbM X u' ∘ (fun h => g * h) := by
    funext h
    simp only [Function.comp, orbM, mul_smul]
  rw [e, ← Measure.map_map (measurable_orbM X u') (measurable_mul_leftHA X g),
    map_mul_left_eq_self]

end PI.AprimeInfW
