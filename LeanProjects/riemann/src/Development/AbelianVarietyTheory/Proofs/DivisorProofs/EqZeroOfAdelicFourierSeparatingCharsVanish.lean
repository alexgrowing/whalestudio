import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AveragedIntegralFunctional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFourierEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.AdelicFourierUniq

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem t2Space_infiniteAdeleRing_of_numberField : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))

theorem secondCountable_completion (v : InfinitePlace F) : SecondCountableTopology v.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology

theorem secondCountable_inf : SecondCountableTopology (InfiniteAdeleRing F) := by
  haveI := secondCountable_completion F
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))

theorem t2Space_adeleRing_of_numberField : T2Space (AF F) := by
  haveI := t2Space_infiniteAdeleRing_of_numberField F
  exact inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem secondCountable_AF : SecondCountableTopology (AF F) := by
  haveI := secondCountable_inf F
  exact inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem continuousAdd_AE : ContinuousAdd (AE F E) :=
  IsModuleTopology.toContinuousAdd (AF F) (AE F E)

def homAE : AE F E ≃ₜ (Fin (Module.finrank F E) → AF F) :=
  haveI := continuousAdd_AE F E
  let e := (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun
  { toEquiv := e.toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

theorem t2Space_cm_host_adeles : T2Space (AE F E) := by
  haveI := t2Space_adeleRing_of_numberField F
  exact (homAE F E).isEmbedding.t2Space

theorem secondCountable_AE : SecondCountableTopology (AE F E) := by
  haveI := secondCountable_AF F
  exact (homAE F E).isEmbedding.secondCountableTopology

theorem locallyCompact_AE : LocallyCompactSpace (AE F E) :=
  (homAE F E).isClosedEmbedding.locallyCompactSpace

theorem topAddGroup_AE : IsTopologicalAddGroup (AE F E) :=
  IsModuleTopology.topologicalAddGroup (R := AF F) (AE F E)

end GlobalTheory.AdelicFourierUniq

open GlobalTheory.AdelicFourierUniq in

theorem GlobalTheory.AdelicFourierUniq.eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ψ : AddChar (AF F) ℂ),
    IsStd ψ → ∀ (d : ℕ) (A : Type) [AddCommGroup A] (p : A → (Fin d → AE F E) →ₗ[AF F] AF F),
    (∀ a b, p (a + b) = p a + p b) → (∀ u, (∀ a, ψ (p a u) = 1) → u = 0) →
    ∀ μ : @Measure (Fin d → AE F E) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ N : (Fin d → AE F E) → ℂ, Continuous N → Integrable N μ → (∀ a, ∫ u, ψ (p a u) * N u ∂μ = 0) → N = 0 := by
  intro F E _ _ _ _ _ ψ hψ d A _ p hp hsep μ hμ N hN hi h
  letI : MeasurableSpace (Fin d → AE F E) := borel _
  haveI : BorelSpace (Fin d → AE F E) := ⟨rfl⟩
  haveI := t2Space_cm_host_adeles F E
  haveI := secondCountable_AE F E
  haveI := locallyCompact_AE F E
  haveI := topAddGroup_AE F E
  have hp0 : p 0 = 0 := by simpa using hp 0 0
  refine GlobalTheory.CharFourierInj.eq_zero (fun a u => ψ (p a u))
    (fun a => hψ.1.comp (IsModuleTopology.continuous_of_linearMap (R := AF F) (p a)))
    (fun a x y => by simp only [map_add, AddChar.map_add_eq_mul])
    (fun a b x => by simp only [hp, LinearMap.add_apply, AddChar.map_add_eq_mul])
    (fun x => by simp only [hp0, LinearMap.zero_apply, AddChar.map_zero_eq_one])
    (fun a x => GlobalTheory.StdCharFromIsStd.norm_psi hψ _) hsep μ N hN hi h
