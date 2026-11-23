import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.GlobLevelSOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF

noncomputable section

namespace MassDataLevelSSteps.ProdW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.Volumes MeasureTheory NumberField
  IsDedekindDomain Topology PI.AdicCompletionValuation
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem isClosed_stabT (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [T2Space R]
    {a : ℕ} (X0 : Fin a → Fin n → E) :
    IsClosed ((stabT R σ J X0 : Subgroup (HA R σ J)) : Set (HA R σ J)) := by
  have hcont : Continuous fun g : HA R σ J => g • ratTup (F := F) R X0 := by
    show Continuous fun g : HA R σ J => actTup R (HA.mat R σ J g) (ratTup (F := F) R X0)
    unfold actTup HA.mat
    refine continuous_pi fun b => Continuous.matrix_mulVec ?_ continuous_const
    exact Units.continuous_val.comp
      (continuous_subtype_val : Continuous fun g : HR R σ J => (g : GL (Fin n) (R ⊗[F] E)))
  have : ((stabT R σ J X0 : Subgroup (HA R σ J)) : Set (HA R σ J)) =
      {g | g • ratTup (F := F) R X0 = ratTup (F := F) R X0} := by
    ext g
    exact MulAction.mem_stabilizer_iff
  rw [this]
  exact isClosed_eq hcont continuous_const

instance secondCountable_HAf : SecondCountableTopology (HA (Af F) σ J) :=
  PI.VolStabSW.TopoAF.secondCountable_HA_of (Af F) σ J

theorem prodNH_of {r : ℕ} (P : Frame E n r) (M : MeasW σ J P) (hM : M.IsTextNorm) :
    IsProdNH F E σ n J (Ssub (Af F) σ J P) (Nsub (Af F) σ J P) (Hsub (Af F) σ J P) M.μSf M.μNf M.μHf := by
  obtain ⟨-, -, hH, -, -, -, -, -, -, -, hS⟩ := hM
  have hcl : IsClosed ((Hsub (Af F) σ J P : Subgroup (HA (Af F) σ J)) : Set (HA (Af F) σ J)) :=
    isClosed_stabT σ J (Af F) (tupH P)
  have : LocallyCompactSpace (Hsub (Af F) σ J P) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have := hH
  have : SecondCountableTopology (HA (Af F) σ J) := secondCountable_HAf σ J
  have : SecondCountableTopology (Hsub (Af F) σ J P) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have : WeaklyLocallyCompactSpace (Hsub (Af F) σ J P) := inferInstance
  have : IsFiniteMeasureOnCompacts M.μHf := inferInstance
  have : IsLocallyFiniteMeasure M.μHf := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  have : SigmaFinite M.μHf := sigmaFinite_of_locallyFinite
  have : SFinite (amb M.μHf) := inferInstance
  have hmul : Measurable fun p : HA (Af F) σ J × HA (Af F) σ J => p.1 * p.2 := measurable_mul
  intro f hf
  have e1 : ∫⁻ k, f (k : HA (Af F) σ J) ∂M.μSf = ∫⁻ x, f x ∂(amb M.μSf) :=
    (lintegral_map hf measurable_subtype_coe).symm
  rw [e1, hS, lintegral_map hf hmul, lintegral_prod (fun p : HA (Af F) σ J × HA (Af F) σ J => f (p.1 * p.2)) (hf.comp hmul).aemeasurable]
  have hin : Measurable fun x : HA (Af F) σ J => ∫⁻ y, f (x * y) ∂(amb M.μHf) :=
    Measurable.lintegral_prod_right' (f := fun p : HA (Af F) σ J × HA (Af F) σ J => f (p.1 * p.2))
      (hf.comp hmul)
  rw [lintegral_map hin measurable_subtype_coe]
  refine lintegral_congr fun m => ?_
  exact lintegral_map (hf.comp (measurable_const_mul _)) measurable_subtype_coe

end MassDataLevelSSteps.ProdW

namespace MassDataLevelSSteps

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

theorem prodNH_holds : ProdNH := by
  intro D X w
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  exact ProdW.prodNH_of X.B.I.cm.sig X.B.I.J _ (X.measW w) (X.measW_norm w)

end MassDataLevelSSteps
