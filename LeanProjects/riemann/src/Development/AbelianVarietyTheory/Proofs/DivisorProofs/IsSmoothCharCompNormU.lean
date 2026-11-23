import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalCyclic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSmallStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormContinuous
import GroundTheory.GlobalFields.CompletionAtPlace

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Neutral.B1
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.FunExt

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCChar

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def normU (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal] :
    (u.adicCompletion L)ˣ →* (v.adicCompletion K)ˣ :=
  letI : Algebra (v.adicCompletion K) (u.adicCompletion L) := (GroundTheory.Global.adicCompletionMap v u).toAlgebra
  Units.map (Algebra.norm (v.adicCompletion K) : u.adicCompletion L →* v.adicCompletion K)

theorem isSmoothChar_comp_normU (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L))
    [u.asIdeal.LiesOver v.asIdeal] {χ : (v.adicCompletion K)ˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    IsSmoothChar (χ.comp (normU v u)) := by
  letI : Algebra (v.adicCompletion K) (u.adicCompletion L) := (GroundTheory.Global.adicCompletionMap v u).toAlgebra
  have : ContinuousSMul (v.adicCompletion K) (u.adicCompletion L) :=
    continuousSMul_of_algebraMap _ _ (GroundTheory.Global.continuous_adicCompletionMap v u)
  have : IsScalarTower K (v.adicCompletion K) (u.adicCompletion L) :=
    .of_algebraMap_eq fun x => by
      show _ = GroundTheory.Global.adicCompletionMap v u _
      rw [GroundTheory.Global.adicCompletionMap_algebraMap, IsScalarTower.algebraMap_apply K L (u.adicCompletion L)]
  have hfd : FiniteDimensional (v.adicCompletion K) (u.adicCompletion L) := GroundTheory.Global.finite_adicCompletion v u
  have hc := (GlobalTheory.adicCompletion_trace_norm_continuous K L v u _ (GroundTheory.Global.continuous_adicCompletionMap v u) hfd).2
  unfold IsSmoothChar at hχ ⊢
  rw [← MonoidHom.comap_ker]
  exact hχ.preimage (Continuous.units_map _ hc)

end GlobalTheory.BCChar

end
