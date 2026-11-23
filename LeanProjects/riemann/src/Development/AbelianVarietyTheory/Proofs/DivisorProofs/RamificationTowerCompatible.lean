import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothCharCompNormU
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.BCChar

open scoped GroundTheory.Global.AdicLiesOver

theorem adicCompletionMap_comp_adicCompletionMap {K M L : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Field L] [NumberField L] [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 M))
    (w : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal]
    [w.asIdeal.LiesOver v.asIdeal] :
    (GroundTheory.Global.adicCompletionMap u w).comp (GroundTheory.Global.adicCompletionMap v u) =
      GroundTheory.Global.adicCompletionMap v w := by
  have h := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 K) (K := K) v).equalizer
    ((GroundTheory.Global.continuous_adicCompletionMap u w).comp
      (GroundTheory.Global.continuous_adicCompletionMap v u))
    (GroundTheory.Global.continuous_adicCompletionMap v w) (funext fun x ↦ ?_)
  · exact RingHom.ext (congrFun h)
  · simp only [Function.comp_apply]
    rw [GroundTheory.Global.adicCompletionMap_algebraMap, GroundTheory.Global.adicCompletionMap_algebraMap,
      GroundTheory.Global.adicCompletionMap_algebraMap, ← IsScalarTower.algebraMap_apply K M L]

theorem normU_comp_normU {K M L : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Field L] [NumberField L] [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 M))
    (w : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal]
    [w.asIdeal.LiesOver v.asIdeal] :
    (normU v u).comp (normU u w) = normU v w := by
  haveI : IsScalarTower (v.adicCompletion K) (u.adicCompletion M) (w.adicCompletion L) :=
    .of_algebraMap_eq' (adicCompletionMap_comp_adicCompletionMap v u w).symm
  refine MonoidHom.ext fun x => Units.ext ?_
  simp only [normU, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  exact Algebra.norm_norm (R := v.adicCompletion K) (S := u.adicCompletion M) (a := (x : w.adicCompletion L))

end GlobalTheory.BCChar

end
