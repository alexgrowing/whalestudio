import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction

noncomputable section

open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

theorem applySmooth : ApplySmooth := by
  intro X _ _ V F _ _ _ _ q f v x hf hv
  let B : (V [⋀^Fin q]→L[ℝ] F) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin q => V) F :=
    ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ
  have hB : ContDiffAt ℝ ∞ (fun p : (V [⋀^Fin q]→L[ℝ] F) × (Fin q → V) => B p.1 p.2)
      (f x, fun i => v i x) :=
    (B.cpolynomialAt_uncurry_of_multilinear).contDiffAt
  have hin : ContDiffAt ℝ ∞ (fun y => (f y, fun i => v i y)) x :=
    hf.prodMk (contDiffAt_pi.mpr hv)
  exact hB.comp x hin

end UpperTheory.V.Lit.Dr
