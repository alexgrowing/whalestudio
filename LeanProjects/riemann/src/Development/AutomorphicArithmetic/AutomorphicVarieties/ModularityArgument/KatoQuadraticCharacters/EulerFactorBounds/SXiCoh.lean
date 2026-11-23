import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KmapComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.RepSlD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.ValCast
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.OrbitSum

noncomputable section

open scoped MatrixGroups Matrix Classical
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4

namespace UpperTheory.V.Z.Kato.Nb

theorem sXiCoh : SXiCoh := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL hW x y hxy A _ π u u' h
  obtain ⟨a, ha, hu⟩ := h
  obtain ⟨hE, hadd, -⟩ := sApi Ω ε X l n
  refine ⟨fun t => Xi X l n N M₀ M w g x y (fun z => π z = t) a,
    fun t => sXiInv Ω ε X l n N M₀ M w g hL hW x y hxy _ a ha, fun s t => ?_⟩
  have h1 := (sXiMul Ω ε X l n N M₀ M w g hL x y hxy (fun z => π z = t)).1 (u s) (u' s) (tw X (l ^ n) M₀ s a) a (hu s)
  have h2 := sXiTw Ω ε X l n N M₀ M w g hL x y (fun z => π z = t) a s
  have h3 : (fun z => π (z * cycM M s) = t) = fun z => π z = t * (π (cycM M s))⁻¹ := by
    funext z
    rw [map_mul, eq_mul_inv_iff_mul_eq]
  rw [h3] at h2
  exact hE.trans h1 (hadd _ _ _ _ (hE.refl _) (hadd _ _ _ _ h2 (hE.refl _)).2).1

end UpperTheory.V.Z.Kato.Nb

end
