import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.MatchIndOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNorm

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Gam

theorem normLoc : NormLoc := by
  intro K L _ _ _ _ _ χ
  let ξ : HChar L := ⟨χ.1.comp (GroundTheory.Global.ideleNorm K L), χ.2.1.comp GroundTheory.Global.continuous_ideleNorm, fun k =>
    (congrArg χ.1 (GroundTheory.Global.ideleNorm_diagonal (K := K) k)).trans (χ.2.2 _)⟩
  refine ⟨ξ, ?_⟩
  rintro v ⟨w, hw⟩
  have hN : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ fdeg (⟨w, hw⟩ : PlacesOver L v) :=
    Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal v.asIdeal v.isPrime v.ne_bot
  obtain rfl : v = w.under (𝓞 K) := HeightOneSpectrum.ext hw.over
  refine ⟨MonoidHom.ext fun x => ?_, GlobalTheory.NormValGen.unrAt_val_of_comp_norm K L χ ξ (fun _ => rfl) w _ hN, hN⟩
  exact congrArg χ.1 (GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w x)

end UpperTheory.V.Z.Gam
