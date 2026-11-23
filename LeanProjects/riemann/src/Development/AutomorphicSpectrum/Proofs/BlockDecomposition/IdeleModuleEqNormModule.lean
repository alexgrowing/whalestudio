import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleConjugationInvariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleModuleBaseChangeSqStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

theorem ideleModule_eq_md_of_isNm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (x : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ), IsNm σ x n → (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x) : ℝ) = md n := by
  intro F E _ _ _ _ _ σ hcm x n h
  have h1 := GlobalTheory.T.idele_module_conjugation_invariant F E σ hcm x
  have h2 := GlobalTheory.T.idele_module_base_change_sq F E σ hcm n
  have hu : (ofF n : (AF F ⊗[F] E)ˣ) = Units.map (sigR (AF F) σ).toMonoidHom x * x := Units.ext h
  rw [hu, map_mul, map_mul] at h2
  have h3 : ((IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (Units.map (sigR (AF F) σ).toMonoidHom x)) : ℝ)) *
      (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x) : ℝ) = md n ^ 2 := h2
  rw [h1] at h3
  have hp : 0 < (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x) : ℝ) :=
    (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x)).2
  have hq : 0 < md n := (IdeleGroup.ideleModule F n).2
  nlinarith [sq_nonneg ((IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E x) : ℝ) - md n)]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
