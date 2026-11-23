import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.AbsFactsAlt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr

set_option maxHeartbeats 400000 in
theorem UpperTheory.Gal.TP.Chr.readEx :
    UpperTheory.Gal.TP.Chr.ReadEx := by
  intro E _ _ _ μ hU
  let e := GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (GlobalTheory.GalOfCusp.isCMExt_real E)
  let f : (AE (↥(maximalRealSubfield E)) E)ˣ →* (AdeleRing (𝓞 E) E)ˣ := Units.map (e : _ →* _)
  refine ⟨{ toFun := fun z => ⟨((μ.1 (f z) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hU (f z))⟩,
            map_one' := ?_, map_mul' := ?_ }, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simp
  · intro x y
    apply Subtype.ext
    simp only [map_mul, Units.val_mul]
    rfl
  · intro z
    rfl
  · have hf : Continuous f := by
      show Continuous (Units.map (e : AE (↥(maximalRealSubfield E)) E →* AdeleRing (𝓞 E) E))
      exact Continuous.units_map _ (GlobalTheory.UnitaryHeckeBaseChange.continuous_toAdele _ E)
    have hμc : Continuous (μ.1 : Ideles E → ℂˣ) := μ.2.1
    refine continuous_induced_rng.2 ?_
    exact Units.continuous_val.comp (hμc.comp hf)
  · intro x
    apply Subtype.ext
    show ((μ.1 (f _) : ℂˣ) : ℂ) = 1
    rw [show f _ = diagUnits E x from Units.ext ?_, μ.2.2 x]
    · rfl
    · exact GlobalTheory.UnitaryHeckeBaseChange.toAdele_incA (x : E)
