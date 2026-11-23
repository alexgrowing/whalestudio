import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.AbsFactsAlt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr

open scoped TensorProduct

namespace UpperTheory.Gal.TP.Chr

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem fst_extZero (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :
    (GlobalTheory.UnitaryHeckeBaseChange.toAdele F E (extZero F E y)).1 = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have h : extZero F E (a ⊗ₜ[F] x) =
        (((0, a) : HeckeCharacterZeroLocus.ThmBIn.AF F) ⊗ₜ[F] x : HeckeCharacterZeroLocus.ThmBIn.AF F ⊗[F] E) :=
      GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul _ _ _ _
    rw [h]
    erw [GlobalTheory.UnitaryHeckeBaseChange.toAdele_tmul]
    show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E 0 * _ = 0
    rw [map_zero, zero_mul]
  | add y z hy hz => simp [map_add, hy, hz]

private theorem snd_extZero (y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :
    (GlobalTheory.UnitaryHeckeBaseChange.toAdele F E (extZero F E y)).2 = finAdEquiv F E y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have h : extZero F E (a ⊗ₜ[F] x) =
        (((0, a) : HeckeCharacterZeroLocus.ThmBIn.AF F) ⊗ₜ[F] x : HeckeCharacterZeroLocus.ThmBIn.AF F ⊗[F] E) :=
      GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul _ _ _ _
    rw [h]
    refine (congrArg (fun z : AdeleRing (𝓞 E) E => z.2)
      (GlobalTheory.UnitaryHeckeBaseChange.toAdele_tmul (F := F) (E := E) ((0, a) : HeckeCharacterZeroLocus.ThmBIn.AF F) x)).trans ?_
    show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E a * algebraMap E (FiniteAdeleRing (𝓞 E) E) x = _
    apply RestrictedProduct.ext
    intro w
    refine Eq.trans ?_ (finAdEquiv_tmul a x w).symm
    simp only [complMap_rfl, GlobalTheory.CharTransport.locMap_eq]
    rfl
  | add y z hy hz => simp [map_add, hy, hz]

private theorem toAdele_locIdele (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) :
    GlobalTheory.UnitaryHeckeBaseChange.toAdele F E (locIdele F w x : AF F ⊗[F] E) =
      (GlobalTheory.Mem.Chr.localIdele E w x : AdeleRing (𝓞 E) E) := by
  rw [coe_locIdele]
  simp only [map_add, map_sub, map_one]
  refine Prod.ext ?_ ?_
  · erw [Prod.fst_add, Prod.fst_sub, fst_extZero, fst_extZero]
    simp
    rfl
  · erw [Prod.snd_add, Prod.snd_sub, snd_extZero, snd_extZero]
    simp
    show (1 : FiniteAdeleRing (𝓞 E) E) - 1 + finiteSingle E w (x : w.adicCompletion E) = _
    rw [sub_self, zero_add]
    rfl

end

end UpperTheory.Gal.TP.Chr

theorem UpperTheory.Gal.TP.Chr.readLoc :
    UpperTheory.Gal.TP.Chr.ReadLoc := by
  intro E _ _ _ μ χ hR w
  ext y
  simp only [locChar, Formalism.L2.Host.HChar.loc, MonoidHom.comp_apply]
  show ((χ ((locIdele (↥(maximalRealSubfield E)) w) y) : Circle) : ℂ) = _
  rw [hR]
  congr 2
  exact Units.ext (toAdele_locIdele w y)
