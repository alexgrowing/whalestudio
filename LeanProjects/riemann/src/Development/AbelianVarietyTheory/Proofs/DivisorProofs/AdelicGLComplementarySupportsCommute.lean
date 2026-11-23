import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.MirSemi

theorem supS_mul_comm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (h t : GA E a), h ∈ GlobalTheory.JSW.supS E a S →
    GeneralLinearGroup.map (pInf E) t = 1 →
    (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → h * t = t * h := by
  intro E _ _ _ a S h t hh ht htS
  refine ga_ext ?_ ?_
  · rw [map_mul, map_mul, ht, mul_one, one_mul]
  · ext i j w
    have key : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (h * t) =
        GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (t * h) := by
      rw [map_mul, map_mul]
      by_cases hw : w ∈ S
      · rw [htS w hw, mul_one, one_mul]
      · rw [hh w hw, mul_one, one_mul]
    have e : ((GeneralLinearGroup.map (pFin E) (h * t)).val i j) w =
        ((GeneralLinearGroup.map (pFin E) (t * h)).val i j) w :=
      congrArg (fun g : GL (Fin a) (w.adicCompletion E) => g.val i j) key
    rw [e]

end GlobalTheory.JSW.MirSemi
