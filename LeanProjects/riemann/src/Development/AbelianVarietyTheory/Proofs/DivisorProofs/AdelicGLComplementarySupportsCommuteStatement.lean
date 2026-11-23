import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicGLComplementarySupportsCommute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGL_complementary_supports_commute : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (h t : GA E a), h ∈ GlobalTheory.JSW.supS E a S → GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → h * t = t * h := by
  first | exact @GlobalTheory.JSW.MirSemi.supS_mul_comm | exact GlobalTheory.JSW.MirSemi.supS_mul_comm | (intros; apply GlobalTheory.JSW.MirSemi.supS_mul_comm <;> assumption)
