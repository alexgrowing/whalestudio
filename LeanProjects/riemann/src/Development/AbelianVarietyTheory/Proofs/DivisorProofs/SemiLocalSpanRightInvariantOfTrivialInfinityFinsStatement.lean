import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiLocalSpanRightInvariantOfTrivialInfinityFins
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiLocalSpan_rightInvariant_of_trivial_infinity_finset : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (F₀ : GA E a → ℂ) (k : GA E a), GeneralLinearGroup.map (pInf E) k = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) k = 1) → (∀ g, F₀ (g * k) = F₀ g) → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S F₀, ∀ g, F (g * k) = F g := by
  first | exact @GlobalTheory.JSW.MirSemi.locSpan_rightInv | exact GlobalTheory.JSW.MirSemi.locSpan_rightInv | (intros; apply GlobalTheory.JSW.MirSemi.locSpan_rightInv <;> assumption)
