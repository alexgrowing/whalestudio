import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericSubquotientPrincipalSeries
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
open NumberField IsDedekindDomain
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_subquotient_principal_series : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (x x' : ℕ) (τ : GlobalTheory.CuspRep.CuspSub E (x + x'))
    (w : HeightOneSpectrum (𝓞 E)) (χ₁ χ₂ : (w.adicCompletion E)ˣ →* ℂˣ), GlobalTheory.Published.GenericityGL →
    GlobalTheory.SmGL.IsSmoothChar χ₁ → GlobalTheory.SmGL.IsSmoothChar χ₂ →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Q : Representation ℂ (GL (Fin (x + x')) (w.adicCompletion E)) V),
      GlobalTheory.SmGL.IsSubquotient Q (GlobalTheory.SmGL.prod₂ (GlobalTheory.SmGL.detRep (Fin x) χ₁) (GlobalTheory.SmGL.detRep (Fin x') χ₂)) →
      ∀ f : Q.IntertwiningMap (τ.locRep w), f ≠ 0 → x ≤ 1 ∧ x' ≤ 1 := by
  first | exact @GlobalTheory.CuspDetBlocks.le_one_of_intertwining | exact GlobalTheory.CuspDetBlocks.le_one_of_intertwining | (intros; apply GlobalTheory.CuspDetBlocks.le_one_of_intertwining <;> assumption)
