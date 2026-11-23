import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientEquivOfIrreducibleImage
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
open GlobalTheory.PRep GlobalTheory.SmGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subquotient_equiv_of_irreducible_image : ∀ (G : Type) [Group G] (V Y W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (R : Representation ℂ G Y) (σ : Representation ℂ G W), ρ.IsIrreducible → σ.IsIrreducible →
    (⨆ f : ρ.IntertwiningMap R, LinearMap.range f.toLinearMap = ⊤) → IsSubquotient σ R → Nonempty (σ.Equiv ρ) := by
  first | exact @GlobalTheory.CompanionTheory.IsoSub.equiv_of_isSubquotient | exact GlobalTheory.CompanionTheory.IsoSub.equiv_of_isSubquotient | (intros; apply GlobalTheory.CompanionTheory.IsoSub.equiv_of_isSubquotient <;> assumption)
