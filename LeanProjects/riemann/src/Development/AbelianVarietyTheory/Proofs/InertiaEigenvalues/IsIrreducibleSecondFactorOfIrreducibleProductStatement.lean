import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
open NumberField ReciprocityTheory.Gal Formalism.ConjugateSelfDual IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.DefiniteBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIrreducible_second_factor_of_irreducible_product : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (V W U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    (σ₀ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin t) k) W)
    (π : Representation ℂ (GL (Fin (r + t)) k) U),
    IsSmooth σ₀ → σ₀.IsIrreducible → IsSmooth τ → π.IsIrreducible → Nonempty (π.Equiv (prod₂ σ₀ τ)) →
      τ.IsIrreducible := by
  first | exact @GlobalTheory.SmGL.ProdIrr.isIrreducible_of_prod₂ | exact GlobalTheory.SmGL.ProdIrr.isIrreducible_of_prod₂ | (intros; apply GlobalTheory.SmGL.ProdIrr.isIrreducible_of_prod₂ <;> assumption)
