import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeActsByScalarCommutative
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_acts_by_scalar_commutative : ∀ (G : Type) [Group G] (K : Subgroup G), IsCommensurated K → (∀ f₁ ∈ Hecke ℂ K, ∀ f₂ ∈ Hecke ℂ K, conv K f₁ f₂ = conv K f₂ f₁) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), ρ.IsIrreducible → FiniteDimensional ℂ (fixed ρ K) → ∀ h ∈ Hecke ℂ K, ∃ c : ℂ, ∀ x ∈ fixed ρ K, heckeVec ρ K h x = c • x := by
  first | exact @GlobalTheory.LFun.HeckeScalar.heckeVec_scalar | exact GlobalTheory.LFun.HeckeScalar.heckeVec_scalar | (intros; apply GlobalTheory.LFun.HeckeScalar.heckeVec_scalar <;> assumption)
