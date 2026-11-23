import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataProperties
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.Pass

theorem jumpsInV_of_isSubFam : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (ι : Type) (k : ℕ) (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (W : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsSubFam Ms W → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (U : Set ℤ), (∀ x, JumpsInV (P.PD K) (matRep (Ms x)) τ U) → JumpsInV (P.PD K) W.ρ τ U := by
  intro l _ P K LL ι k Ms W hW τ U hU
  obtain ⟨a, x, p, hp, hinj⟩ := hW
  refine GlobalTheory.SubSumJumps.jumpsInV_of_isSubOfSums (P.PD K) W.ρ Ms τ U ⟨a, x, LinearMap.pi p, ?_, ?_⟩ hU
  · rw [injective_iff_map_eq_zero]
    intro v hv
    exact hinj v fun j => congrFun hv j
  · intro g v
    funext j
    exact hp j g v

end GlobalTheory.Pass
