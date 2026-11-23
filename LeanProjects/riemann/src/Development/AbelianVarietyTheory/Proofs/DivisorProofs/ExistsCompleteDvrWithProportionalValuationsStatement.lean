import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrWithProportionalValuations
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCdvrDominating
open IsLocalRing

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complete_dvr_with_proportional_valuations : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ ψ : R →+* V, IsLocalHom ψ → ∀ (I : Type) [Finite I] (a : I → R) (k : I → ℕ), (∀ i, Associated (ψ (a i)) (ϖ ^ k i)) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (ϖ' : W) (ψ' : R →+* W) (m m' : ℕ) (k' : I → ℕ), IsAdicComplete (maximalIdeal W) W ∧ Irreducible ϖ' ∧ Function.Injective ψ' ∧ IsLocalHom ψ' ∧ 1 ≤ m ∧ 1 ≤ m' ∧ ∀ i, Associated (ψ' (a i)) (ϖ' ^ k' i) ∧ m * k' i = m' * k i := by
  first | exact @GlobalTheory.PropDvr.exists_cdvr_proportional | exact GlobalTheory.PropDvr.exists_cdvr_proportional | (intros; apply GlobalTheory.PropDvr.exists_cdvr_proportional <;> assumption)
