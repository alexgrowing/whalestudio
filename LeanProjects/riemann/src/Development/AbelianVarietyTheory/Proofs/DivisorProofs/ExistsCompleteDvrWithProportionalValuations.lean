import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCdvrDominating
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrOfDimOne
open IsLocalRing

namespace GlobalTheory.PropDvr

theorem exists_cdvr_proportional : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ ψ : R →+* V, IsLocalHom ψ → ∀ (I : Type) [Finite I] (a : I → R) (k : I → ℕ), (∀ i, Associated (ψ (a i)) (ϖ ^ k i)) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (ϖ' : W) (ψ' : R →+* W) (m m' : ℕ) (k' : I → ℕ), IsAdicComplete (maximalIdeal W) W ∧ Irreducible ϖ' ∧ Function.Injective ψ' ∧ IsLocalHom ψ' ∧ 1 ≤ m ∧ 1 ≤ m' ∧ ∀ i, Associated (ψ' (a i)) (ϖ' ^ k' i) ∧ m * k' i = m' * k i := by
  first
  | exact @_root_.GlobalTheory.CompleteDiscreteValuationRing.main
  | exact _root_.GlobalTheory.CompleteDiscreteValuationRing.main
  | (apply _root_.GlobalTheory.CompleteDiscreteValuationRing.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CompleteDiscreteValuationRing.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CompleteDiscreteValuationRing.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CompleteDiscreteValuationRing.main ..)

end GlobalTheory.PropDvr
