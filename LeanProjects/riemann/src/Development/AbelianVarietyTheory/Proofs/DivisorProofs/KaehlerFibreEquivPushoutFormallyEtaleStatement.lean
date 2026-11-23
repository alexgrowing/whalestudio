import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerFibreEquivPushoutFormallyEtale
open scoped TensorProduct Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kaehler_fibre_equiv_D_compat : ∀ (R R' B C B' K : Type) [CommRing R] [CommRing R'] [CommRing B] [CommRing C] [CommRing B'] [Field K] [Algebra R R'] [Algebra R B] [Algebra R C] [Algebra R' C] [Algebra B C] [IsScalarTower R R' C] [IsScalarTower R B C] [Algebra.IsPushout R R' B C] [Algebra C B'] [Algebra R' B'] [IsScalarTower R' C B'] [Algebra.FormallyEtale C B'] [Algebra B' K] [Algebra B K], (∀ x : B, algebraMap B K x = algebraMap B' K (algebraMap C B' (algebraMap B C x))) → ∃ e : (K ⊗[B] Ω[B⁄R]) ≃ₗ[K] (K ⊗[B'] Ω[B'⁄R']), ∀ x : B, e ((1 : K) ⊗ₜ[B] KaehlerDifferential.D R B x) = (1 : K) ⊗ₜ[B'] KaehlerDifferential.D R' B' (algebraMap C B' (algebraMap B C x)) := by
  first | exact @GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale | exact GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale | (intros; apply GlobalTheory.kaehler_fibre_equiv_pushout_formallyEtale <;> assumption)
