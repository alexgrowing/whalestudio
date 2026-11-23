import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittVectorGhostEqFrobeniusIterateStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GhostComponentInjectiveOfNoTorsionStatement
open scoped NNReal

namespace GlobalTheory.DworkLift

theorem exists_frobenius_compatible_lift : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (φ : A →+* A),
    (∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) → (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) →
    ∀ (O : Type) [CommRing O] [CharP O l] (f : A →+* O), ∃ F : A →+* WittVector l O,
      (∀ a, (F a).coeff 0 = f a) ∧ ∀ a, F (φ a) = WittVector.frobenius (F a) := by
  intro l _ A _ φ hφ htor O _ _ f
  have hex := GlobalTheory.T.exists_wittVector_ghost_eq_frobenius_iterate l A φ hφ
  have inj := GlobalTheory.T.wittVector_eq_of_ghostComponent_eq_of_no_torsion l A htor
  let s : A → WittVector l A := fun a => Classical.choose (hex a)
  have hs : ∀ a n, WittVector.ghostComponent n (s a) = φ^[n] a := fun a => Classical.choose_spec (hex a)
  have hit : ∀ (n : ℕ) (a : A), φ^[n] a = (φ ^ n) a := fun n a => by rw [RingHom.coe_pow]
  let S : A →+* WittVector l A :=
    { toFun := s
      map_one' := inj _ _ fun n => by rw [hs, map_one, hit, map_one]
      map_mul' := fun a b => inj _ _ fun n => by rw [map_mul, hs, hs, hs, hit, hit, hit, map_mul]
      map_zero' := inj _ _ fun n => by rw [hs, map_zero, hit, map_zero]
      map_add' := fun a b => inj _ _ fun n => by rw [map_add, hs, hs, hs, hit, hit, hit, map_add] }
  have hS0 : ∀ a, (S a).coeff 0 = a := fun a => by
    change (s a).coeff 0 = a
    have h := hs a 0
    rw [WittVector.ghostComponent_apply, wittPolynomial_zero] at h
    simpa using h
  have hSφ : ∀ a, S (φ a) = WittVector.frobenius (S a) := fun a => inj _ _ fun n => by
    change WittVector.ghostComponent n (s (φ a)) = WittVector.ghostComponent n (WittVector.frobenius (s a))
    rw [WittVector.ghostComponent_frobenius, hs, hs, Function.iterate_succ_apply]
  refine ⟨(WittVector.map f).comp S, fun a => ?_, fun a => ?_⟩
  · simp only [RingHom.comp_apply, WittVector.map_coeff, hS0]
  · simp only [RingHom.comp_apply, hSφ]
    exact WittVector.IsPoly.map (WittVector.frobenius_isPoly l) f (S a)

end GlobalTheory.DworkLift
