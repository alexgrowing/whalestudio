import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryCharacterTrivialAtNonsplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeIffNonSplitPlaceIdempotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicPointUnitaryGroupGramOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCosetIndicatorReadingSphericalOffModulus

open NumberField IsDedekindDomain
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.NormSum.VacInt.PartFin

open GlobalTheory.NormSum.VacInt

section Cut

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem cutM_of_eq_zero (e : R) (he : e * e = e) (h : e = 0) (A : Matrix n n R) : cutM e he A = 1 := by
  subst h
  show (0 : R) • A + (1 - 0 : R) • (1 : Matrix n n R) = 1
  simp

theorem cutM_add (e e' f : R) (he : e * e = e) (he' : e' * e' = e') (hf : f * f = f) (h0 : e * e' = 0)
    (h : f = e + e') (A : Matrix n n R) : cutM f hf A = cutM e he A * cutM e' he' A := by
  subst h
  have h1 : e * (1 - e') = e := by linear_combination - h0
  have h2 : (1 - e) * e' = e' := by linear_combination - h0
  have h3 : (1 - e) * (1 - e') = 1 - (e + e') := by linear_combination h0
  show (e + e') • A + (1 - (e + e')) • (1 : Matrix n n R) =
    (e • A + (1 - e) • (1 : Matrix n n R)) * (e' • A + (1 - e') • (1 : Matrix n n R))
  simp only [add_mul, mul_add, smul_mul_smul_comm, Matrix.mul_one, Matrix.one_mul, h0, h1, h2, h3,
    zero_smul, zero_add, add_smul]
  abel

end Cut

variable {E : Type} [Field E] [NumberField E]

theorem eps_empty : eps E (fun p => p ∈ (∅ : Finset ℕ)) = 0 :=
  ext_prV fun v => by rw [prV_eps, map_zero]; simp

theorem eps_insert (q : ℕ) (s : Finset ℕ) (h : q ∉ s) :
    eps E (fun p => p ∈ insert q s) = eps E (fun p => p = q) + eps E (fun p => p ∈ s) :=
  ext_prV fun v => by
    rw [map_add, prV_eps, prV_eps, prV_eps]
    by_cases h1 : pr v = q
    · simp [h1, h]
    · by_cases h2 : pr v ∈ s <;> simp [h1, h2]

theorem eps_single_mul (q : ℕ) (s : Finset ℕ) (h : q ∉ s) :
    eps E (fun p => p = q) * eps E (fun p => p ∈ s) = 0 :=
  ext_prV fun v => by
    rw [map_mul, prV_eps, prV_eps, map_zero]
    by_cases h1 : pr v = q
    · simp [h1, h]
    · simp [h1]

theorem part_finset : ∀ {D : Formalism.BasicNotions.D7} {N : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D N), GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ (∅ : Finset ℕ)) y = 1 ∧ ∀ (q : ℕ) (s : Finset ℕ), q ∉ s → GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ insert q s) y = GlobalTheory.NormSum.VacInt.part D (fun p => p = q) y * GlobalTheory.NormSum.VacInt.part D (fun p => p ∈ s) y := by
  intro D N y
  exact ⟨Subtype.ext (Units.ext (cutM_of_eq_zero _ _ eps_empty _)), fun q s h =>
    Subtype.ext (Units.ext (cutM_add _ _ _ _ _ _ (eps_single_mul q s h) (eps_insert q s h) _))⟩

end GlobalTheory.NormSum.VacInt.PartFin
