import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem GlobalTheory.exists_pow_char_eq_of_isReduced_finite : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] [IsReduced A], ∀ a : A, ∃ b : A, a = b ^ p := by
  intro p _ k _ _ _ A _ _ _ _ a
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  haveI : PerfectField k := PerfectRing.toPerfectField k p
  let e := IsArtinianRing.equivPi A
  have key : ∀ I : MaximalSpectrum A, ∃ c : A ⧸ I.asIdeal, e a I = c ^ p := by
    intro I
    haveI : I.asIdeal.IsMaximal := I.isMaximal
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : Module.Finite k (A ⧸ I.asIdeal) := Module.Finite.trans A (A ⧸ I.asIdeal)
    haveI : Algebra.IsAlgebraic k (A ⧸ I.asIdeal) := Algebra.IsAlgebraic.of_finite k _
    haveI : PerfectField (A ⧸ I.asIdeal) := Algebra.IsAlgebraic.perfectField k
    haveI : CharP (A ⧸ I.asIdeal) p :=
      charP_of_injective_algebraMap (algebraMap k (A ⧸ I.asIdeal)).injective p
    haveI : PerfectRing (A ⧸ I.asIdeal) p := PerfectField.toPerfectRing p
    obtain ⟨c, hc⟩ := surjective_frobenius (A ⧸ I.asIdeal) p (e a I)
    exact ⟨c, by rw [← hc, frobenius_def]⟩
  choose c hc using key
  refine ⟨e.symm c, e.injective ?_⟩
  rw [map_pow, AlgEquiv.apply_symm_apply]
  funext I
  rw [hc I, Pi.pow_apply]
