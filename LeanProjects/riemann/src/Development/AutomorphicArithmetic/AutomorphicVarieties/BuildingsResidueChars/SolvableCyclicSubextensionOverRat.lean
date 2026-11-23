import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.IntegralDomain

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.solvable_cyclic_subextension_over_rat :
    UpperTheory.V.Af.Sol.CycQ := by
  intro N
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (N + 3)
  obtain ⟨q, hq, -, hqp⟩ := Nat.exists_prime_gt_modEq_one 0 hp.ne_zero
  haveI := Fact.mk hq
  have hpdvd : p ∣ q - 1 := (Nat.modEq_iff_dvd' hq.one_le).mp hqp.symm
  haveI : IsAbelianGalois ℚ (CyclotomicField q ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {q} ℚ (CyclotomicField q ℚ)
  have hcardG : Nat.card Gal(CyclotomicField q ℚ/ℚ) = q - 1 := by
    rw [IsGalois.card_aut_eq_finrank, IsCyclotomicExtension.Rat.finrank q (CyclotomicField q ℚ),
      Nat.totient_prime hq]
  haveI : IsCyclic Gal(CyclotomicField q ℚ/ℚ) :=
    isCyclic_of_surjective (IsCyclotomicExtension.autEquivPow (CyclotomicField q ℚ)
      (Polynomial.cyclotomic.irreducible_rat hq.pos)).symm (MulEquiv.surjective _)
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Gal(CyclotomicField q ℚ/ℚ))
  have hH : Nat.card (Subgroup.zpowers (g ^ p)) = (q - 1) / p := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd hp.ne_zero (by rw [hg, hcardG]; exact hpdvd), hg, hcardG]
  have hfin : Module.finrank ℚ (IntermediateField.fixedField (Subgroup.zpowers (g ^ p))) = p := by
    have h1 := Module.finrank_mul_finrank ℚ (IntermediateField.fixedField (Subgroup.zpowers (g ^ p)))
      (CyclotomicField q ℚ)
    rw [IntermediateField.finrank_fixedField_eq_card, hH,
      IsCyclotomicExtension.Rat.finrank q (CyclotomicField q ℚ), Nat.totient_prime hq] at h1
    obtain ⟨m, hm⟩ := hpdvd
    have hq2 := hq.two_le
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; omega
      · exact h
    rw [hm, Nat.mul_div_cancel_left m hp.pos] at h1
    exact Nat.eq_of_mul_eq_mul_right hmpos h1
  haveI : IsAbelianGalois ℚ (IntermediateField.fixedField (Subgroup.zpowers (g ^ p))) :=
    IsAbelianGalois.tower_bot ℚ _ (CyclotomicField q ℚ)
  refine ⟨IntermediateField.fixedField (Subgroup.zpowers (g ^ p)), inferInstance, inferInstance,
    inferInstance, ?_, ?_, ?_⟩
  · classical
    rw [NumberField.isTotallyReal_iff]
    have hodd := InfinitePlace.nrRealPlaces_pos_of_odd_finrank
      (K := IntermediateField.fixedField (Subgroup.zpowers (g ^ p)))
      (by rw [hfin]; exact hp.odd_of_ne_two (by omega))
    obtain ⟨w0, hw0⟩ : ∃ w : InfinitePlace (IntermediateField.fixedField (Subgroup.zpowers (g ^ p))),
        w.IsReal := by
      by_contra hne
      push_neg at hne
      have : IsEmpty {w : InfinitePlace (IntermediateField.fixedField (Subgroup.zpowers (g ^ p))) //
          w.IsReal} := ⟨fun w => hne w.1 w.2⟩
      simp [InfinitePlace.nrRealPlaces] at hodd
    intro w
    obtain ⟨σ, hσ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq (k := ℚ) (w := w0) (w' := w)
      (Subsingleton.elim _ _)
    rw [← hσ]
    exact InfinitePlace.isReal_smul_iff.mpr hw0
  · rw [hfin]; exact hp
  · rw [hfin]; omega
