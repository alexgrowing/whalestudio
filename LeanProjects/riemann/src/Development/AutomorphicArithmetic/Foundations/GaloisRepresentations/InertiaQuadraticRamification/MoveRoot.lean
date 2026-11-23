import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.UnrCharAtOf

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.moveRoot :
    MoveRoot := by
  intro Ω _ _ _ U hU ℓ hℓ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨E, hEfin, hEsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Ω _).1 (hU.mem_nhds U.one_mem)
  haveI := hEfin
  set b := Module.finrank ℚ E + 2 with hb
  have hn : 0 < ℓ ^ b := pow_pos hℓ.pos b
  haveI : NeZero ((ℓ ^ b : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  obtain ⟨ζ0, hζ0⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (ℓ ^ b) Ω)
    (Polynomial.degree_cyclotomic_pos _ Ω hn).ne'
  have hprim : IsPrimitiveRoot ζ0 (ℓ ^ b) := Polynomial.isRoot_cyclotomic_iff.1 hζ0
  have hnot : ζ0 ∉ E := by
    intro hmem
    have h0 := minpoly.natDegree_le (A := ℚ) (⟨ζ0, hmem⟩ : E)
    have h0' := IntermediateField.minpoly_eq (K := ℚ) (S := E) ⟨ζ0, hmem⟩
    have h1 : (minpoly ℚ ζ0).natDegree ≤ Module.finrank ℚ E := h0' ▸ h0
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hprim hn,
      Polynomial.natDegree_cyclotomic, Nat.totient_prime_pow hℓ (by omega)] at h1
    have h2 : b - 1 < ℓ ^ (b - 1) := Nat.lt_pow_self hℓ.one_lt
    have h3 : 1 ≤ ℓ - 1 := by have := hℓ.two_le; omega
    have h4 : ℓ ^ (b - 1) ≤ Module.finrank ℚ E :=
      (Nat.le_mul_of_pos_right _ h3).trans h1
    generalize ℓ ^ (b - 1) = N at h2 h4
    omega
  have hex : ∃ σ ∈ E.fixingSubgroup, σ ζ0 ≠ ζ0 := by
    by_contra hcon
    push_neg at hcon
    apply hnot
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    exact hcon
  obtain ⟨σ, hσE, hσ⟩ := hex
  refine ⟨b, σ, hEsub hσE, fun ζ hζ hfix => hσ ?_⟩
  haveI : NeZero (ℓ ^ b) := ⟨hn.ne'⟩
  obtain ⟨m, -, hm⟩ := hζ.eq_pow_of_pow_eq_one hprim.pow_eq_one
  rw [← hm, map_pow, hfix]
