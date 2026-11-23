import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

theorem UpperTheory.V.ML.isCrys_isDR_prod :
    ∀ (l F r : ℕ) (L : List ℕ), AdmL l F r L → admitted l F r L.prod ∧ L.prod ≠ 0 ∧ (∀ q, AdmL l F r (q :: L) → q.Coprime L.prod) ∧ ∀ q, AdmL l F r (q :: L) → AdmL l F r L := by
  intro l F r L hL
  induction L with
  | nil =>
    refine ⟨⟨squarefree_one, fun q hq hd => absurd (Nat.eq_one_of_dvd_one hd) hq.ne_one⟩, by simp, fun q _ => by simp, fun q _ => ⟨List.nodup_nil, by simp⟩⟩
  | cons a L ih =>
    have tail : ∀ (b : ℕ) (M : List ℕ), AdmL l F r (b :: M) → AdmL l F r M := fun b M h =>
      ⟨(List.nodup_cons.mp h.1).2, fun q hq => h.2 q (List.mem_cons_of_mem b hq)⟩
    obtain ⟨hA, hne, hcop, -⟩ := ih (tail a L hL)
    have haP : AdmP l F r a := hL.2 a List.mem_cons_self
    have ha : a.Prime := haP.1
    have haL : a.Coprime L.prod := hcop a hL
    rw [List.prod_cons]
    refine ⟨⟨?_, ?_⟩, mul_ne_zero ha.ne_zero hne, ?_, fun q hq => tail q _ hq⟩
    · exact Nat.squarefree_mul_iff.mpr ⟨haL, ha.prime.squarefree, hA.1⟩
    · intro q hq hd
      rcases (Nat.Prime.dvd_mul hq).mp hd with h | h
      · rw [(Nat.prime_dvd_prime_iff_eq hq ha).mp h]
        exact haP
      · exact hA.2 q hq h
    · intro q hq
      have hqa : q ≠ a := fun h => (List.nodup_cons.mp hq.1).1 (h ▸ List.mem_cons_self)
      have hqP : q.Prime := (hq.2 q List.mem_cons_self).1
      have hqL : AdmL l F r (q :: L) :=
        ⟨List.nodup_cons.mpr ⟨fun h => (List.nodup_cons.mp hq.1).1 (List.mem_cons_of_mem a h), (List.nodup_cons.mp (List.nodup_cons.mp hq.1).2).2⟩,
          fun p hp => by
            rcases List.mem_cons.mp hp with h | h
            · exact h ▸ hq.2 q List.mem_cons_self
            · exact hq.2 p (List.mem_cons_of_mem q (List.mem_cons_of_mem a h))⟩
      exact Nat.Coprime.mul_right ((Nat.coprime_primes hqP ha).mpr hqa) (hcop q hqL)
