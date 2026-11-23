import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLocalInductionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIdempotentComplementIffStatement
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.NewtonStep

variable {S : Type} [CommRing S]

theorem mul_eval_eq (Q : Polynomial S) {e z w : S} (h : e * (z - w) = 0) :
    e * Q.eval z = e * Q.eval w := by
  obtain ⟨c, hc⟩ := Polynomial.sub_dvd_eval_sub z w Q
  linear_combination e * hc + c * h

theorem mul_pow_eq (d : ℕ) {e z w : S} (h : e * (z - w) = 0) :
    e * z ^ d = e * w ^ d := by
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow z w d
  linear_combination e * hc + c * h

theorem step_of_forall_maximal (ϖ : S)
    (H : ∀ m : Ideal S, m.IsMaximal → Step (Ideal.Quotient.mk (compI m) ϖ)) : Step ϖ := by
  intro Q n hQ hd h0
  have key := GlobalTheory.T.idempotent_local_induction (S := S)
    (fun e => ∃ z, ϖ ^ (n + 1) ∣ e * Q.eval z ∧ ϖ ^ n ∣ e * z ^ Q.natDegree) ?_ ?_ ?_ ?_
  · obtain ⟨z, h1, h2⟩ := key
    exact ⟨z, by simpa using h1, by simpa using h2⟩
  · exact ⟨0, by simp, by simp⟩
  · rintro e e' _ _ ⟨z, h1, h2⟩
    refine ⟨z, ?_, ?_⟩
    · rw [mul_right_comm]; exact Dvd.dvd.mul_right h1 e'
    · rw [mul_right_comm]; exact Dvd.dvd.mul_right h2 e'
  · rintro e e' he he' hee ⟨z1, a1, b1⟩ ⟨z2, a2, b2⟩
    have he1 : e * e = e := he
    have he2 : e' * e' = e' := he'
    have hz1 : e * (e * z1 + e' * z2 - z1) = 0 := by
      linear_combination z1 * he1 + z2 * hee
    have hz2 : e' * (e * z1 + e' * z2 - z2) = 0 := by
      linear_combination z1 * hee + z2 * he2
    refine ⟨e * z1 + e' * z2, ?_, ?_⟩
    · rw [add_mul, mul_eval_eq Q hz1, mul_eval_eq Q hz2]
      exact dvd_add a1 a2
    · rw [add_mul, mul_pow_eq _ hz1, mul_pow_eq _ hz2]
      exact dvd_add b1 b2
  · intro m hm
    have hle : compI m ≤ m := Ideal.span_le.2 (fun e he => he.2)
    have hne : compI m ≠ ⊤ := fun h => hm.ne_top (top_le_iff.1 (h ▸ hle))
    have : Nontrivial (S ⧸ compI m) := Ideal.Quotient.nontrivial_iff.2 hne
    have hdeg : (Q.map (Ideal.Quotient.mk (compI m))).natDegree = Q.natDegree :=
      hQ.natDegree_map _
    have h0' : (Ideal.Quotient.mk (compI m) ϖ) ^ n ∣
        (Q.map (Ideal.Quotient.mk (compI m))).eval 0 := by
      rw [Polynomial.eval_zero_map, ← map_pow]
      exact map_dvd _ h0
    obtain ⟨z', h1, h2⟩ := H m hm (Q.map (Ideal.Quotient.mk (compI m))) n
      (hQ.map _) (hdeg ▸ hd) h0'
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z'
    obtain ⟨a', ha⟩ := h1
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
    obtain ⟨b', hb⟩ := h2
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
    rw [hdeg] at hb
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, ← map_pow, ← map_mul] at ha
    rw [← map_pow, ← map_pow, ← map_mul] at hb
    obtain ⟨e1, i1, n1, E1⟩ := (GlobalTheory.T.mem_idempotent_complement_iff m hm.isPrime _).1 (Ideal.Quotient.eq.1 ha)
    obtain ⟨e2, i2, n2, E2⟩ := (GlobalTheory.T.mem_idempotent_complement_iff m hm.isPrime _).1 (Ideal.Quotient.eq.1 hb)
    have i1' : e1 * e1 = e1 := i1
    have i2' : e2 * e2 = e2 := i2
    refine ⟨e1 * e2, ?_, ?_, z, ⟨e1 * e2 * a, ?_⟩, ⟨e1 * e2 * b, ?_⟩⟩
    · change e1 * e2 * (e1 * e2) = e1 * e2
      linear_combination (e2 * e2) * i1' + e1 * i2'
    · intro h
      exact (hm.isPrime.mem_or_mem h).elim n1 n2
    · linear_combination e2 * E1
    · linear_combination e1 * E2

end GlobalTheory.CompanionTheory.NewtonStep
