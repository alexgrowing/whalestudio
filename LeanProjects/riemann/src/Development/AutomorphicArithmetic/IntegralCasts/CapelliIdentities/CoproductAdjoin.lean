import Mathlib

private theorem UpperTheory.Reformulated.B.CoproductAdjoin.reindex {G : Type} [Mul G] (A : Subalgebra ℂ (G → ℂ))
    (p : G → ℂ) {ι : Type} [Fintype ι] (a b : ι → G → ℂ) (h : ∀ i, a i ∈ A ∧ b i ∈ A)
    (hp : ∀ x k : G, p (x * k) = ∑ i, a i x * b i k) :
    ∃ (m : ℕ) (a : Fin m → G → ℂ) (b : Fin m → G → ℂ),
      (∀ i : Fin m, a i ∈ A ∧ b i ∈ A) ∧ ∀ x k : G, p (x * k) = ∑ i : Fin m, a i x * b i k := by
  refine ⟨Fintype.card ι, fun j => a ((Fintype.equivFin ι).symm j),
    fun j => b ((Fintype.equivFin ι).symm j), fun j => h _, fun x k => ?_⟩
  rw [hp]
  exact (Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => a i x * b i k)).symm

theorem UpperTheory.Reformulated.B.CoproductAdjoin.coprod_adjoin :
    ∀ {G : Type} [inst : Mul G] (S : Set (G → ℂ)),
    (∀ p ∈ S,
        ∃ (m : ℕ) (a : Fin m → G → ℂ) (b : Fin m → G → ℂ),
          (∀ (i : Fin m), a i ∈ Algebra.adjoin ℂ S ∧ b i ∈ Algebra.adjoin ℂ S) ∧
            ∀ (x k : G), p (x * k) = ∑ i : Fin m, a i x * b i k) →
      ∀ p ∈ Algebra.adjoin ℂ S,
        ∃ (m : ℕ) (a : Fin m → G → ℂ) (b : Fin m → G → ℂ),
          (∀ (i : Fin m), a i ∈ Algebra.adjoin ℂ S ∧ b i ∈ Algebra.adjoin ℂ S) ∧
            ∀ (x k : G), p (x * k) = ∑ i : Fin m, a i x * b i k := by
  intro G _ S hS p hp
  induction hp using Algebra.adjoin_induction with
  | mem p hp => exact hS p hp
  | algebraMap r =>
    refine ⟨1, fun _ => algebraMap ℂ (G → ℂ) r, fun _ => 1,
      fun _ => ⟨Subalgebra.algebraMap_mem _ r, one_mem _⟩, fun x k => ?_⟩
    simp
  | add p q _ _ ihp ihq =>
    obtain ⟨m, a, b, hab, hp⟩ := ihp
    obtain ⟨n, c, d, hcd, hq⟩ := ihq
    refine UpperTheory.Reformulated.B.CoproductAdjoin.reindex _ _ (Sum.elim a c) (Sum.elim b d) ?_ ?_
    · rintro (i | i)
      · exact hab i
      · exact hcd i
    · intro x k
      simp [Fintype.sum_sum_type, hp, hq]
  | mul p q _ _ ihp ihq =>
    obtain ⟨m, a, b, hab, hp⟩ := ihp
    obtain ⟨n, c, d, hcd, hq⟩ := ihq
    refine UpperTheory.Reformulated.B.CoproductAdjoin.reindex _ _ (ι := Fin m × Fin n)
      (fun z => a z.1 * c z.2) (fun z => b z.1 * d z.2) ?_ ?_
    · intro z
      exact ⟨mul_mem (hab _).1 (hcd _).1, mul_mem (hab _).2 (hcd _).2⟩
    · intro x k
      rw [Pi.mul_apply, hp, hq, Finset.sum_mul_sum, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.mul_apply]
      ring
