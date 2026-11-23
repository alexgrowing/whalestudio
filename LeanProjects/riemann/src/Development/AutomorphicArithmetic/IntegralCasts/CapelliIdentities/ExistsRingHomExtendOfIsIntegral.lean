import Mathlib

theorem UpperTheory.Reformulated.B.RingHomExtensionOfIntegral.exists_ringHom_extend_of_isIntegral.{u_1, u_2, u_3} :
    ∀ {R : Type u_1} {S : Type u_2} {K : Type u_3} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Field K]
      [IsAlgClosed K] [inst_4 : Algebra R S] [Algebra.IsIntegral R S],
      Function.Injective (⇑(Algebra.algebraMap R S) : R → S) →
        ∀ (f : R →+* K), ∃ (g : S →+* K), ∀ (r : R), (g : S → K) ((Algebra.algebraMap R S : R → S) r) = (f : R → K) r := by
  intro R S K _ _ _ _ _ _ hinj f
  have hP : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  have hle : Ideal.comap (algebraMap R S) (⊥ : Ideal S) ≤ RingHom.ker f := by
    intro a ha
    have h0 : algebraMap R S a = 0 := by simpa using ha
    have : a = 0 := hinj (by rw [map_zero]; exact h0)
    simp [this]
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker f) ⊥ hle
  have hlies : Q.LiesOver (RingHom.ker f) := (Ideal.liesOver_iff _ _).2 hQc.symm
  letI : Algebra (R ⧸ RingHom.ker f) K := (RingHom.kerLift f).toAlgebra
  have hK : Module.IsTorsionFree (R ⧸ RingHom.ker f) K :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.kerLift_injective f)
  have hS : Module.IsTorsionFree (R ⧸ RingHom.ker f) (S ⧸ Q) := by
    refine Module.isTorsionFree_iff_algebraMap_injective.2
      ((injective_iff_map_eq_zero _).2 fun x hx => ?_)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h2 : Ideal.Quotient.mk Q (algebraMap R S r) = 0 := hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at h2
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hQc]
    exact h2
  have hint : Algebra.IsIntegral (R ⧸ RingHom.ker f) (S ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q (RingHom.ker f)
  have halg : Algebra.IsAlgebraic (R ⧸ RingHom.ker f) (S ⧸ Q) :=
    Algebra.IsIntegral.isAlgebraic
  let φ : (S ⧸ Q) →ₐ[R ⧸ RingHom.ker f] K := IsAlgClosed.lift
  refine ⟨φ.toRingHom.comp (Ideal.Quotient.mk Q), fun r => ?_⟩
  have h1 : φ (algebraMap (R ⧸ RingHom.ker f) (S ⧸ Q) (Ideal.Quotient.mk _ r)) =
      algebraMap (R ⧸ RingHom.ker f) K (Ideal.Quotient.mk _ r) := φ.commutes _
  exact h1
