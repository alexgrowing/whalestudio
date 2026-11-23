import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Formalism.CyclotomicNorms.NonsquarefreeBounds.NonsquarefreeMonicBoundHolds

namespace GlobalTheory.RingHomOfIsIntegral

theorem exists_ringHom_of_isIntegral (R : Type) [CommRing R] [CharZero R] [Algebra.IsIntegral ℤ R]
    (l : ℕ) [hl : Fact (Nat.Prime l)] : Nonempty (R →+* AlgebraicClosure (ZMod l)) := by
  have hinj : Function.Injective (algebraMap ℤ R) := (algebraMap ℤ R).injective_int
  have hlp : (Ideal.span {(l : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hl.out)
  obtain ⟨P, -, hP, hPc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := R)
    (Ideal.span {(l : ℤ)}) ⊥ (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      rw [hinj (hx.trans (map_zero _).symm)]
      exact Ideal.zero_mem _)
  have := hP
  have hl0 : ((l : ℕ) : R ⧸ P) = 0 := by
    have h1 : (l : ℤ) ∈ P.comap (algebraMap ℤ R) := by
      rw [hPc]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap] at h1
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
    simpa using h1
  have hchar : CharP (R ⧸ P) l := (CharP.charP_iff_prime_eq_zero hl.out).mpr hl0
  let : Algebra (ZMod l) (R ⧸ P) := ZMod.algebra _ l
  have : Algebra.IsIntegral (ZMod l) (R ⧸ P) := ⟨fun x => by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ((Algebra.IsIntegral.isIntegral (R := ℤ) r).map (Ideal.Quotient.mkₐ ℤ P)).tower_top⟩
  exact ⟨(IsAlgClosed.lift (R := ZMod l) (S := R ⧸ P)
    (M := AlgebraicClosure (ZMod l))).toRingHom.comp (Ideal.Quotient.mk P)⟩

theorem nonempty_ringHom : ∀ (l : ℕ) [Fact (Nat.Prime l)],
    Nonempty (↥(integralClosure ℤ ℂ) →+* Formalism.CyclotomicNorms.Fbar l) := by
  intro l _
  exact exists_ringHom_of_isIntegral (integralClosure ℤ ℂ) l

end GlobalTheory.RingHomOfIsIntegral
