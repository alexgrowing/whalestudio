import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

noncomputable section

namespace GlobalTheory.JacVal

theorem mem_iff_dvd_of_height_one : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → ∀ (Q : Ideal B), Q.IsPrime → Q.height = 1 → ∀ (t : A), Irreducible t → (∀ b : B, (b : K) = algebraMap F K t → b ∈ Q) → ∀ (a : A) (b : B), (b : K) = algebraMap F K a → (b ∈ Q ↔ t ∣ a) := by
  intro k F K _ _ _ _ _ _ _ d u hu A _ hA B hB Q hQ hQ1 t ht htQ
  have hmem : ∀ x : K, x ∈ B ↔ x ∈ integralClosure A K := by
    intro x; rw [hB]; rfl
  let φ : A →+* B := (algebraMap A K).codRestrict B
    (fun a => (hmem _).2 (Subalgebra.algebraMap_mem _ a))
  letI : Algebra A B := φ.toAlgebra
  have hφ : ∀ a : A, ((algebraMap A B a : B) : K) = algebraMap F K (a : F) := fun a => rfl
  have hinjK : Function.Injective (algebraMap A K) := by
    intro x y h
    exact Subtype.val_injective ((algebraMap F K).injective h)
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr (by
    intro x y h
    apply hinjK
    have := congrArg (fun z : B => (z : K)) h
    exact this)
  let f : B →ₐ[A] K := { (B.val : B →ₐ[k] K).toRingHom with commutes' := fun a => rfl }
  haveI : Algebra.IsIntegral A B := ⟨fun b => by
    have hb : IsIntegral A (b : K) := (hmem _).1 b.2
    exact (isIntegral_algHom_iff f Subtype.val_injective).1 hb⟩
  let e : MvPolynomial (Fin d) k ≃ₐ[k] A :=
    hu.aevalEquiv.trans (Subalgebra.equivOfEq _ _ hA.symm)
  haveI : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv e.toRingEquiv
  have htp : Prime t := by
    have h1 : Irreducible (e.symm t) := (MulEquiv.irreducible_iff e.symm.toMulEquiv).2 ht
    have h2 : Prime (e.symm t) := h1.prime
    exact (MulEquiv.prime_iff e.symm.toMulEquiv).1 h2
  have ht0 : t ≠ 0 := htp.ne_zero
  haveI hsp : (Ideal.span {t} : Ideal A).IsPrime := (Ideal.span_singleton_prime ht0).2 htp
  set P : Ideal A := Q.comap (algebraMap A B) with hP
  haveI : P.IsPrime := Ideal.comap_isPrime _ Q
  haveI : Q.LiesOver P := ⟨rfl⟩
  have htP : t ∈ P := htQ _ (hφ t)
  have hle : Ideal.span {t} ≤ P := (Ideal.span_singleton_le_iff_mem _).2 htP
  have hPeq : P = Ideal.span {t} := by
    by_contra hne
    have hlt : Ideal.span {t} < P := lt_of_le_of_ne hle (Ne.symm hne)
    obtain ⟨Q', hQ'Q, hQ', hQ'o⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := Ideal.span {t}) (q := P) Q hlt
    haveI := hQ'
    have hQ'0 : Q' ≠ ⊥ := by
      rintro rfl
      have h := hQ'o.over
      have : t ∈ (⊥ : Ideal B).under A := h ▸ Ideal.mem_span_singleton_self t
      rw [Ideal.under, Ideal.mem_comap, Ideal.mem_bot] at this
      exact ht0 ((FaithfulSMul.algebraMap_injective A B) (by rw [this, map_zero]))
    haveI : (⊥ : Ideal B).IsPrime := Ideal.bot_prime
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hQ'0)
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hQ'Q
    have h4 : (1 : ℕ∞) ≤ Q'.height := le_trans le_add_self h1
    have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) (h2.trans hQ1.le)
    exact absurd h3 (by decide)
  intro a b hab
  have hb : b = algebraMap A B a := Subtype.ext (hab.trans (hφ a).symm)
  subst hb
  have : algebraMap A B a ∈ Q ↔ a ∈ P := Iff.rfl
  rw [this, hPeq, Ideal.mem_span_singleton]

end GlobalTheory.JacVal
