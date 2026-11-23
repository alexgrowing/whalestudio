import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChowNorm
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

namespace GenChowIrreducible

variable {n e : ℕ}

theorem map_specRest {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S)
    (ψ : S →+* T) (f : MvPolynomial (Fin (e + 1) × Fin n) R) (y : Par e n → S) :
    (specRest φ f y).map ψ = specRest (ψ.comp φ) f (ψ ∘ y) := by
  unfold specRest
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [eval₂_add, hp, hq]
  | mul_X p ij hp =>
    obtain ⟨i, j⟩ := ij
    induction i using Fin.cases <;> simp [eval₂_mul, hp]

theorem constantCoeff_specRest {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {δ : ℕ}
    (hδ : 1 ≤ δ) {f : MvPolynomial (Fin (e + 1) × Fin n) R} (hf : IsMultiHomog δ f)
    (y : Par e n → S) : constantCoeff (specRest φ f y) = 0 := by
  unfold specRest
  rw [← coe_eval₂Hom, ← RingHom.comp_apply, MvPolynomial.comp_eval₂Hom]
  rw [coe_eval₂Hom, eval₂_eq']
  refine Finset.sum_eq_zero fun d hd => ?_
  obtain ⟨j, hj⟩ : ∃ j, d (0, j) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 := congrFun (hf (mem_support_iff.mp hd)) 0
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finset.sum_eq_zero] at h0
    · omega
    · rintro ⟨i, j'⟩ _
      simp only [groupWeight, Pi.smul_apply, smul_eq_mul]
      by_cases hi : i = 0
      · subst hi; simp [hcon j']
      · simp [Ne.symm hi]
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := (0, j)) (Finset.mem_univ _) ?_)
  simp [zero_pow hj]

def parVar (e n : ℕ) (ij : Fin (e + 1) × Fin n) : Fin n ⊕ Par e n :=
  Fin.cases (motive := fun _ => Fin n ⊕ Par e n) (.inl ij.2) (fun i => .inr (.inl (i, ij.2))) ij.1

theorem parVar_injective : Function.Injective (parVar e n) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  induction i using Fin.cases <;> induction i' using Fin.cases <;> simp_all [parVar]

theorem specRest_X {k : Type*} [Field k] (f : MvPolynomial (Fin (e + 1) × Fin n) k) :
    specRest (algebraMap k (MvPolynomial (Par e n) k)) f X =
      sumAlgEquiv k (Fin n) (Par e n) (rename (parVar e n) f) := by
  unfold specRest
  rw [MvPolynomial.algebraMap_eq]
  induction f using MvPolynomial.induction_on with
  | C a => simp [sumAlgEquiv_C_inl]
  | add p q hp hq => simp [eval₂_add, hp, hq]
  | mul_X p ij hp =>
    obtain ⟨i, j⟩ := ij
    induction i using Fin.cases <;>
      simp [eval₂_mul, hp, parVar, sumAlgEquiv_X_inl, sumAlgEquiv_X_inr]

theorem proof (h1 : GroundTheory.Heights₂.Heights.IncIdealPrime.Statement)
    (h2 : GroundTheory.Heights₂.Heights.ChowFormMultiHomog.Statement) : GenChowIrreducible.Statement := by
  intro k _ n e Q g hQ hg

  have hspan : GroundTheory.Heights₂.Heights.incIdeal Q (e + 1) = Ideal.span {g} := by
    ext p
    rw [Ideal.mem_span_singleton, ← hg.2 p]
    simp [GroundTheory.Heights₂.Heights.incIdeal, Submodule.mem_iInf, RingHom.mem_ker]
  have hprime : Prime g := by
    have := h1 k n (e + 1) Q hQ.isPrime hQ.isRelevant
    rw [hspan] at this
    exact (Ideal.span_singleton_prime hg.1).mp this
  obtain ⟨δ, hδ, hhom⟩ := h2 k n (e + 1) Q g hQ hg

  have hren : Prime (rename (parVar e n) g) := by
    have e1 : rename (parVar e n) g = rename ((↑) : Set.range (parVar e n) → _)
        (rename (Equiv.ofInjective _ parVar_injective) g) := by
      rw [rename_rename]; rfl
    rw [e1, prime_rename_iff]
    exact (MulEquiv.prime_iff (renameEquiv k (Equiv.ofInjective _ parVar_injective))).mpr hprime
  have hpP : Prime (specRest (algebraMap k (MvPolynomial (Par e n) k)) g X) := by
    rw [specRest_X]
    exact (MulEquiv.prime_iff (sumAlgEquiv k (Fin n) (Par e n))).mpr hren
  set p := specRest (algebraMap k (MvPolynomial (Par e n) k)) g X with hp
  have hq : specRest (algebraMap k (GenParField k e n)) g (genPar k e n) =
      p.map (algebraMap (MvPolynomial (Par e n) k) (GenParField k e n)) := by
    rw [hp, map_specRest, ← IsScalarTower.algebraMap_eq]; rfl

  let _ : Algebra (MvPolynomial (Fin n) (MvPolynomial (Par e n) k))
      (MvPolynomial (Fin n) (GenParField k e n)) := algebraMvPolynomial
  have hc0 : constantCoeff p = 0 := constantCoeff_specRest _ hδ hhom _
  have hdisj : Disjoint
      (((nonZeroDivisors (MvPolynomial (Par e n) k)).map (C (σ := Fin n)) : Submonoid _) :
        Set (MvPolynomial (Fin n) (MvPolynomial (Par e n) k))) ↑(Ideal.span {p}) := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hmem
    rw [SetLike.mem_coe, Ideal.mem_span_singleton] at hmem
    obtain ⟨s, hs⟩ := hmem
    have := congrArg constantCoeff hs
    rw [constantCoeff_C, map_mul, hc0, zero_mul] at this
    exact nonZeroDivisors.ne_zero hr this
  have hpr := IsLocalization.isPrime_of_isPrime_disjoint
    ((nonZeroDivisors (MvPolynomial (Par e n) k)).map (C (σ := Fin n)))
    (MvPolynomial (Fin n) (GenParField k e n)) (Ideal.span {p})
    ((Ideal.span_singleton_prime hpP.ne_zero).mpr hpP) hdisj
  rw [Ideal.map_span, Set.image_singleton, algebraMap_def] at hpr
  have hq0 : p.map (algebraMap (MvPolynomial (Par e n) k) (GenParField k e n)) ≠ 0 := by
    intro h
    apply hpP.ne_zero
    apply map_injective _ (IsFractionRing.injective (MvPolynomial (Par e n) k) (GenParField k e n))
    rw [h, map_zero]
  rw [hq]
  exact ((Ideal.span_singleton_prime hq0).mp hpr).irreducible

end GenChowIrreducible

end

end GroundTheory.Heights₂.Heights.Vertical
