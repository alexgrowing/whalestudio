import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyCoeffsValuedBoundedOnCompactGLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyIntegralUnitConstCoeffOfMemMaxCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationEqOrConjOfUnderMaximalRealSubfieldEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticPolyConjSelfReciprocalCoeffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfBoundedEmbeddingsAndValuationsStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FinChar

theorem norm_coeff_le_of_mem_ell (E : Type) [Field E] (n : ℕ) (P : E[X]) (hP : P ∈ Ell E n) (τ : E →+* ℂ) (k : ℕ) :
    ‖τ (P.coeff k)‖ ≤ (2 : ℝ) ^ n := by
  obtain ⟨hm, hd, -, hr⟩ := hP
  have h := Polynomial.coeff_le_of_roots_le (f := τ) (B := 1) k hm (IsAlgClosed.splits _) (fun z hz => (hr τ z hz).le)
  rw [Polynomial.coeff_map, one_pow, one_mul, hd] at h
  exact h.trans (by exact_mod_cast Nat.choose_le_two_pow n k)

theorem finite_ell_charpoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ C : ∀ w : Pl E, Set (GLw n w), (∀ w, IsCompact (C w)) → (∀ᶠ w in cofinite, C w ⊆ GlobalTheory.LFun.KGL w n) → {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, ∃ g ∈ C w, g.val.charpoly = atPl w P}.Finite := by
  intro E _ _ _ n S hS C hC hK
  set T := {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, ∃ g ∈ C w, g.val.charpoly = atPl w P} with hT
  choose σ hσ using fun w => (hS w).exists
  choose B hB using fun w => GlobalTheory.T.charpoly_coeffs_valued_bounded_on_compact_GL E n w (C w) (hC w)
  have loc : ∀ P ∈ T, ∀ u ∈ S, (∀ k, u.valuation E (P.coeff k) ≤ B u) ∧ u.valuation E (P.coeff 0)⁻¹ ≤ B u ∧
      (C u ⊆ GlobalTheory.LFun.KGL u n → (∀ k, u.valuation E (P.coeff k) ≤ 1) ∧ u.valuation E (P.coeff 0) = 1) := by
    intro P hP u hu
    obtain ⟨g, hg, hgP⟩ := hP.2 u hu
    have e : ∀ k, u.valuation E (P.coeff k) = Valued.v (g.val.charpoly.coeff k) := fun k => by
      rw [hgP, Polynomial.coeff_map]; exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u _).symm
    refine ⟨fun k => (e k).trans_le ((hB u g hg).1 k), ?_, fun hsub => ?_⟩
    · rw [map_inv₀, e, ← map_inv₀]; exact (hB u g hg).2
    · have := GlobalTheory.T.charpoly_integral_unit_constCoeff_of_mem_maxCompact E n u g (hsub hg)
      exact ⟨fun k => (e k).trans_le (this.1 k), (e 0).trans this.2⟩
  have glob : ∀ P ∈ T, ∀ w : Pl E, ∀ k, w.valuation E (P.coeff k) ≤ max (B (σ w)) (B (σ w) * B (σ w)) ∧
      (C (σ w) ⊆ GlobalTheory.LFun.KGL (σ w) n → w.valuation E (P.coeff k) ≤ 1) := by
    intro P hP w k
    have hu := loc P hP (σ w) (hσ w).1
    obtain ⟨h0, hc⟩ := GlobalTheory.T.elliptic_poly_conj_selfReciprocal_coeff E n P hP.1
    rcases GlobalTheory.T.valuation_eq_or_conj_of_under_maximalRealSubfield_eq E w (σ w) (hσ w).2 with h | h
    · rw [h]
      exact ⟨(hu.1 k).trans (le_max_left _ _), fun hs => (hu.2.2 hs).1 k⟩
    · rw [h]
      by_cases hk : k ≤ n
      · have e : IsCMField.complexConj E (P.coeff k) = P.coeff (n - k) * (P.coeff 0)⁻¹ := by
          rw [← hc k hk]; field_simp
        rw [e, map_mul]
        refine ⟨(mul_le_mul' (hu.1 _) hu.2.1).trans (le_max_right _ _), fun hs => ?_⟩
        rw [map_inv₀, (hu.2.2 hs).2, inv_one, mul_one]; exact (hu.2.2 hs).1 _
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hP.1.2.1]; omega), map_zero, map_zero]
        exact ⟨zero_le', fun _ => zero_le'⟩
  set A := {x : E | ∃ P ∈ T, ∃ k, P.coeff k = x} with hA
  have hAfin : A.Finite := by
    refine GlobalTheory.T.finite_of_bounded_embeddings_and_valuations E A ((2 : ℝ) ^ n) ?_ ?_ ?_
    · rintro _ ⟨P, hP, k, rfl⟩ τ; exact norm_coeff_le_of_mem_ell E n P hP.1 τ k
    · intro w; exact ⟨_, by rintro _ ⟨P, hP, k, rfl⟩; exact (glob P hP w k).1⟩
    · have hbad : {u : Pl E | ¬ C u ⊆ GlobalTheory.LFun.KGL u n}.Finite := Filter.eventually_cofinite.1 hK
      have : {w : Pl E | ¬ ∀ x ∈ A, w.valuation E x ≤ 1} ⊆ ⋃ u ∈ {u : Pl E | ¬ C u ⊆ GlobalTheory.LFun.KGL u n},
          {w : Pl E | w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E))} := by
        intro w hw
        simp only [Set.mem_setOf_eq, Set.mem_iUnion] at hw ⊢
        refine ⟨σ w, fun hs => hw ?_, (hσ w).2.symm⟩
        rintro _ ⟨P, hP, k, rfl⟩; exact (glob P hP w k).2 hs
      refine Filter.eventually_cofinite.2 (Set.Finite.subset (hbad.biUnion fun u _ => ?_) this)
      exact ((IsDedekindDomain.primesOver_finite (u.under (𝓞 (maximalRealSubfield E))).asIdeal (𝓞 E)).preimage
        (fun a _ b _ h => HeightOneSpectrum.ext h)).subset fun w hw => ⟨w.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hw).symm⟩⟩
  refine Set.Finite.of_finite_image (f := fun P : E[X] => fun k : Fin (n + 1) => P.coeff k) ?_ ?_
  · refine (Set.Finite.pi (t := fun _ : Fin (n + 1) => A) fun _ => hAfin).subset ?_
    rintro _ ⟨P, hP, rfl⟩ k _
    exact ⟨P, hP, k, rfl⟩
  · intro P hP Q hQ h
    ext k
    by_cases hk : k ≤ n
    · exact congrFun h ⟨k, Nat.lt_succ_of_le hk⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hP.1.2.1]; omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hQ.1.2.1]; omega)]

end GlobalTheory.FinChar
