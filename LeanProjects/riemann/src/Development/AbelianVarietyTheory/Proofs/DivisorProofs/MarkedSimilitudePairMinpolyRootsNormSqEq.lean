import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import GroundTheory.Brauer.TensorSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairGramInvCongruent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairHermitianFormInvertibleSimilitude
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormNegOnOrthogonalOfPositiveIndexOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegDefOfHermitianMatrixPositiveIndexEqZero
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.MarkEll

theorem star_mulVec_dot {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ) :
    star (M *ᵥ a) ⬝ᵥ (A *ᵥ (M *ᵥ b)) = star a ⬝ᵥ ((Mᴴ * A * M) *ᵥ b) := by
  rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec, vecMul_vecMul, Matrix.mul_assoc]

theorem normSq_eq_of_form {n : ℕ} (Γ A : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (hΓ : Γᴴ * A * Γ = (c : ℂ) • A)
    (x : Fin n → ℂ) (w : ℂ) (hx : Γ *ᵥ x = w • x) (h0 : star x ⬝ᵥ (A *ᵥ x) ≠ 0) : ‖w‖ ^ 2 = c := by
  have h := star_mulVec_dot Γ A x x
  rw [hΓ, hx] at h
  simp only [Matrix.smul_mulVec, mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h
  rw [← mul_assoc] at h
  have h2 : w * star w = (c : ℂ) := mul_right_cancel₀ h0 h
  have h3 : ((‖w‖ ^ 2 : ℝ) : ℂ) = (c : ℂ) := by
    rw [← h2, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact_mod_cast h3

theorem natDegree_minpoly_le_tmul {F A : Type} [Field F] [Ring A] [Algebra F A] (K : Type)
    [Field K] [Algebra F K] (g : A) (hK : IsIntegral K ((1 : K) ⊗ₜ[F] g)) :
    (minpoly F g).natDegree ≤ (minpoly K ((1 : K) ⊗ₜ[F] g)).natDegree := by
  set x : K ⊗[F] A := (1 : K) ⊗ₜ[F] g with hx
  have hli : LinearIndependent K (fun j : Fin (minpoly F g).natDegree => x ^ (j : ℕ)) := by
    have h := Module.Flat.linearIndependent_one_tmul (S := K) (linearIndependent_pow (K := F) g)
    convert h using 1
    funext j
    simp [hx, Algebra.TensorProduct.tmul_pow]
  by_contra hlt
  push_neg at hlt
  have hsum := Polynomial.aeval_eq_sum_range' hlt x
  rw [minpoly.aeval, ← Fin.sum_univ_eq_sum_range (fun i => (minpoly K x).coeff i • x ^ i)] at hsum
  have hc := Fintype.linearIndependent_iff.mp hli (fun i => (minpoly K x).coeff i) hsum.symm
  apply minpoly.ne_zero hK
  ext i
  rw [Polynomial.coeff_zero]
  by_cases hi : i < (minpoly F g).natDegree
  · exact hc ⟨i, hi⟩
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem eigA : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (g : G.C) (v : InfinitePlace G.F) (z : ℂ),
    (minpoly G.F g).natDegree = G.n → (minpoly G.F g).eval₂ v.embedding z = 0 →
    ∃ x : Fin G.n → ℂ, x ≠ 0 ∧ G.psi v g *ᵥ x = z • x := by
  intro p _ G g v z hdeg hz
  letI alg : Algebra G.F ℂ := v.embedding.toAlgebra
  have halg : ∀ a : G.F, algebraMap G.F ℂ a = v.embedding a := fun a => rfl
  let ψF : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ :=
    { G.psi v with
      commutes' := fun a => by
        change G.psi v (algebraMap G.F G.C a) = _
        rw [G.psi_F]
        ext i j
        simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply, halg] }
  let Θ : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ψF (fun a _ => Algebra.commute_algebraMap_left a _)
  have hinj : Function.Injective Θ :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain Θ.toRingHom).resolve_right
      (by haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩; exact not_subsingleton _)
  set x : ℂ ⊗[G.F] G.C := (1 : ℂ) ⊗ₜ[G.F] g with hx
  have hxi : IsIntegral ℂ x := IsIntegral.of_finite ℂ x
  have hge := natDegree_minpoly_le_tmul ℂ g hxi
  have hΘx : Θ x = G.psi v g := by
    rw [hx]
    first
      | (erw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl)
      | (show (Algebra.ofId ℂ (Matrix (Fin G.n) (Fin G.n) ℂ)) 1 * ψF g = G.psi v g
         rw [map_one, one_mul]; rfl)
      | simp [Θ, ψF]
  have hmin : minpoly ℂ (G.psi v g) = minpoly ℂ x := by rw [← hΘx]; exact minpoly.algHom_eq Θ hinj x
  have hgi : IsIntegral G.F g := IsIntegral.of_finite G.F g
  have hdvd : minpoly ℂ (G.psi v g) ∣ (minpoly G.F g).map (algebraMap G.F ℂ) := by
    apply minpoly.dvd
    rw [Polynomial.aeval_map_algebraMap]
    change Polynomial.aeval (ψF g) (minpoly G.F g) = 0
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hmon : ((minpoly G.F g).map (algebraMap G.F ℂ)).Monic := (minpoly.monic hgi).map _
  have heq : (minpoly G.F g).map (algebraMap G.F ℂ) = minpoly ℂ (G.psi v g) := by
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic ?_) hmon hdvd ?_
    · exact IsIntegral.of_finite ℂ _
    · rw [Polynomial.natDegree_map, hmin]; exact hge
  have hroot : (minpoly ℂ (Matrix.toLin' (G.psi v g))).IsRoot z := by
    rw [Matrix.minpoly_toLin', ← heq, Polynomial.IsRoot, Polynomial.eval_map]
    exact hz
  obtain ⟨y, hy⟩ := (Module.End.hasEigenvalue_iff_isRoot.mpr hroot).exists_hasEigenvector
  refine ⟨y, hy.2, ?_⟩
  have := hy.apply_eq_smul
  rwa [Matrix.toLin'_apply] at this

theorem normSq_of_eigenvector {p : ℕ} [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ) (ha : G.a = 1)
    (hm : P.Mark μ) (v : InfinitePlace G.F) (x : Fin G.n → ℂ) (hx0 : x ≠ 0) (w : ℂ)
    (hx : G.psi v P.γ *ᵥ x = w • x) : ‖w‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  obtain ⟨-, -, hΓ⟩ := GlobalTheory.LKMid.pair_form_laws p G P v
  obtain ⟨Z, hZ⟩ := GlobalTheory.LKMid.Pair.gram_psi_inv_congr p G P v
  set A := G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) with hAdef
  set Γ := G.psi v P.γ with hΓdef
  have hΓ' : Γᴴ * A * Γ = ((((P.c : ℚ) : ℝ)) : ℂ) • A := by rw [hΓ]; push_cast; rfl
  have cong : ∀ a b : Fin G.n → ℂ, star a ⬝ᵥ (A *ᵥ b) =
      star ((Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a) ⬝ᵥ (G.gram v *ᵥ ((Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ b)) := by
    intro a b; rw [star_mulVec_dot, ← hZ]
  have Zne : ∀ a : Fin G.n → ℂ, a ≠ 0 → (Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a ≠ 0 := by
    intro a ha h
    apply ha
    have := congrArg (fun y => ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ y) h
    simpa only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec, mulVec_zero] using this
  have hc0 : ((((P.c : ℚ) : ℝ)) : ℂ) ≠ 0 := by
    have : ((P.c : ℚ)) ≠ 0 := P.c.ne_zero
    exact_mod_cast this
  rcases G.sig v with ⟨h1, -⟩ | ⟨h0, -⟩
  · obtain ⟨v0, hv0, x0, hx0e, hpos⟩ := hm
    have hv : v = v0 := by
      have hcard : Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} ≤ 1 := by
        have := ha; unfold HTGroup.a at this; omega
      haveI := Fintype.card_le_one_iff_subsingleton.mp hcard
      exact congrArg Subtype.val (Subsingleton.elim (⟨v, h1⟩ : {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1})
        ⟨v0, hv0⟩)
    subst hv
    have hS0 : star x0 ⬝ᵥ (A *ᵥ x0) ≠ 0 := fun h => by rw [h] at hpos; simp at hpos
    have hμ : ‖μ‖ ^ 2 = ((P.c : ℚ) : ℝ) := normSq_eq_of_form Γ A _ hΓ' x0 μ hx0e hS0
    by_cases hw : w = μ
    · rw [hw]; exact hμ
    · have hS : star x0 ⬝ᵥ (A *ᵥ x) = 0 := by
        by_contra hne
        have h := star_mulVec_dot Γ A x0 x
        rw [hΓ', hx0e, hx] at h
        simp only [Matrix.smul_mulVec, mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct,
          smul_eq_mul] at h
        rw [← mul_assoc] at h
        have h2 := mul_right_cancel₀ hne h
        have hμ2 : μ * star μ = ((((P.c : ℚ) : ℝ)) : ℂ) := by
          rw [← hμ, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        have hμ0 : star μ ≠ 0 := by
          intro h0; apply hc0; rw [← hμ2, h0, mul_zero]
        apply hw
        apply mul_right_cancel₀ hμ0
        rw [hμ2]
        first | exact h2 | (rw [mul_comm]; exact h2)
      apply normSq_eq_of_form Γ A _ hΓ' x w hx
      intro h
      have hneg := GlobalTheory.re_form_neg_of_orth_of_sigPosH_eq_one (G.gram v) (G.gram_herm v) (G.gram_det v) h1 _ _
        (by rw [← cong]; exact hpos) (by rw [← cong]; exact hS) (Zne x hx0)
      rw [← cong, h] at hneg; simp at hneg
  · apply normSq_eq_of_form Γ A _ hΓ' x w hx
    intro h
    have hneg := GlobalTheory.herm_negDef_of_sigPosH_eq_zero (G.gram v) (G.gram_herm v) (G.gram_det v) h0 _ (Zne x hx0)
    rw [← cong, h] at hneg; simp at hneg

theorem mark_ell : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ →
    ∀ (φ : G.F →+* ℂ) (z : ℂ), P.pol.eval₂ φ z = 0 → ‖z‖ ^ 2 = ((P.c : ℚ) : ℝ) := by
  intro p _ G P μ ha hm φ z hz
  have hdeg : (minpoly G.F (P.γ : G.C)).natDegree = G.n := P.reg.1
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · obtain ⟨x, hx0, hx⟩ := eigA p G (P.γ : G.C) (InfinitePlace.mk φ) z hdeg (by rw [h]; exact hz)
    exact normSq_of_eigenvector G P μ ha hm _ x hx0 z hx
  · have hz' : (minpoly G.F (P.γ : G.C)).eval₂ (InfinitePlace.mk φ).embedding (star z) = 0 := by
      have e : (InfinitePlace.mk φ).embedding = (starRingEnd ℂ).comp φ := by
        rw [h]; ext x; simp [ComplexEmbedding.conjugate_coe_eq]
      have := Polynomial.hom_eval₂ P.pol φ (starRingEnd ℂ) z
      rw [hz, map_zero] at this
      rw [e]; exact this.symm
    obtain ⟨x, hx0, hx⟩ := eigA p G (P.γ : G.C) (InfinitePlace.mk φ) (star z) hdeg hz'
    have := normSq_of_eigenvector G P μ ha hm _ x hx0 (star z) hx
    rwa [norm_star] at this

end GlobalTheory.LKMid.MarkEll
