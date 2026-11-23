import Mathlib
import Formalism.QuotientMetricDivisors.ProdFormula

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

section SpecDetAux

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def metMat {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K) :
    Matrix (Fin d) (Fin d) ℂ :=
  ((X v)⁻¹).conjTranspose * (X v)⁻¹

def cv {d : ℕ} (σ : K →+* ℂ) (x : Fin d → K) : Fin d → ℂ := fun i => σ (x i)

lemma star_mulVec_dot {d : ℕ} (A N : Matrix (Fin d) (Fin d) ℂ) (u w : Fin d → ℂ) :
    star (A *ᵥ u) ⬝ᵥ (N *ᵥ (A *ᵥ w)) = star u ⬝ᵥ ((Aᴴ * N * A) *ᵥ w) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

lemma majAt_eq {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K)
    (x y : Fin d → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y =
      star (cv v.embedding x) ⬝ᵥ (metMat X v *ᵥ cv v.embedding y) := by
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, Pi.basisFun_repr]
  rw [metMat, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  rfl

lemma cv_mulVec {d : ℕ} (σ : K →+* ℂ) (φ : Matrix (Fin d) (Fin d) K) (x : Fin d → K) :
    cv σ (φ *ᵥ x) = (φ.map σ) *ᵥ cv σ x := by
  ext i
  exact RingHom.map_mulVec σ φ x i

lemma cv_single {d : ℕ} (σ : K →+* ℂ) (a : Fin d) :
    cv σ (Pi.single a (1 : K)) = Pi.single a (1 : ℂ) := by
  ext i
  rcases eq_or_ne i a with rfl | h
  · simp [cv]
  · simp [cv, Pi.single_eq_of_ne h]

lemma single_dot_single {d : ℕ} (N : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) :
    star (Pi.single a (1 : ℂ)) ⬝ᵥ (N *ᵥ Pi.single b (1 : ℂ)) = N a b := by
  have hs : star (Pi.single a (1 : ℂ) : Fin d → ℂ) = Pi.single a 1 := by
    ext i
    rcases eq_or_ne i a with rfl | h
    · simp
    · simp [Pi.single_eq_of_ne h]
  rw [hs]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

lemma conjT_mul_mul_apply {n : ℕ} (A N : Matrix (Fin n) (Fin n) ℂ) (a a' : Fin n) :
    (Aᴴ * N * A) a a' = star (fun i => A i a) ⬝ᵥ (N *ᵥ fun i => A i a') := by
  have hcol : ∀ c, A *ᵥ Pi.single c (1 : ℂ) = fun i => A i c := by
    intro c
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← single_dot_single (Aᴴ * N * A) a a', ← star_mulVec_dot, hcol, hcol]

lemma detRatio_eq {d : ℕ} (XS XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (φ : Matrix (Fin d) (Fin d) K) (v : InfinitePlace K) :
    detRatio XS XT φ v =
      ((φ.map v.embedding)ᴴ * metMat XT v * φ.map v.embedding).det.re / (metMat XS v).det.re := by
  have h1 : gram XT v (fun i => φ.mulVec (Pi.single i 1)) =
      (φ.map v.embedding)ᴴ * metMat XT v * φ.map v.embedding := by
    ext a c
    simp only [gram, Formalism.HN.gramPl, Matrix.of_apply]
    rw [majAt_eq, cv_mulVec, cv_mulVec, cv_single, cv_single, star_mulVec_dot, single_dot_single]
  have h2 : gram XS v (fun i => (Pi.single i 1 : Fin d → K)) = metMat XS v := by
    ext a c
    simp only [gram, Formalism.HN.gramPl, Matrix.of_apply]
    rw [majAt_eq, cv_single, cv_single, single_dot_single]
  rw [detRatio, h1, h2]

lemma metMat_det_re_ne {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (v : InfinitePlace K) (hX : IsUnit (X v).det) : (metMat X v).det.re ≠ 0 := by
  have hY : ((X v)⁻¹).det ≠ 0 := (Matrix.isUnit_nonsing_inv_det (X v) hX).ne_zero
  have hm : (metMat X v).det = (Complex.normSq ((X v)⁻¹).det : ℂ) := by
    rw [metMat, Matrix.det_mul, Matrix.det_conjTranspose, Complex.normSq_eq_conj_mul_self]
    rfl
  rw [hm, Complex.ofReal_re]
  exact (Complex.normSq_pos.mpr hY).ne'

lemma det_of_scalar {D : ℕ} (σ : K →+* ℂ) {Ix : Type} [Fintype Ix]
    (Qp : Ix → Submodule K (Fin D → K)) (hind : iSupIndep Qp) (htop : (⨆ p, Qp p) = ⊤)
    (N1 N2 : Matrix (Fin D) (Fin D) ℂ) (c : Ix → ℂ)
    (h : ∀ p, ∀ x ∈ Qp p, ∀ y : Fin D → K,
      star (cv σ x) ⬝ᵥ (N1 *ᵥ cv σ y) = c p * (star (cv σ x) ⬝ᵥ (N2 *ᵥ cv σ y))) :
    N1.det = (∏ p, c p ^ finrank K (Qp p)) * N2.det ∧ ∑ p, finrank K (Qp p) = D := by
  classical
  have hint : DirectSum.IsInternal Qp :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top Qp).mpr ⟨hind, htop⟩
  let b := hint.collectedBasis (fun p => Module.finBasis K (Qp p))
  have hcard : Fintype.card (Σ p, Fin (finrank K (Qp p))) = D := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fin_fun]
  have hsum : ∑ p, finrank K (Qp p) = D := by
    have hc := hcard
    rw [Fintype.card_sigma] at hc
    simpa using hc
  refine ⟨?_, hsum⟩
  let e := Fintype.equivFinOfCardEq hcard
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix (Fin D) (Fin D) K,
      Q = (Pi.basisFun K (Fin D)).toMatrix (b.reindex e) := ⟨_, rfl⟩
  have hQ : Q.det ≠ 0 := by
    have hu := (Pi.basisFun K (Fin D)).isUnit_det (b.reindex e)
    rw [Module.Basis.det_apply, ← hQdef] at hu
    exact hu.ne_zero
  obtain ⟨Qs, hQs⟩ : ∃ M : Matrix (Fin D) (Fin D) ℂ, M = Q.map σ := ⟨_, rfl⟩
  have hQs_det : Qs.det ≠ 0 := by
    rw [hQs, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero σ).mpr hQ
  have hcol : ∀ a, (fun i => Qs i a) = cv σ (b (e.symm a)) := by
    intro a
    ext i
    simp [hQs, hQdef, cv, Module.Basis.toMatrix_apply, Module.Basis.reindex_apply]
  have hmem : ∀ a, b (e.symm a) ∈ Qp (e.symm a).1 := fun a => hint.collectedBasis_mem _ _
  have key : Qsᴴ * N1 * Qs = Matrix.diagonal (fun a => c (e.symm a).1) * (Qsᴴ * N2 * Qs) := by
    ext a a'
    rw [Matrix.diagonal_mul, conjT_mul_mul_apply, conjT_mul_mul_apply, hcol, hcol]
    exact h _ _ (hmem a) _
  have hdet := congrArg Matrix.det key
  simp only [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_conjTranspose] at hdet
  have hne : star Qs.det * Qs.det ≠ 0 := mul_ne_zero (star_ne_zero.mpr hQs_det) hQs_det
  have hprod : ∏ a, c (e.symm a).1 = ∏ p, c p ^ finrank K (Qp p) := by
    rw [Equiv.prod_comp e.symm (fun s => c s.1), Fintype.prod_sigma]
    simp
  rw [← hprod]
  apply mul_right_cancel₀ hne
  linear_combination hdet

lemma detRatio_of_scalar (v : InfinitePlace K) {d : ℕ}
    (XS XT : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hS : IsUnit (XS v).det)
    (φ : Matrix (Fin d) (Fin d) K) {Ix : Type} [Fintype Ix]
    (Qp : Ix → Submodule K (Fin d → K)) (hind : iSupIndep Qp) (htop : (⨆ p, Qp p) = ⊤)
    (c : Ix → ℝ)
    (h : ∀ p, ∀ x ∈ Qp p, ∀ y : Fin d → K,
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) XT v (φ.mulVec x) (φ.mulVec y) =
        ((c p : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) XS v x y) :
    detRatio XS XT φ v = ∏ p, c p ^ finrank K (Qp p) ∧ ∑ p, finrank K (Qp p) = d := by
  obtain ⟨hdet, hsum⟩ := det_of_scalar v.embedding Qp hind htop
    ((φ.map v.embedding)ᴴ * metMat XT v * φ.map v.embedding) (metMat XS v)
    (fun p => ((c p : ℝ) : ℂ)) (by
      intro p x hx y
      rw [← star_mulVec_dot, ← cv_mulVec, ← cv_mulVec, ← majAt_eq, ← majAt_eq]
      exact h p x hx y)
  refine ⟨?_, hsum⟩
  rw [detRatio_eq, hdet]
  have hm := metMat_det_re_ne XS v hS
  have hc : (∏ p, ((c p : ℝ) : ℂ) ^ finrank K (Qp p)) =
      ((∏ p, c p ^ finrank K (Qp p) : ℝ) : ℂ) := by
    simp [Complex.ofReal_prod]
  rw [hc, Complex.re_ofReal_mul]
  field_simp

end SpecDetAux

theorem spectral_determinant_formula : SpecDet := by
  unfold SpecDet
  intro K _ _ _ v D XQ XE hXQ hXE ι hι J _ d XT XW hXT hXW θ hθ Ix _ Qp Tq hind htop hindT htopT
    hdim s lam hQ hT
  obtain ⟨h1, hsum⟩ :=
    detRatio_of_scalar v XQ XE (hXQ v) ι Qp hind htop (fun p => s * ∏ j, lam j p) hQ
  have h2 : ∀ j, detRatio (XT j) (XW j) (θ j) v = ∏ p, lam j p ^ finrank K (Qp p) := by
    intro j
    obtain ⟨h, -⟩ := detRatio_of_scalar v (XT j) (XW j) (hXT j v) (θ j) (Tq j) (hindT j)
      (htopT j) (lam j) (hT j)
    rw [h]
    exact Finset.prod_congr rfl (fun p _ => by rw [hdim j p])
  rw [h1, Finset.prod_congr rfl (fun j _ => h2 j)]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum, Finset.prod_pow]
  congr 1
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [Finset.prod_pow]

end Formalism.DivisionValues
