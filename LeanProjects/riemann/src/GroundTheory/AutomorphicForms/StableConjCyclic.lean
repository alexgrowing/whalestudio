import Mathlib

namespace GroundTheory.Automorphic

open Polynomial Module Matrix

section AlgClosed

variable {K W : Type*} [Field K] [IsAlgClosed K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem exists_linearIndependent_pow_apply_of_isAlgClosed (f : Module.End K W)
    (hf : f.charpoly.Separable) :
    ∃ w : W, LinearIndependent K (fun k : Fin (finrank K W) => (f ^ (k : ℕ)) w) := by
  set n := finrank K W
  have hdeg : f.charpoly.natDegree = n := LinearMap.charpoly_natDegree f
  have hnd := nodup_roots hf
  let s : Finset K := ⟨f.charpoly.roots, hnd⟩
  have hs : s.card = n := by
    change f.charpoly.roots.card = n
    rw [IsAlgClosed.card_roots_eq_natDegree, hdeg]
  let e : Fin n ≃ s := (s.equivFin.trans (finCongr hs)).symm
  let μ : Fin n → K := fun j => (e j : K)
  have hμ : Function.Injective μ := Subtype.coe_injective.comp e.injective
  have hroot : ∀ j, f.charpoly.IsRoot (μ j) := fun j =>
    (mem_roots hf.ne_zero).1 (e j).2
  have hev : ∀ j, f.HasEigenvalue (μ j) := fun j =>
    (Module.End.hasEigenvalue_iff_isRoot_charpoly f _).2 (hroot j)
  choose w hw using fun j => (hev j).exists_hasEigenvector
  have hli : LinearIndependent K w := f.eigenvectors_linearIndependent' μ hμ w hw
  have hpow : ∀ (k : ℕ) j, (f ^ k) (w j) = μ j ^ k • w j := by
    intro k j
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, (hw j).apply_eq_smul, smul_smul,
        pow_succ]
  refine ⟨∑ j, w j, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hsum : ∀ j, ∑ k : Fin n, c k * μ j ^ (k : ℕ) = 0 := by
    have h2 : ∑ j, (∑ k : Fin n, c k * μ j ^ (k : ℕ)) • w j = 0 := by
      rw [← hc]
      simp only [map_sum, hpow, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact fun j => (Fintype.linearIndependent_iff.1 hli) _ h2 j
  have hV : Matrix.vandermonde μ *ᵥ c = 0 := by
    ext j
    simp only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply]
    rw [← hsum j]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hdet : (Matrix.vandermonde μ).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.2 hμ
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hV)

end AlgClosed

section Krylov

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

def krylov (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i k => (M ^ (k : ℕ) *ᵥ v) i

theorem krylov_col (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) (k : Fin n) :
    (krylov M v).col k = M ^ (k : ℕ) *ᵥ v := rfl

theorem map_krylov (φ : R →+* S) (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    (krylov M v).map φ = krylov (M.map φ) (φ ∘ v) := by
  ext i k
  simp only [krylov, Matrix.map_apply, Matrix.of_apply]
  rw [RingHom.map_mulVec]
  congr 2
  exact (map_pow φ.mapMatrix M k)

variable {E : Type*} [Field E]

theorem map_det_krylov_C_X {T : Type*} [CommRing T] (M : Matrix (Fin n) (Fin n) E)
    (ψ : MvPolynomial (Fin n) E →+* T) :
    ψ (krylov (M.map MvPolynomial.C) (fun i => MvPolynomial.X i)).det =
      (krylov ((M.map MvPolynomial.C).map ψ) (ψ ∘ fun i => MvPolynomial.X i)).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, map_krylov]

variable [Infinite E]

theorem exists_det_krylov_ne_zero {L : Type*} [Field L] (φ : E →+* L)
    (M : Matrix (Fin n) (Fin n) E) (w : Fin n → L) (hw : (krylov (M.map φ) w).det ≠ 0) :
    ∃ v : Fin n → E, (krylov M v).det ≠ 0 := by
  classical
  set D : MvPolynomial (Fin n) E :=
    (krylov (M.map MvPolynomial.C) (fun i => MvPolynomial.X i)).det with hD
  have hD0 : D ≠ 0 := by
    intro h0
    have := map_det_krylov_C_X M (MvPolynomial.eval₂Hom φ w)
    rw [← hD] at this
    rw [h0, map_zero] at this
    apply hw
    rw [this]
    congr 2
    · ext i j; simp
    · ext i; simp
  by_contra hne
  push Not at hne
  apply hD0
  apply MvPolynomial.funext
  intro x
  rw [map_zero]
  have := map_det_krylov_C_X M (MvPolynomial.eval x)
  rw [← hD] at this
  rw [this]
  convert hne x using 3
  · ext i j; simp
  · ext i; simp

end Krylov

section Cyclic

variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]

theorem exists_linearIndependent_pow_apply [Infinite E] (f : Module.End E V)
    (hf : f.charpoly.Separable) :
    ∃ v : V, LinearIndependent E (fun k : Fin (finrank E V) => (f ^ (k : ℕ)) v) := by
  classical
  set n := finrank E V
  let b : Basis (Fin n) E V := Module.finBasis E V
  set M := LinearMap.toMatrix b b f with hM
  let φ : E →+* AlgebraicClosure E := algebraMap E (AlgebraicClosure E)
  have hchar : (Matrix.toLin' (M.map φ)).charpoly = f.charpoly.map φ := by
    rw [Matrix.charpoly_toLin', Matrix.charpoly_map, hM, LinearMap.charpoly_toMatrix]
  have hsep : (Matrix.toLin' (M.map φ)).charpoly.Separable := by
    rw [hchar]; exact hf.map
  obtain ⟨w, hw⟩ := exists_linearIndependent_pow_apply_of_isAlgClosed _ hsep
  rw [Module.finrank_fin_fun] at hw
  have hw' : (krylov (M.map φ) w).det ≠ 0 := by
    rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
      ← Matrix.linearIndependent_cols_iff_isUnit]
    have hcol : (krylov (M.map φ) w).col = fun k : Fin n => (Matrix.toLin' (M.map φ) ^ (k : ℕ)) w := by
      ext1 k
      rw [krylov_col, ← Matrix.toLin'_pow, Matrix.toLin'_apply]
    rw [hcol]
    exact hw
  obtain ⟨v₀, hv₀⟩ := exists_det_krylov_ne_zero φ M w hw'
  have hli : LinearIndependent E (krylov M v₀).col := by
    rw [Matrix.linearIndependent_cols_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero]
    exact hv₀
  refine ⟨b.equivFun.symm v₀, ?_⟩
  have key : (fun k : Fin n => (f ^ (k : ℕ)) (b.equivFun.symm v₀)) =
      b.equivFun.symm ∘ (krylov M v₀).col := by
    ext1 k
    simp only [Function.comp_apply, krylov_col]
    apply b.equivFun.injective
    rw [LinearEquiv.apply_symm_apply, Basis.equivFun_apply, ← LinearMap.toMatrix_mulVec_repr b b,
      hM, LinearMap.toMatrix_pow]
    congr 1
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [key]
  exact hli.map' _ (LinearEquiv.ker _)

end Cyclic

section Consequences

variable {E V V' : Type*} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
  [AddCommGroup V'] [Module E V'] [FiniteDimensional E V']

def IsCyclicVector (f : Module.End E V) (v : V) : Prop :=
  LinearIndependent E (fun k : Fin (finrank E V) => (f ^ (k : ℕ)) v)

theorem exists_isCyclicVector [Infinite E] (f : Module.End E V) (hf : f.charpoly.Separable) :
    ∃ v, IsCyclicVector f v :=
  exists_linearIndependent_pow_apply f hf

variable {f : Module.End E V} {v : V}

noncomputable def cyclicBasis (hv : IsCyclicVector f v) : Basis (Fin (finrank E V)) E V :=
  basisOfLinearIndependentOfCardEqFinrank' _ hv (Fintype.card_fin _)

theorem cyclicBasis_apply (hv : IsCyclicVector f v) (k : Fin (finrank E V)) :
    cyclicBasis hv k = (f ^ (k : ℕ)) v :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' (K := E) _ hv _) k

omit [FiniteDimensional E V] in
theorem aeval_C_mul_X_pow_apply (f : Module.End E V) (a : E) (k : ℕ) (x : V) :
    aeval f (C a * X ^ k) x = a • (f ^ k) x := by
  simp [Module.algebraMap_end_apply]

theorem IsCyclicVector.exists_aeval_apply_eq (hv : IsCyclicVector f v) (x : V) :
    ∃ p : E[X], aeval f p v = x := by
  refine ⟨∑ k : Fin (finrank E V), C ((cyclicBasis hv).repr x k) * X ^ (k : ℕ), ?_⟩
  conv_rhs => rw [← (cyclicBasis hv).sum_repr x]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [aeval_C_mul_X_pow_apply, cyclicBasis_apply]

theorem IsCyclicVector.exists_eq_aeval (hv : IsCyclicVector f v) {g : Module.End E V}
    (hg : Commute f g) : ∃ p : E[X], g = aeval f p := by
  obtain ⟨p, hp⟩ := hv.exists_aeval_apply_eq (g v)
  refine ⟨p, (cyclicBasis hv).ext fun k => ?_⟩
  rw [cyclicBasis_apply, ← Module.End.mul_apply, ← ((hg.pow_left (k : ℕ)).eq), Module.End.mul_apply,
    ← hp, ← Module.End.mul_apply, ← Module.End.mul_apply, ← aeval_X_pow (R := E) f, ← map_mul,
    ← map_mul, mul_comm]

theorem IsCyclicVector.commute_of_commute (hv : IsCyclicVector f v) {g g' : Module.End E V}
    (hg : Commute f g) (hg' : Commute f g') : Commute g g' := by
  obtain ⟨p, rfl⟩ := hv.exists_eq_aeval hg
  obtain ⟨q, rfl⟩ := hv.exists_eq_aeval hg'
  exact (Commute.all p q).map (aeval f)

theorem aeval_apply_eq_sum_modByMonic (f : Module.End E V) (v : V) (p : E[X]) :
    aeval f p v = ∑ k : Fin (finrank E V), (p %ₘ f.charpoly).coeff k • (f ^ (k : ℕ)) v := by
  have hmon := LinearMap.charpoly_monic f
  conv_lhs => rw [← modByMonic_add_div p f.charpoly]
  rw [map_add, map_mul, LinearMap.aeval_self_charpoly, zero_mul, add_zero]
  by_cases h0 : p %ₘ f.charpoly = 0
  · simp [h0]
  have hdeg : (p %ₘ f.charpoly).natDegree < finrank E V := by
    rw [Polynomial.natDegree_lt_iff_degree_lt h0, ← LinearMap.charpoly_natDegree f,
      ← degree_eq_natDegree hmon.ne_zero]
    exact degree_modByMonic_lt p hmon
  rw [aeval_eq_sum_range' hdeg, LinearMap.sum_apply,
    Finset.sum_range (fun i => ((p %ₘ f.charpoly).coeff i • f ^ i) v)]
  rfl

theorem IsCyclicVector.exists_conj {f' : Module.End E V'} {v' : V'} (hv : IsCyclicVector f v)
    (hv' : IsCyclicVector f' v') (hch : f.charpoly = f'.charpoly) :
    ∃ e : V ≃ₗ[E] V', ∀ x, e (f x) = f' (e x) := by
  have hdim : finrank E V = finrank E V' := by
    rw [← LinearMap.charpoly_natDegree f, ← LinearMap.charpoly_natDegree f', hch]
  let e : V ≃ₗ[E] V' := (cyclicBasis hv).equiv (cyclicBasis hv') (finCongr hdim)
  have he : ∀ k : Fin (finrank E V), e ((f ^ (k : ℕ)) v) = (f' ^ (k : ℕ)) v' := by
    intro k
    rw [← cyclicBasis_apply hv, Basis.equiv_apply, cyclicBasis_apply]
    rfl
  have hp : ∀ p : E[X], e (aeval f p v) = aeval f' p v' := by
    intro p
    rw [aeval_apply_eq_sum_modByMonic, aeval_apply_eq_sum_modByMonic, map_sum, ← hch]
    rw [← (finCongr hdim).sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, he]
    rfl
  refine ⟨e, fun x => ?_⟩
  obtain ⟨p, rfl⟩ := hv.exists_aeval_apply_eq x
  have h1 : f (aeval f p v) = aeval f (X * p) v := by
    rw [map_mul, aeval_X, Module.End.mul_apply]
  rw [h1, hp, hp, map_mul, aeval_X, Module.End.mul_apply]

theorem exists_conj_of_charpoly_eq [Infinite E] {f f' : Module.End E V}
    (hf : f.charpoly.Separable) (hch : f.charpoly = f'.charpoly) :
    ∃ e : V ≃ₗ[E] V, ∀ x, e (f x) = f' (e x) := by
  obtain ⟨v, hv⟩ := exists_isCyclicVector f hf
  obtain ⟨v', hv'⟩ := exists_isCyclicVector f' (hch ▸ hf)
  exact hv.exists_conj hv' hch

theorem commute_of_commute_of_separable [Infinite E] {f g g' : Module.End E V}
    (hf : f.charpoly.Separable) (hg : Commute f g) (hg' : Commute f g') : Commute g g' := by
  obtain ⟨v, hv⟩ := exists_isCyclicVector f hf
  exact hv.commute_of_commute hg hg'

end Consequences

end GroundTheory.Automorphic
