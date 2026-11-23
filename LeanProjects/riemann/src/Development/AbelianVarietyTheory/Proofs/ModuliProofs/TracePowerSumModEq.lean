import Mathlib
open Polynomial

namespace GlobalTheory.TraceAeval

open Module

theorem trace_aeval_of_isNilpotent {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (g : Module.End ℂ V) (μ : ℂ) (h : IsNilpotent (g - algebraMap ℂ _ μ)) (p : ℂ[X]) :
    LinearMap.trace ℂ V (aeval g p) = (finrank ℂ V : ℂ) * p.eval μ := by
  have hk : ∀ k : ℕ, LinearMap.trace ℂ V (g ^ k) = (finrank ℂ V : ℂ) * μ ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent μ
        ((Commute.refl g).pow_left k) h
      rw [pow_succ, Module.End.mul_eq_comp, this, ih]; ring
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, eval_add]; ring
  | monomial k a =>
    rw [aeval_monomial, ← Algebra.smul_def, map_smul, hk, eval_monomial, smul_eq_mul]; ring

theorem coe_aeval_restrict {V : Type*} [AddCommGroup V] [Module ℂ V] (f : Module.End ℂ V)
    (N : Submodule ℂ V) (hf : ∀ x ∈ N, f x ∈ N) (p : ℂ[X]) (x : N) :
    ((aeval (f.restrict hf) p x : N) : V) = aeval f p x := by
  have hk : ∀ (k : ℕ) (x : N), ((((f.restrict hf) ^ k) x : N) : V) = (f ^ k) x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => intro x; simp [pow_succ, ih]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial k a => simp [aeval_monomial, hk]

theorem trace_aeval_end {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (f : Module.End ℂ V) (p : ℂ[X]) :
    LinearMap.trace ℂ V (aeval f p) = (f.charpoly.roots.map fun z => p.eval z).sum := by
  classical
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    f.independent_maxGenEigenspace (Module.End.iSup_maxGenEigenspace_eq_top f)
  have h_fin : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep f.independent_maxGenEigenspace
  have hf : ∀ μ, ∀ x ∈ f.maxGenEigenspace μ, f x ∈ f.maxGenEigenspace μ :=
    fun μ => f.mapsTo_maxGenEigenspace_of_comm (Commute.refl _) μ
  have hp : ∀ μ, Set.MapsTo (aeval f p) (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) := by
    intro μ x hx
    rw [show aeval f p x = _ from (coe_aeval_restrict f _ (hf μ) p ⟨x, hx⟩).symm]
    exact Subtype.mem _
  rw [LinearMap.trace_eq_sum_trace_restrict' hds h_fin hp]
  have h1 : ∀ μ, LinearMap.trace ℂ _ ((aeval f p).restrict (hp μ))
      = (f.charpoly.rootMultiplicity μ : ℂ) * p.eval μ := by
    intro μ
    have e : (aeval f p).restrict (hp μ) = aeval (f.restrict (hf μ)) p := by
      ext x
      rw [coe_aeval_restrict]; rfl
    have hn := f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
    have e2 : f.restrict (hf μ) - algebraMap ℂ _ μ = (f - algebraMap ℂ _ μ).restrict
        (f.mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ) := by
      ext x
      rfl
    rw [e, trace_aeval_of_isNilpotent _ μ (e2 ▸ hn), LinearMap.finrank_maxGenEigenspace_eq]
  simp_rw [h1]
  rw [Finset.sum_multiset_map_count]
  have hs : h_fin.toFinset = f.charpoly.roots.toFinset := by
    ext μ
    rw [Set.Finite.mem_toFinset, Multiset.mem_toFinset, Set.mem_setOf_eq,
      ← Multiset.count_ne_zero, count_roots, ← LinearMap.finrank_maxGenEigenspace_eq,
      Ne, Ne, Submodule.finrank_eq_zero]
  rw [hs]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [count_roots, nsmul_eq_mul]

theorem trace_aeval_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (p : ℂ[X]) :
    (aeval A p).trace = (A.charpoly.roots.map fun z => p.eval z).sum := by
  rw [← Matrix.charpoly_toLin', ← trace_aeval_end, ← Matrix.trace_toLin'_eq]
  congr 1
  exact (aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)) A p).symm

theorem trace_aeval_map {n : ℕ} {R : Type*} [CommRing R] (A : Matrix (Fin n) (Fin n) ℤ)
    (p : ℤ[X]) :
    (aeval (A.map (Int.castRingHom R)) p).trace = (((aeval A p).trace : ℤ) : R) := by
  have := aeval_algHom_apply ((Int.castRingHom R).mapMatrix (m := Fin n)).toIntAlgHom A p
  have h2 : aeval (A.map (Int.castRingHom R)) p = (aeval A p).map (Int.castRingHom R) := this
  rw [h2]
  simp [Matrix.trace]

theorem trace_aeval_int {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (p : ℤ[X]) :
    (((aeval A p).trace : ℤ) : ℂ)
      = ((A.map (Int.castRingHom ℂ)).charpoly.roots.map fun z => aeval z p).sum := by
  rw [← trace_aeval_map, ← aeval_map_algebraMap ℂ, trace_aeval_matrix]
  simp only [eval_map_algebraMap]

noncomputable def powMat {R : Type*} [CommRing R] (n : ℕ) (ψ : R[X]) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => ((X ^ ((j : ℕ) + 1)) %ₘ ψ).coeff i

open Polynomial in
open Module in
theorem _root_.GlobalTheory.TraceAeval.powMat_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (n : ℕ) {ψ : R[X]} (h : ψ.Monic) :
    (_root_.GlobalTheory.TraceAeval.powMat n ψ).map f = _root_.GlobalTheory.TraceAeval.powMat n (ψ.map f) := by
  ext i j
  simp only [_root_.GlobalTheory.TraceAeval.powMat, Matrix.map_apply, Matrix.of_apply]
  rw [← Polynomial.coeff_map, Polynomial.map_modByMonic f h, Polynomial.map_pow,
    Polynomial.map_X]

theorem charpoly_powMat {ψ : ℂ[X]} (h : ψ.Monic) : (powMat ψ.natDegree ψ).charpoly = ψ := by
  have h1 := charpoly_leftMulMatrix (AdjoinRoot.powerBasis' h)
  have h2 : minpoly ℂ (AdjoinRoot.powerBasis' h).gen = ψ := by
    rw [AdjoinRoot.powerBasis'_gen, AdjoinRoot.minpoly_root h.ne_zero, h.leadingCoeff]
    simp
  rw [h2] at h1
  refine Eq.trans ?_ h1
  congr 1
  ext i j
  refine Eq.trans ?_ (Algebra.leftMulMatrix_eq_repr_mul _ _ i j).symm
  have h3 := (AdjoinRoot.powerBasis' h).basis_eq_pow j
  refine Eq.trans ?_ (congrArg (fun t => (AdjoinRoot.powerBasis' h).basis.repr
    ((AdjoinRoot.powerBasis' h).gen * t) i) h3).symm
  simp only [← pow_succ']
  change _ = (AdjoinRoot.powerBasisAux' h).repr ((AdjoinRoot.root ψ) ^ ((j : ℕ) + 1)) i
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun, ← AdjoinRoot.mk_X, ← map_pow,
    AdjoinRoot.modByMonicHom_mk]
  rfl

theorem trace_aeval_powMat {ψ : ℤ[X]} (h : ψ.Monic) (p : ℤ[X]) :
    (((aeval (powMat ψ.natDegree ψ) p).trace : ℤ) : ℂ)
      = ((ψ.aroots ℂ).map fun z => aeval z p).sum := by
  rw [trace_aeval_int, powMat_map _ _ h, ← h.natDegree_map (Int.castRingHom ℂ),
    charpoly_powMat (h.map _)]
  rfl

theorem exists_int_trace_aeval_eq_sum_aroots :
    ∀ (χ p : Polynomial ℤ), χ.Monic → ∃ s : ℤ, (s : ℂ) = ((χ.aroots ℂ).map fun z => Polynomial.aeval z p).sum ∧ ∀ (n M : ℕ) (B : Matrix (Fin n) (Fin n) (ZMod M)), B.charpoly = χ.map (Int.castRingHom (ZMod M)) → (Polynomial.aeval B p).trace = (s : ZMod M) := by
  intro χ p hχ
  refine ⟨(aeval (powMat χ.natDegree χ) p).trace, trace_aeval_powMat hχ p, ?_⟩
  intro n M B hB
  rcases subsingleton_or_nontrivial (ZMod M) with hM | hM
  · exact Subsingleton.elim _ _
  have hn : χ.natDegree = n := by
    rw [← hχ.natDegree_map (Int.castRingHom (ZMod M)), ← hB, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  choose B₀ hB₀ using fun i j => ZMod.intCast_surjective (B i j)
  have hBB : (Matrix.of B₀).map (Int.castRingHom (ZMod M)) = B := by
    ext i j; simpa using hB₀ i j
  set A : Matrix (Fin n) (Fin n) ℤ := Matrix.of B₀
  have hA : A.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have h1 : (aeval A p).trace = (aeval (powMat n A.charpoly) p).trace := by
    have h2 := trace_aeval_powMat A.charpoly_monic p
    rw [hA] at h2
    apply Int.cast_injective (α := ℂ)
    rw [h2, trace_aeval_int, Matrix.charpoly_map]
    rfl
  rw [← hBB, trace_aeval_map, h1, hn, ← trace_aeval_map, ← trace_aeval_map,
    powMat_map _ _ hχ, powMat_map _ _ A.charpoly_monic, ← Matrix.charpoly_map, hBB, hB]

end GlobalTheory.TraceAeval
