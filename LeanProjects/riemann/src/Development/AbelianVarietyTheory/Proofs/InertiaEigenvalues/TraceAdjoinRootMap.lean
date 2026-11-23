import Mathlib
open Polynomial

namespace GlobalTheory

theorem adjoinRoot_map_mk_map {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) (h f : R[X]) :
    AdjoinRoot.map g h (h.map g) dvd_rfl (AdjoinRoot.mk h f) = AdjoinRoot.mk (h.map g) (f.map g) := by
  have : (AdjoinRoot.map g h (h.map g) dvd_rfl).comp (AdjoinRoot.mk h) =
      (AdjoinRoot.mk (h.map g)).comp (Polynomial.mapRingHom g) := by
    ext <;> simp
  exact DFunLike.congr_fun this f

theorem trace_adjoinRoot_map : ∀ (R S : Type) [CommRing R] [CommRing S] (g : R →+* S) (h : R[X]),
    h.Monic → ∀ x : AdjoinRoot h, g (Algebra.trace R (AdjoinRoot h) x) =
      Algebra.trace S (AdjoinRoot (h.map g)) (AdjoinRoot.map g h (h.map g) dvd_rfl x) := by
  intro R S _ _ g h hm x
  rcases subsingleton_or_nontrivial S with hS | hS
  · exact Subsingleton.elim _ _
  have hm' : (h.map g).Monic := hm.map g
  have hn : (h.map g).natDegree = h.natDegree := hm.natDegree_map g
  have key : ∀ (y : AdjoinRoot h) (k : ℕ),
      (AdjoinRoot.modByMonicHom hm' (AdjoinRoot.map g h (h.map g) dvd_rfl y)).coeff k =
        g ((AdjoinRoot.modByMonicHom hm y).coeff k) := by
    intro y k
    induction y using AdjoinRoot.induction_on with
    | ih f =>
      rw [adjoinRoot_map_mk_map, AdjoinRoot.modByMonicHom_mk, AdjoinRoot.modByMonicHom_mk,
        ← Polynomial.map_modByMonic g hm, Polynomial.coeff_map]
  let b : Module.Basis (Fin h.natDegree) R (AdjoinRoot h) := (AdjoinRoot.powerBasis' hm).basis
  let b' : Module.Basis (Fin h.natDegree) S (AdjoinRoot (h.map g)) := (AdjoinRoot.powerBasis' hm').basis.reindex (finCongr hn)
  have hb : ∀ i, b i = AdjoinRoot.root h ^ (i : ℕ) := fun i =>
    (AdjoinRoot.powerBasis' hm).basis_eq_pow i
  have hb' : ∀ i, b' i = AdjoinRoot.root (h.map g) ^ (i : ℕ) := fun i => by
    simp only [b', Module.Basis.reindex_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis'_gen]
    rfl
  have hr : ∀ (z : AdjoinRoot h) (i : Fin h.natDegree), b.repr z i = (AdjoinRoot.modByMonicHom hm z).coeff i :=
    fun _ _ => rfl
  have hr' : ∀ (z : AdjoinRoot (h.map g)) (i : Fin h.natDegree),
      b'.repr z i = (AdjoinRoot.modByMonicHom hm' z).coeff i := fun z i => by
    simp only [b', Module.Basis.repr_reindex_apply]
    rfl
  rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace b', Matrix.trace, Matrix.trace,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag]
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul]
  have hbi : b' i = AdjoinRoot.map g h (h.map g) dvd_rfl (b i) := by
    rw [hb, hb', map_pow, AdjoinRoot.map_root]
  rw [hbi, ← map_mul, hr', hr, key]

end GlobalTheory
