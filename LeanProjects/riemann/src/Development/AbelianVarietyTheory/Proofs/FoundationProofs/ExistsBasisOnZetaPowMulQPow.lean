import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne

noncomputable section
open Polynomial
namespace GlobalTheory.K5.OnFree

section General

variable {R : Type*} [CommRing R] (f : R[X]) (m : ℕ) (c : R)

abbrev relIdeal : Ideal R[X][X] := Ideal.span {C f, X ^ m - C (C c)}

abbrev topPoly : (AdjoinRoot f)[X] := X ^ m - C (algebraMap R (AdjoinRoot f) c)

def toAdj : (R[X][X] ⧸ relIdeal f m c) →ₐ[R] AdjoinRoot (topPoly f m c) :=
  Ideal.Quotient.liftₐ (relIdeal f m c)
    (Polynomial.eval₂AlgHom
      (Polynomial.aeval (AdjoinRoot.of (topPoly f m c) (AdjoinRoot.root f)))
      (AdjoinRoot.root (topPoly f m c)) (fun _ => Commute.all _ _)) (by
      have h : relIdeal f m c ≤ RingHom.ker (Polynomial.eval₂AlgHom
          (Polynomial.aeval (R := R) (AdjoinRoot.of (topPoly f m c) (AdjoinRoot.root f)))
          (AdjoinRoot.root (topPoly f m c)) (fun _ => Commute.all _ _)) := by
        rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        constructor
        · have h1 : aeval (AdjoinRoot.of (topPoly f m c) (AdjoinRoot.root f)) f = 0 := by
            rw [← AdjoinRoot.algebraMap_eq, aeval_algebraMap_apply, AdjoinRoot.aeval_eq,
              AdjoinRoot.mk_self, map_zero]
          simpa [RingHom.mem_ker] using h1
        · have h2 := AdjoinRoot.eval₂_root (topPoly f m c)
          simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h2
          simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_pow]
          change eval₂ _ _ X ^ m - eval₂ _ _ (C (C c)) = 0
          rw [eval₂_X, eval₂_C, RingHom.coe_coe, aeval_C,
            IsScalarTower.algebraMap_apply R (AdjoinRoot f)]
          exact h2
      exact fun a ha => h ha)

def baseToQuot : AdjoinRoot f →ₐ[R] (R[X][X] ⧸ relIdeal f m c) :=
  AdjoinRoot.liftAlgHom f (Algebra.ofId R _) (Ideal.Quotient.mk (relIdeal f m c) (C X)) (by
    have h : (Ideal.Quotient.mkₐ R (relIdeal f m c)) (C f) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp))
    have h2 : aeval ((Ideal.Quotient.mkₐ R (relIdeal f m c)) (CAlgHom (R := R) (X : R[X]))) f = 0 := by
      rw [aeval_algHom_apply, aeval_algHom_apply, aeval_X_left_apply]
      exact h
    exact h2)

def toQuot : AdjoinRoot (topPoly f m c) →ₐ[R] (R[X][X] ⧸ relIdeal f m c) :=
  AdjoinRoot.liftAlgHom (topPoly f m c) (baseToQuot f m c)
    (Ideal.Quotient.mk (relIdeal f m c) X) (by
    have h : (Ideal.Quotient.mk (relIdeal f m c)) (X ^ m - C (C c)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp))
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, RingHom.coe_coe, AlgHom.commutes]
    rw [map_sub, map_pow] at h
    exact h)

theorem toQuot_root : toQuot f m c (AdjoinRoot.root _) = Ideal.Quotient.mk (relIdeal f m c) X := by
  simp [toQuot]

theorem toQuot_of_root : toQuot f m c (AdjoinRoot.of _ (AdjoinRoot.root f)) =
    Ideal.Quotient.mk (relIdeal f m c) (C X) := by
  have h : baseToQuot f m c (AdjoinRoot.root f) = Ideal.Quotient.mk (relIdeal f m c) (C X) :=
    AdjoinRoot.liftAlgHom_root _ _ _ _
  rw [← h]
  simp [toQuot]

theorem toAdj_X : toAdj f m c (Ideal.Quotient.mk (relIdeal f m c) X) = AdjoinRoot.root _ := by
  change eval₂ _ _ X = _
  rw [eval₂_X]

theorem toAdj_C_X : toAdj f m c (Ideal.Quotient.mk (relIdeal f m c) (C X)) =
    AdjoinRoot.of _ (AdjoinRoot.root f) := by
  change eval₂ _ _ (C X) = _
  rw [eval₂_C, RingHom.coe_coe, aeval_X]

def adjEquiv : AdjoinRoot (topPoly f m c) ≃ₐ[R] (R[X][X] ⧸ relIdeal f m c) :=
  AlgEquiv.ofAlgHom (toQuot f m c) (toAdj f m c)
    (by
      refine Ideal.Quotient.algHom_ext R ?_
      refine Polynomial.algHom_ext' ?_ ?_
      · refine Polynomial.algHom_ext ?_
        have := toQuot_of_root f m c
        rw [← toAdj_C_X] at this
        exact this
      · have := toQuot_root f m c
        rw [← toAdj_X] at this
        exact this)
    (by
      refine AdjoinRoot.algHom_ext' ?_ ?_
      · refine AdjoinRoot.algHom_ext ?_
        have := toAdj_C_X f m c
        rw [← toQuot_of_root] at this
        exact this
      · have := toAdj_X f m c
        rw [← toQuot_root] at this
        exact this)

theorem exists_basis [Nontrivial R] (hf : f.Monic) (d : ℕ) (hd : f.natDegree = d) (hd0 : 0 < d)
    (hm : m ≠ 0) :
    ∃ b : Module.Basis (Fin d × Fin m) R (R[X][X] ⧸ relIdeal f m c),
      ∀ i j, b (i, j) = (Ideal.Quotient.mk (relIdeal f m c) (C X)) ^ (i : ℕ) *
        (Ideal.Quotient.mk (relIdeal f m c) X) ^ (j : ℕ) := by
  let b₁ : Module.Basis (Fin d) R (AdjoinRoot f) :=
    (AdjoinRoot.powerBasis' hf).basis.reindex (finCongr hd)
  have hb₁ : ∀ i, b₁ i = AdjoinRoot.root f ^ (i : ℕ) := by
    intro i
    simp only [b₁, Module.Basis.reindex_apply, PowerBasis.coe_basis]
    rfl
  haveI : Nontrivial (AdjoinRoot f) := nontrivial_of_ne _ _ (b₁.ne_zero ⟨0, hd0⟩)
  have hg : (topPoly f m c).Monic := monic_X_pow_sub_C _ hm
  have hgd : (topPoly f m c).natDegree = m := natDegree_X_pow_sub_C
  let b₂ : Module.Basis (Fin m) (AdjoinRoot f) (AdjoinRoot (topPoly f m c)) :=
    (AdjoinRoot.powerBasis' hg).basis.reindex (finCongr hgd)
  have hb₂ : ∀ j, b₂ j = AdjoinRoot.root (topPoly f m c) ^ (j : ℕ) := by
    intro j
    simp only [b₂, Module.Basis.reindex_apply, PowerBasis.coe_basis]
    rfl
  refine ⟨(b₁.smulTower b₂).map (adjEquiv f m c).toLinearEquiv, fun i j => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.smulTower_apply, hb₁, hb₂, Algebra.smul_def,
    AdjoinRoot.algebraMap_eq, ← toQuot_of_root, ← toQuot_root, ← map_pow (toQuot f m c),
    ← map_pow (toQuot f m c), ← map_mul, map_pow]
  rfl

end General

theorem on_free (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    ∃ b : Module.Basis (Fin (Nat.totient (p ^ n)) × Fin (p ^ n)) (O0 p) (On p n),
      ∀ i j, b (i, j) = xn p n ^ (i : ℕ) * yn p n ^ (j : ℕ) := by
  rcases subsingleton_or_nontrivial (O0 p) with h | h
  · haveI : Subsingleton (On p n) := Module.subsingleton (O0 p) _
    exact ⟨Module.Basis.ofRepr (LinearEquiv.ofSubsingleton _ _), fun _ _ => Subsingleton.elim _ _⟩
  · have hpos : 0 < p ^ n := pow_pos hp.out.pos n
    exact exists_basis (cyclotomic (p ^ n) (O0 p)) (p ^ n) (qO p) (cyclotomic.monic _ _) _
      (natDegree_cyclotomic _ _) (Nat.totient_pos.2 hpos) hpos.ne'

end GlobalTheory.K5.OnFree
