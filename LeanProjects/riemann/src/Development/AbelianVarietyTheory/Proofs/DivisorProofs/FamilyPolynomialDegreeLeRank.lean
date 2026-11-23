import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResDeg

section Poly

variable {K : Type} [Field K]

theorem natDegree_heckePolyOf_le (n q : ℕ) (a : ℕ → K) : (Formalism.L2.Col.heckePolyOf n q a).natDegree ≤ n := by
  unfold Formalism.L2.Col.heckePolyOf
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))

theorem linear_eq (a : K) : (1 - C a * X : K[X]) = C (-a) * X + C 1 := by
  rw [C_neg, C_1]; ring

theorem linear_natDegree {a : K} (ha : a ≠ 0) : (1 - C a * X : K[X]).natDegree = 1 := by
  rw [linear_eq]; exact natDegree_linear (neg_ne_zero.2 ha)

theorem linear_ne_zero {a : K} (ha : a ≠ 0) : (1 - C a * X : K[X]) ≠ 0 := by
  intro h
  have := linear_natDegree ha
  rw [h] at this
  simp at this

theorem blockPoly_ne_zero {ν : K} {q : ℕ} (t : ℕ) (hν : ν ≠ 0) (hq : (q : K) ≠ 0) : Formalism.L2.Col.blockPoly ν q t ≠ 0 := by
  unfold Formalism.L2.Col.blockPoly
  exact Finset.prod_ne_zero_iff.2 fun c _ => linear_ne_zero (mul_ne_zero hν (pow_ne_zero _ hq))

theorem blockPoly_natDegree {ν : K} {q : ℕ} (t : ℕ) (hν : ν ≠ 0) (hq : (q : K) ≠ 0) :
    (Formalism.L2.Col.blockPoly ν q t).natDegree = t := by
  unfold Formalism.L2.Col.blockPoly
  rw [natDegree_prod _ _ fun c _ => linear_ne_zero (mul_ne_zero hν (pow_ne_zero _ hq))]
  rw [Finset.sum_congr rfl fun c _ => linear_natDegree (mul_ne_zero hν (pow_ne_zero c hq))]
  simp

theorem blocks_prod {q : ℕ} (t : ℕ) (hq : (q : K) ≠ 0) (l : List K) (hl : ∀ ν ∈ l, ν ≠ 0) :
    (l.map fun ν => Formalism.L2.Col.blockPoly ν q t).prod ≠ 0 ∧
      (l.map fun ν => Formalism.L2.Col.blockPoly ν q t).prod.natDegree = l.length * t := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := ih fun ν hν => hl ν (by simp [hν])
    have ha : a ≠ 0 := hl a (by simp)
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    refine ⟨mul_ne_zero (blockPoly_ne_zero t ha hq) h1, ?_⟩
    rw [natDegree_mul (blockPoly_ne_zero t ha hq) h1, h2, blockPoly_natDegree t ha hq]
    ring

end Poly

theorem natDegree_res_le {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) {s : ℕ} (hB : B.Ok s) {Xs : Finset (G → K)} {Sg : Pl0 → K[X]} (h : Sg ∈ B.resSet Xs) (P : B.Pl) :
    (Sg (B.pl P)).natDegree ≤ B.n - B.bl.length * B.t := by
  obtain ⟨x, hx, -⟩ := B.lf_exists_occurs_of_mem_resSet h
  by_cases h0 : Sg (B.pl P) = 0
  · simp [h0]
  have hq : ((B.q P : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (hB.q_pos P).ne'
  have hb := blocks_prod B.t hq (B.bl.map fun ν => ν P) (by
    intro a ha
    obtain ⟨ν, hν, rfl⟩ := List.mem_map.1 ha
    exact hB.blocks.ne_zero ν hν P)
  rw [List.map_map, List.length_map] at hb
  have hd : (Formalism.L2.Col.heckePoly B.n B.q x P).natDegree ≤ B.n := natDegree_heckePolyOf_le _ _ _
  have hb1 : B.blockProd P ≠ 0 := hb.1
  have hb2 : (B.blockProd P).natDegree = B.bl.length * B.t := hb.2
  rw [hx P, natDegree_mul h0 hb1, hb2] at hd
  omega

theorem natDegree_polE_le {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}
    (hA : A.fam.Ok s) (hR : R.Char F) (p : A.fam.base.Ix) (P : Pl0) (hP : P ∈ A.ok A.μ0) :
    (RealDat.polE (A := A) p.1 P).natDegree ≤ D.R.r := by
  obtain ⟨_, _, _, ht⟩ := hR.fam.tie
  have hr : A.r = D.R.r := ht.ranks.2.1
  have h1 := natDegree_res_le (A.fam.R A.fam.μ0) (hA.what₂ _)
    ((A.fam.R A.fam.μ0).lf_mem_resSet_of_mem_ixFin p.2) ⟨P, hP⟩
  have e1 : (A.fam.R A.fam.μ0).n = A.r + D.R.m * A.t := rfl
  have e2 : (A.fam.R A.fam.μ0).bl.length = D.R.m := List.length_ofFn
  have e3 : (A.fam.R A.fam.μ0).t = A.t := rfl
  rw [e1, e2, e3, Nat.add_sub_cancel, hr] at h1
  have h2 : (p.1 P).natDegree ≤ D.R.r := h1
  unfold RealDat.polE
  refine natDegree_comp_le.trans ?_
  calc _ ≤ D.R.r * 1 := Nat.mul_le_mul (natDegree_map_le.trans h2)
        ((natDegree_C_mul_le _ _).trans natDegree_X_le)
    _ = D.R.r := mul_one _

end GlobalTheory.ResDeg
