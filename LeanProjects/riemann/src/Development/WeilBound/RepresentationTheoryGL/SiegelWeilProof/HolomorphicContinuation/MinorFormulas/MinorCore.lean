import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.MinorCoreA

noncomputable section

open MvPolynomial Matrix

namespace PositivityTheory.Rg.Sw.SP.Mi

variable {R : Type} [CommRing R]

def Aop (α : R) (ρ : ℕ) : Matrix (Fin ρ) (Fin ρ) (Algebra.adjoin R (gens α ρ)) :=
  fun p q => ⟨opE α p q, Algebra.subset_adjoin ⟨(p, q), rfl⟩⟩

theorem coe_det_sub (α : R) (ρ r : ℕ) (I J : Fin r → Fin ρ) :
    letI : CommRing (Algebra.adjoin R (gens α ρ)) := Algebra.adjoinCommRingOfComm R (gens_comm α ρ)
    ((((Aop α ρ).submatrix I J).det : Algebra.adjoin R (gens α ρ)) : Module.End R (Pm R ρ)) =
      ∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : R) •
        ((List.finRange r).map (fun k => opE α (I k) (J (σ k)))).prod := by
  letI : CommRing (Algebra.adjoin R (gens α ρ)) := Algebra.adjoinCommRingOfComm R (gens_comm α ρ)
  rw [← det_transpose, det_apply']
  rw [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Subalgebra.coe_mul, ← List.prod_ofFn, coe_list_prod, List.ofFn_eq_map, List.map_map]
  have hε : (((((Equiv.Perm.sign σ : ℤ) : Algebra.adjoin R (gens α ρ))) : Module.End R (Pm R ρ))) =
      ((Equiv.Perm.sign σ : ℤ) : Module.End R (Pm R ρ)) := by push_cast; rfl
  rw [hε, ← zsmul_eq_mul, ← Int.cast_smul_eq_zsmul R]
  rfl

theorem detE_eq_sum (α : R) (ρ : ℕ) :
    detE α = ∑ σ : Equiv.Perm (Fin ρ), ((Equiv.Perm.sign σ : ℤ) : R) •
      ((List.finRange ρ).map (fun k => opE α k (σ k))).prod := by
  unfold detE
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [foldr_eq_prod (fun k => opE α k (σ k))]

theorem prod_ren (α : R) {r s : ℕ} (I J : Fin r ↪ Fin s) (σ : Equiv.Perm (Fin r)) (l : List (Fin r)) (f : Pm R r) :
    (l.map (fun k => opE α (I k) (J (σ k)))).prod (ren I J f) = ren I J ((l.map (fun k => opE α k (σ k))).prod f) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih]
    exact renInt R r s I J α a (σ a) _

theorem core : Core := by
  intro R _ ρ α
  induction ρ with
  | zero =>
    rw [detE_eq_sum]
    simp [Xm]
  | succ ρ ih =>
    letI : CommRing (Algebra.adjoin R (gens α (ρ + 1))) := Algebra.adjoinCommRingOfComm R (gens_comm α (ρ + 1))
    have hfull := coe_det_sub α (ρ + 1) (ρ + 1) id id
    simp only [submatrix_id_id, id] at hfull
    rw [detE_eq_sum, ← hfull, det_succ_row_zero, AddSubmonoidClass.coe_finsetSum, LinearMap.sum_apply]
    have hsub : ∀ j : Fin (ρ + 1),
        ((((Aop α (ρ + 1)).submatrix Fin.succ j.succAbove).det : Algebra.adjoin R (gens α (ρ + 1))) :
          Module.End R (Pm R (ρ + 1))) 1 =
        C (∏ i ∈ Finset.range ρ, (α - (i : R))) * ((Xm R (ρ + 1)).submatrix j.succAbove Fin.succ).det := by
      intro j
      have h := coe_det_sub α (ρ + 1) ρ Fin.succ j.succAbove
      rw [h, LinearMap.sum_apply]
      have h1 : (1 : Pm R (ρ + 1)) = ren (Fin.succEmb ρ) (Fin.succAboveEmb j) 1 := by simp
      rw [h1]
      have h2 : ∀ σ : Equiv.Perm (Fin ρ),
          (((Equiv.Perm.sign σ : ℤ) : R) • ((List.finRange ρ).map (fun k => opE α (Fin.succ k) (j.succAbove (σ k)))).prod)
            (ren (Fin.succEmb ρ) (Fin.succAboveEmb j) 1) =
          ren (Fin.succEmb ρ) (Fin.succAboveEmb j) ((((Equiv.Perm.sign σ : ℤ) : R) •
            ((List.finRange ρ).map (fun k => opE α k (σ k))).prod) 1) := by
        intro σ
        rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
        congr 1
        exact prod_ren α (Fin.succEmb ρ) (Fin.succAboveEmb j) σ (List.finRange ρ) 1
      simp_rw [h2]
      rw [← map_sum, ← LinearMap.sum_apply, ← detE_eq_sum, ih, map_mul, AlgHom.map_det]
      congr 1
      · rw [map_prod, map_prod]
        refine Finset.prod_congr rfl fun i _ => ?_
        simp [ren]
      · congr 1
        ext p q
        simp [ren, Xm]
    have hterm : ∀ j : Fin (ρ + 1),
        ((((-1) ^ (j : ℕ) * Aop α (ρ + 1) 0 j * ((Aop α (ρ + 1)).submatrix Fin.succ j.succAbove).det :
            Algebra.adjoin R (gens α (ρ + 1))) : Module.End R (Pm R (ρ + 1))) 1) =
        C (∏ i ∈ Finset.range ρ, (α - (i : R))) * ((-1) ^ (j : ℕ) *
          (C α * X (j, 0) * ((Xm R (ρ + 1)).submatrix j.succAbove Fin.succ).det +
            del 0 j ((Xm R (ρ + 1)).submatrix j.succAbove Fin.succ).det)) := by
      intro j
      rw [Subalgebra.coe_mul, Subalgebra.coe_mul]
      push_cast
      rw [Module.End.mul_apply, Module.End.mul_apply, hsub]
      have hA : ((Aop α (ρ + 1) 0 j : Algebra.adjoin R (gens α (ρ + 1))) : Module.End R (Pm R (ρ + 1))) = opE α 0 j := rfl
      rw [hA, opE_C_mul]
      have e1 : ((-1 : Module.End R (Pm R (ρ + 1))) ^ (j : ℕ)) = ((-1 : R) ^ (j : ℕ)) • LinearMap.id := by
        rw [← Module.End.one_eq_id, ← neg_one_smul R (1 : Module.End R (Pm R (ρ + 1))), smul_pow, one_pow]
      rw [e1, LinearMap.smul_apply, LinearMap.id_apply]
      change ((-1 : R) ^ (j : ℕ)) • (C (∏ i ∈ Finset.range ρ, (α - (i : R))) *
          (C α * X (j, 0) * ((Xm R (ρ + 1)).submatrix j.succAbove Fin.succ).det +
            del 0 j ((Xm R (ρ + 1)).submatrix j.succAbove Fin.succ).det)) = _
      rw [smul_eq_C_mul, map_pow, map_neg, map_one]
      ring
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    simp_rw [mul_add, Finset.sum_add_distrib]
    have hcol := det_succ_column_zero (Xm R (ρ + 1))
    have e2 : ∑ j : Fin (ρ + 1), (-1 : Pm R (ρ + 1)) ^ (j : ℕ) * (C α * X (j, 0) *
        ((Xm R (ρ + 1)).submatrix j.succAbove Fin.succ).det) = C α * (Xm R (ρ + 1)).det := by
      rw [hcol, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Xm]
      ring
    rw [e2, sum_del, Finset.prod_range_succ]
    simp only [map_prod, map_sub, map_natCast]
    ring

theorem core_of : MComm → RenInt → Core := fun _ _ => core

end PositivityTheory.Rg.Sw.SP.Mi
