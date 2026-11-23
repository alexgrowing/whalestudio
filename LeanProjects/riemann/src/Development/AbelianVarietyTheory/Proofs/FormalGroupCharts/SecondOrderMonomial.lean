import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SumSplitsEvalTwoWord

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.HalfIdentity

variable {k : Type} [CommRing k] {d : ℕ}

section

variable (F : Fin d → PS k 2 d) {ι : Type} (u : ι → Fin d → k)

theorem T_replicate (n : ℕ) (l : ι) (f : PS k 1 d) :
    G2.T F u (List.replicate n l) f = (Dof F (u l))^[n] f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, G2.T_cons, ih, Function.iterate_succ_apply']

theorem foldr_eq_T_word (L : List ι) (m : ι →₀ ℕ) (f : PS k 1 d) :
    L.foldr (fun l g => (Dof F (u l))^[m l] g) f = G2.T F u (G2.word L m) f := by
  induction L with
  | nil => rfl
  | cons l L ih => rw [List.foldr_cons, ih, G2.word_cons, G2.T_append, T_replicate]

variable [Fintype ι]

theorem dmonOf_eq_T_word (m : ι →₀ ℕ) (f : PS k 1 d) :
    DmonOf F u m f = G2.T F u (G2.word (Finset.univ : Finset ι).toList m) f :=
  foldr_eq_T_word F u _ m f

theorem dpolyOf_monomial (m : ι →₀ ℕ) (a : k) (f : PS k 1 d) :
    DpolyOf F u (MvPolynomial.monomial m a) f = C a * DmonOf F u m f := by
  classical
  rw [GE.dpolyOf_eq_sum_of_subset F u _ {m} MvPolynomial.support_monomial_subset,
    Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

theorem secondOrder_add (c : ι → ι → k) (P Q : MvPolynomial ι k) :
    secondOrder k c (P + Q) = secondOrder k c P + secondOrder k c Q := by
  simp only [secondOrder, map_add, mul_add, Finset.sum_add_distrib]

theorem secondOrder_monomial (c : ι → ι → k) (m : ι →₀ ℕ) (a : k) :
    secondOrder k c (MvPolynomial.monomial m a) =
      ∑ x, ∑ y, MvPolynomial.monomial (m - Finsupp.single y 1 - Finsupp.single x 1)
        (a * (c x y * ((m y * (m - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : k))) := by
  unfold secondOrder
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [MvPolynomial.pderiv_monomial, MvPolynomial.pderiv_monomial, MvPolynomial.C_mul_monomial]
  congr 1
  push_cast
  ring

end

theorem halfSt : GE.HalfSt := by
  intro k _ _ d F ι _ u c q hc hq0 hq1 hq2 P A
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
    rw [secondOrder_add, GE.dpolyOf_add_P, GE.dpolyOf_add_P, map_add, map_add, hP, hQ, mul_add]
  | monomial m a =>
    have h2 : algebraMap ℚ k (1 / 2) * 2 = 1 := by
      rw [show (2 : k) = algebraMap ℚ k 2 from (map_ofNat _ 2).symm, ← map_mul]
      norm_num
    have key := G2.sum_splits_evalTwo_word c hc (Finset.univ : Finset ι).toList (Finset.nodup_toList _) m
      (fun w => constantCoeff (G2.T F u w A))
    simp only [Finset.sum_map_toList] at key
    rw [dpolyOf_monomial, dmonOf_eq_T_word, map_mul, constantCoeff_C,
      G2.cc_T_mul_q c F u q hq0 hq1 hq2, secondOrder_monomial, GE.dpolyOf_sum_P, map_sum]
    have hR : ∑ x, constantCoeff (DpolyOf F u
        (∑ y, MvPolynomial.monomial (m - Finsupp.single y 1 - Finsupp.single x 1)
          (a * (c x y * ((m y * (m - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : k)))) A) =
        a * ∑ x, ∑ y, c x y * ((m y * (m - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : k) *
          constantCoeff (G2.T F u (G2.word (Finset.univ : Finset ι).toList
            (m - Finsupp.single y 1 - Finsupp.single x 1)) A) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [GE.dpolyOf_sum_P, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [dpolyOf_monomial, dmonOf_eq_T_word, map_mul, constantCoeff_C, mul_assoc]
    rw [hR, ← key]
    linear_combination (-(a * ((G2.splits (G2.word (Finset.univ : Finset ι).toList m)).map
      (fun p => constantCoeff (G2.T F u p.1 A) * G2.ev2 c p.2)).sum)) * h2

end GlobalTheory.HalfIdentity
