import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

namespace AddBlockData

variable {P : ArithVariety n} (D : AddBlockData P)

theorem weight_eq_mapDomain (s : Coord D.extSizes →₀ ℕ) :
    ⇑(s.mapDomain Sigma.fst) = Finsupp.weight (coordDeg D.extSizes) s := by
  funext o
  rw [Finsupp.weight_apply, Finsupp.mapDomain, Finsupp.sum, Finsupp.sum, Finsupp.finsetSum_apply,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [Finsupp.single_apply, Pi.smul_apply, coordDeg, Pi.single_apply, smul_eq_mul]
  by_cases h : v.1 = o
  · rw [if_pos h, if_pos h.symm, mul_one]
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero]

theorem extMap_monomial (s : Coord D.extSizes →₀ ℕ) (a : ℤ) :
    D.extMap (monomial s a) =
      monomial (s.mapDomain Sigma.fst) ((a : P.FunField) * s.prod fun v e ↦ D.extVal v ^ e) := by
  have hX : (s.prod fun v e ↦ (X v.1 : MvPolynomial (Option ι) P.FunField) ^ e) =
      monomial (s.mapDomain Sigma.fst) 1 := by
    rw [monomial_eq, C_1, one_mul, Finsupp.prod_mapDomain_index (fun _ ↦ pow_zero _)
      (fun _ _ _ ↦ pow_add _ _ _)]
  rw [extMap, coe_eval₂Hom, eval₂_monomial]
  simp only [mul_pow, Finsupp.prod_mul, ← map_pow]
  rw [hX, ← map_finsuppProd, eq_intCast, ← map_intCast (C : P.FunField →+* MvPolynomial (Option ι) P.FunField),
    ← mul_assoc, ← C_mul, C_mul_monomial, mul_one]

theorem extMap_component (m : Option ι → ℕ) (f : MvPolynomial (Coord D.extSizes) ℤ) :
    D.extMap (weightedHomogeneousComponent (coordDeg D.extSizes) m f) =
      monomial (Finsupp.equivFunOnFinite.symm m)
        (coeff (Finsupp.equivFunOnFinite.symm m) (D.extMap f)) := by
  induction f using MvPolynomial.induction_on' with
  | monomial s a =>
    have hh := isWeightedHomogeneous_monomial (coordDeg D.extSizes) s a rfl
    rw [weightedHomogeneousComponent_of_mem (m := m) hh, extMap_monomial, coeff_monomial]
    by_cases h : m = Finsupp.weight (coordDeg D.extSizes) s
    · have h' : s.mapDomain Sigma.fst = Finsupp.equivFunOnFinite.symm m := by
        apply DFunLike.coe_injective
        rw [Finsupp.coe_equivFunOnFinite_symm, h, weight_eq_mapDomain]
      rw [if_pos h, if_pos h', extMap_monomial, h']
    · have h' : s.mapDomain Sigma.fst ≠ Finsupp.equivFunOnFinite.symm m := by
        intro e
        apply h
        rw [← weight_eq_mapDomain, e]
        rfl
      rw [if_neg h, if_neg h', map_zero, monomial_zero]
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, map_add, coeff_add, map_add]

end AddBlockData

theorem ChartPrimality.proof : ChartPrimality.Statement := by
  intro ι _ _ n P D
  refine ⟨{ ideal := D.extIdeal, isPrime := ?_, homogeneous := ?_, relevant := ?_, horizontal := ?_ }, rfl⟩
  · exact RingHom.ker_isPrime _
  · intro f hf m
    rw [AddBlockData.extIdeal, RingHom.mem_ker] at hf ⊢
    rw [D.extMap_component, hf, coeff_zero, monomial_zero]
  · rintro (_ | k)
    · obtain ⟨c, hc⟩ := P.exists_chart
      obtain ⟨u, -, hu⟩ := D.generating c hc
      have hj : ∃ j, D.elt j ≠ 0 := by
        by_contra h
        push Not at h
        simp [h] at hu
      obtain ⟨j, hj⟩ := hj
      refine ⟨j, fun hmem ↦ hj ?_⟩
      rw [AddBlockData.extIdeal, RingHom.mem_ker, AddBlockData.extMap, eval₂Hom_X'] at hmem
      exact (mul_eq_zero.mp hmem).resolve_right (X_ne_zero _) |> C_eq_zero.mp
    · obtain ⟨i, hi⟩ := P.relevant k
      refine ⟨i, fun hmem ↦ hi ?_⟩
      rw [AddBlockData.extIdeal, RingHom.mem_ker, AddBlockData.extMap, eval₂Hom_X'] at hmem
      rw [← P.mkF_eq_zero_iff]
      exact (mul_eq_zero.mp hmem).resolve_right (X_ne_zero _) |> C_eq_zero.mp
  · intro a ha
    rw [AddBlockData.extIdeal, RingHom.mem_ker, AddBlockData.extMap, eval₂Hom_C, eq_intCast] at ha
    have h2 : (a : P.FunField) = 0 := by rw [← C_eq_zero, map_intCast]; exact ha
    have h3 : algebraMap P.CoordRing P.FunField (a : P.CoordRing) = 0 := by rw [map_intCast]; exact h2
    rw [(IsFractionRing.injective P.CoordRing P.FunField).eq_iff' (map_zero _)] at h3
    exact_mod_cast h3

end

end GroundTheory.Heights₂.Heights
