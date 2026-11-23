import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAtOfNe

open scoped IntermediateField Polynomial RatFunc

open GlobalTheory.Nef Polynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem ord_mul_of_ne {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) {x y : F} (hx : x ≠ 0)
    (hy : y ≠ 0) : ord v (x * y) = ord v x + ord v y := by
  simp only [ord, map_mul]
  rw [WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx) ((Valuation.ne_zero_iff _).2 hy)]
  ring

theorem ord_zpow_of_ne {k F : Type} [Field k] [Field F] [Algebra k F] (v : Place k F) {x : F} (hx : x ≠ 0)
    (m : ℤ) : ord v (x ^ m) = m * ord v x := by
  have h0 : v.1 x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  simp only [ord, map_zpow₀]
  rw [← WithZero.exp_log h0, ← WithZero.exp_zsmul, WithZero.log_exp, WithZero.log_exp, smul_eq_mul]
  ring

theorem admissible_degree_twistFamilyAtPlaceByScalar (k F : Type) [Field k] [Field F] [Algebra k F] [IsAlgClosed k] (n : ℕ)
    (h : Place k F → Matrix (Fin n) (Fin n) F) (hh : admitted h) (v₀ : Place k F) (π : F) (hπ : π ≠ 0)
    (h1 : ord v₀ π = 1) (e : ℤ) :
    admitted (twistAt v₀ (π ^ (-e)) h) ∧ deg (twistAt v₀ (π ^ (-e)) h) = deg h - n * e := by
  classical
  have hc : π ^ (-e) ≠ 0 := zpow_ne_zero _ hπ
  have hdet : ∀ v, (twistAt v₀ (π ^ (-e)) h v).det =
      (if v = v₀ then (π ^ (-e)) ^ n else 1) * (h v).det := by
    intro v
    by_cases hv : v = v₀
    · subst hv
      rw [twistAt_self, Matrix.det_smul, Fintype.card_fin, if_pos rfl]
    · rw [twistAt_of_ne _ _ _ _ hv, if_neg hv, one_mul]
  have hord : ∀ v, ord v (twistAt v₀ (π ^ (-e)) h v).det =
      ord v (h v).det - if v = v₀ then (n : ℤ) * e else 0 := by
    intro v
    rw [hdet, ord_mul_of_ne _ (by split_ifs; exacts [pow_ne_zero _ hc, one_ne_zero]) (hh.1 v)]
    split_ifs with hv
    · subst hv
      rw [← zpow_natCast, ← zpow_mul, ord_zpow_of_ne _ hπ, h1]
      ring
    · simp [ord]
  refine ⟨⟨fun v => ?_, (hh.2.union (Set.finite_singleton v₀)).subset fun v hv => ?_⟩, ?_⟩
  · rw [hdet]
    exact mul_ne_zero (by split_ifs; exacts [pow_ne_zero _ hc, one_ne_zero]) (hh.1 v)
  · by_cases hv' : v = v₀
    · exact Or.inr hv'
    · exact Or.inl (show ¬ Unimod v (h v) from fun hu => hv (by rw [twistAt_of_ne _ _ _ _ hv']; exact hu))
  · have hfin : (Function.support fun v => ord v (h v).det).Finite := by
      refine hh.2.subset fun v hv => ?_
      intro hu
      exact hv (by simp [ord, hu.2])
    have hfin' : (Function.support fun v : Place k F => if v = v₀ then (n : ℤ) * e else 0).Finite :=
      (Set.finite_singleton v₀).subset fun v hv => by
        by_contra h'
        exact hv (if_neg h')
    rw [deg, deg, finsum_congr hord, finsum_sub_distrib hfin hfin', finsum_eq_single _ v₀ fun v hv => if_neg hv, if_pos rfl]

end GlobalTheory.Nef
