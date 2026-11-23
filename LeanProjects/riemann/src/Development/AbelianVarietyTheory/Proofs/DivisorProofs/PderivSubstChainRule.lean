import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace GlobalTheory.PSChain

open scoped MvPowerSeries.WithPiTopology in

theorem continuous_pderiv_discrete {σ R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    (i : σ) : Continuous (fun f : MvPowerSeries σ R => pderiv R i f) := by
  classical
  apply continuous_pi
  intro n
  have e : (fun f : MvPowerSeries σ R => (pderiv R i f) n) =
      (fun r : R => r * (n i + 1)) ∘ (fun f : MvPowerSeries σ R => coeff (n + Finsupp.single i 1) f) := by
    funext f
    exact coeff_pderiv f n
  rw [e]
  exact continuous_of_discreteTopology.comp (MvPowerSeries.WithPiTopology.continuous_coeff R _)

open scoped MvPowerSeries.WithPiTopology in

theorem pderiv_subst_chain {R σ τ : Type} [CommRing R] [Fintype σ] [Fintype τ]
    (a : σ → MvPowerSeries τ R) (ha0 : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) (k : τ) :
    pderiv R k (subst a f) = ∑ j, subst a (pderiv R j f) * pderiv R k (a j) := by
  classical
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  let _ : UniformSpace R := ⊥
  have _ : DiscreteUniformity R := ⟨rfl⟩
  have hcs : Continuous (subst a : MvPowerSeries σ R → MvPowerSeries τ R) := continuous_subst ha
  have hs0 : subst a (0 : MvPowerSeries σ R) = 0 := by rw [← coe_substAlgHom ha, map_zero]
  have hs1 : subst a (1 : MvPowerSeries σ R) = 1 := by rw [← coe_substAlgHom ha, map_one]
  let D1 : MvPowerSeries σ R → MvPowerSeries τ R := fun g => pderiv R k (subst a g)
  let D2 : MvPowerSeries σ R → MvPowerSeries τ R := fun g =>
    ∑ s, subst a (pderiv R s g) * pderiv R k (a s)
  have c1 : Continuous D1 := (continuous_pderiv_discrete _).comp hcs
  have c2 : Continuous D2 :=
    continuous_finsetSum _ fun i _ => (hcs.comp (continuous_pderiv_discrete _)).mul continuous_const
  have hpoly : ∀ p : MvPolynomial σ R, D1 (p : MvPowerSeries σ R) = D2 (p : MvPowerSeries σ R) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r => simp [D1, D2, subst_C, hs0]
    | add p q hp hq =>
      simp only [D1, D2, MvPolynomial.coe_add, subst_add ha, map_add] at hp hq ⊢
      rw [hp, hq, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    | mul_X p s2 hp =>
      simp only [D1, D2, MvPolynomial.coe_mul, MvPolynomial.coe_X] at hp ⊢
      rw [subst_mul ha, subst_X ha, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hp]
      have hX : ∀ i : σ, pderiv R i (X s2 : MvPowerSeries σ R) = if i = s2 then 1 else 0 := by
        intro i
        by_cases h : i = s2
        · subst h; simp
        · rw [if_neg h, pderiv_X_of_ne (Ne.symm h)]
      have hterm : ∀ i : σ, subst a (pderiv R i ((p : MvPowerSeries σ R) * X s2)) * pderiv R k (a i) =
          (if i = s2 then subst a (p : MvPowerSeries σ R) * pderiv R k (a i) else 0) +
            a s2 * (subst a (pderiv R i (p : MvPowerSeries σ R)) * pderiv R k (a i)) := by
        intro i
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hX i, subst_add ha, subst_mul ha,
          subst_mul ha, subst_X ha]
        split_ifs with h
        · rw [hs1]; ring
        · rw [hs0]; ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, Finset.sum_ite_eq',
        if_pos (Finset.mem_univ _), ← Finset.mul_sum]
  have := (MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries).equalizer c1 c2 (funext hpoly)
  exact congrFun this f

end GlobalTheory.PSChain
