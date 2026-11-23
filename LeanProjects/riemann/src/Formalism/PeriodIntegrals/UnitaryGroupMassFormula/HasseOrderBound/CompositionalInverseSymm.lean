import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseOrderBound.Development
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TayInvPow

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps MvPowerSeries

namespace PI.HasseOrdBdW

section

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

def s0 : Lc X la w := algebraMap (Rp X la N) (Lc X la w) (sec X la w 0)

theorem section_mul_inverse : s0 X la w * wi X la w = 1 := section_mul_inverse_eq_one X la w

theorem hasse_apply (β : Idx D j N →₀ ℕ) (x : Lc X la w) :
    hasse X la w β x = MvPowerSeries.coeff β (tayLc X la w x) := rfl

def cS (p : Idx D j N) : Lc X la w := hasse X la w (Finsupp.single p 1) (s0 X la w)

theorem cS_eq (p : Idx D j N) : cS X la w p =
    if p.1 = 0 then algebraMap (Rp X la N) (Lc X la w) (emb X la N (X.inc wL (w p.2))) else 0 := by
  unfold cS s0
  rw [hasse_algebraMap, hasseRp_single, pdRp_sec]
  by_cases h : p.1 = 0 <;> simp [h]

theorem taySec : tayLc X la w (s0 X la w) =
    MvPowerSeries.C (s0 X la w) +
      (Finsupp.equivFunOnFinite.symm (cS X la w)).sum (fun p a => MvPowerSeries.C a * MvPowerSeries.X p) := by
  classical
  ext γ
  rw [Finsupp.sum_fintype _ _ (by intro p; simp)]
  simp only [map_add, map_sum, Finsupp.coe_equivFunOnFinite_symm, MvPowerSeries.coeff_C_mul,
    MvPowerSeries.coeff_X, MvPowerSeries.coeff_C]
  rw [← hasse_apply]
  have hne : ∀ p : Idx D j N, (0 : Idx D j N →₀ ℕ) ≠ Finsupp.single p 1 := fun p h => by
    simpa using h.symm
  by_cases h0 : γ = 0
  · subst h0
    rw [hasse_zero]
    simp [hne]
  · by_cases h1 : ∃ q, γ = Finsupp.single q 1
    · obtain ⟨q, rfl⟩ := h1
      have hq : hasse X la w (Finsupp.single q 1) (s0 X la w) = cS X la w q := rfl
      rw [hq]
      simp [Finsupp.single_left_inj one_ne_zero, h0]
    · push Not at h1
      unfold s0
      rw [hasse_algebraMap, hasseRp_sec_eq_zero X la w h0 h1 0, map_zero]
      simp [h0, h1]

end

theorem compositionalInverseSymm : S1 := by
  classical
  intro D B P j X la N wL w T β
  have hT := _root_.coeffInversePowerFacts (Idx D j N) (Lc X la w) (tayLc X la w) (s0 X la w) (wi X la w)
    (Finsupp.equivFunOnFinite.symm (cS X la w)) (section_mul_inverse X la w) (taySec X la w) T β
  rw [← hasse_apply] at hT
  have hprod : (β.prod fun p b => (Finsupp.equivFunOnFinite.symm (cS X la w)) p ^ b) =
      if (∀ i : Fin (WeightFamilies.dimY D j), ∀ k, β (i.succ, k) = 0) then
        algebraMap (Rp X la N) (Lc X la w) (∏ k, emb X la N (X.inc wL (w k)) ^ β (0, k)) else 0 := by
    rw [Finsupp.prod_fintype _ _ (by intro p; simp)]
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    rw [Fintype.prod_prod_type, Fin.prod_univ_succ]
    simp only [cS_eq, Fin.succ_ne_zero, if_false, if_true, map_prod, map_pow]
    split_ifs with h
    · simp [h]
    · push Not at h
      obtain ⟨i, k, hk⟩ := h
      apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      exact zero_pow hk
  refine ⟨if (∀ i : Fin (WeightFamilies.dimY D j), ∀ k, β (i.succ, k) = 0) then
      (-1) ^ (β.sum fun _ n => n) * (((T + (β.sum fun _ n => n) - 1).choose (β.sum fun _ n => n) : ℕ) : ℤ) *
        ((Nat.multinomial β.support β : ℕ) : ℤ) else 0, ?_, ?_⟩
  · intro hm
    split_ifs at hm with h
    · rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type, Fin.sum_univ_succ]
      simp [h]
    · exact absurd rfl hm
  · rw [hT, hprod]
    split_ifs with h
    · push_cast
      ring
    · simp

end PI.HasseOrdBdW
