import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Vanish

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps Finset.HasAntidiagonal

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem algebraMap_Op_mul {N : ℕ} (la : HeightOneSpectrum (𝓞 B.KO)) (w : Fin N → B.Cusp j wL) (a : Op X la N)
    (y : Lw X la w) :
    algebraMap (Rp X la N) (Lw X la w) (algebraMap (Op X la N) (Rp X la N) a) * y =
      algebraMap (Op X la N) (Kp X la N) a • y := by
  rw [algebraMap_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply (Op X la N) (Rp X la N) (Lw X la w)]

theorem restricted_derivative_linear (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : LinOp G la := by
  intro k β r x hx hβ
  have hP := hasse_preserves_kernel G la
  set c := algebraMap (Op X la G.N) (Kp X la G.N) r with hc
  have h1 : hasse X la G.w β ((c • x : ↥(HK X la G.w wF)) : Lw X la G.w) ∈ HK X la G.w wF := hP β _ (c • x).2
  have h2 : hasse X la G.w β (x : Lw X la G.w) ∈ HK X la G.w wF := hP β _ x.2
  unfold rD
  rw [dif_pos h1, dif_pos h2]
  show _ = c • toA0K X la G.w wF ⟨_, h2⟩
  rw [← LinearMap.map_smul_of_tower, ← sub_eq_zero, ← map_sub]
  refine leading_coeff_eq_zero_of_jet la G.w _ ?_
  have hA : ∀ (q : Idx D j G.N →₀ ℕ) (a : Op X la G.N), PI.HJP.H X la G.w q
      (algebraMap (Rp X la G.N) (Lw X la G.w) (algebraMap (Op X la G.N) (Rp X la G.N) a)) =
      algebraMap (Rp X la G.N) (Lw X la G.w) (algebraMap (Op X la G.N) (Rp X la G.N) (hasseOp X la G.N q a)) :=
    fun q a => hasse_algebraMap_Op X la G.w q a
  have e0 : ((c • x : ↥(HK X la G.w wF)) : Lw X la G.w) =
      algebraMap (Rp X la G.N) (Lw X la G.w) (algebraMap (Op X la G.N) (Rp X la G.N) r) * (x : Lw X la G.w) :=
    (algebraMap_Op_mul la G.w r x).symm
  show PI.HJP.H X la G.w β ((c • x : ↥(HK X la G.w wF)) : Lw X la G.w) -
    c • PI.HJP.H X la G.w β (x : Lw X la G.w) ∈ JHfr X la G.w wF 1
  rw [e0, PI.HJP.H_mul]
  simp only [hA, algebraMap_Op_mul la G.w]
  have hmem : ((0 : Idx D j G.N →₀ ℕ), β) ∈ antidiagonal β := by simp
  rw [← Finset.add_sum_erase _ _ hmem, hasseOp_zero, add_sub_cancel_left]
  refine Submodule.sum_mem _ fun q hq => ?_
  obtain ⟨hne, hq⟩ := Finset.mem_erase.1 hq
  rw [mem_antidiagonal] at hq
  have hq1 : q.1 ≠ 0 := by
    rintro h0
    apply hne
    ext1
    · exact h0
    · simpa [h0] using hq
  have hdeg : Finsupp.degree q.2 < k := by
    have e1 : Finsupp.degree β = Finsupp.degree q.1 + Finsupp.degree q.2 := by rw [← hq, map_add]
    have e2 : Finsupp.degree q.1 ≠ 0 := fun h => hq1 ((Finsupp.degree_eq_zero_iff q.1).1 h)
    rw [PI.HJP.sum_eq_degree] at hβ
    omega
  refine Submodule.smul_mem _ _ ?_
  show hasse X la G.w q.2 (x : Lw X la G.w) ∈ _
  have h3 := hasse_jid_power X la G.w wF q.2 k _ ((mem_pow_smul_top_iff la G.w).1 hx)
  rw [PI.HJP.sum_eq_degree] at h3
  exact PI.HJP.JHfr_anti X la G.w wF (by omega) h3

end PI.PoleLengthCount
