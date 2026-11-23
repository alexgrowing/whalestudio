import Formalism.PeriodIntegrals.HassePresH

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.Gaps.EtaleWeightGaps Finset.HasAntidiagonal

namespace PI.UnitaryGroupMassFormula.HassePresH

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
  (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

theorem hasse_frac_eq (β : Idx D j N →₀ ℕ) (K : ℕ) (G : Rp X la N) (y : Lw X la w)
    (hy : y = frac X la w K G) :
    @id (Lw X la w) (hasse X la w β y) = frac X la w K (hasseRp X la N β G) -
      ∑ q ∈ (antidiagonal β).erase (0, β),
        frac X la w K (hasseRp X la N q.1 (sec X la w 0 ^ K)) * @id (Lw X la w) (hasse X la w q.2 y) := by
  have hinv : algebraMap (Rp X la N) (Lw X la w) (sec X la w 0 ^ K) * w0inv X la w ^ K = 1 := by
    rw [map_pow, ← mul_pow, section_mul_inverse_eq_one, one_pow]
  have hsy : algebraMap (Rp X la N) (Lw X la w) (sec X la w 0 ^ K) * y =
      algebraMap (Rp X la N) (Lw X la w) G := by
    rw [hy, frac_apply]
    linear_combination (algebraMap (Rp X la N) (Lw X la w) G) * hinv
  have H := hasse_of_mul_eq X la w β hsy
  have H' : ∑ q ∈ antidiagonal β, algebraMap (Rp X la N) (Lw X la w) (hasseRp X la N q.1 (sec X la w 0 ^ K)) *
      @id (Lw X la w) (hasse X la w q.2 y) = algebraMap (Rp X la N) (Lw X la w) (hasseRp X la N β G) := H
  have hmem : ((0 : Idx D j N →₀ ℕ), β) ∈ antidiagonal β := by simp [mem_antidiagonal]
  rw [← Finset.add_sum_erase _ _ hmem] at H'
  have h0 : hasseRp X la N 0 (sec X la w 0 ^ K) = sec X la w 0 ^ K := hasseRp_zero X la _
  rw [h0] at H'
  have hsum : ∑ q ∈ (antidiagonal β).erase (0, β),
        frac X la w K (hasseRp X la N q.1 (sec X la w 0 ^ K)) * @id (Lw X la w) (hasse X la w q.2 y) =
      w0inv X la w ^ K * ∑ q ∈ (antidiagonal β).erase (0, β),
        algebraMap (Rp X la N) (Lw X la w) (hasseRp X la N q.1 (sec X la w 0 ^ K)) *
          @id (Lw X la w) (hasse X la w q.2 y) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [frac_apply]
    ring
  rw [hsum, frac_apply]
  linear_combination (w0inv X la w ^ K) * H' - @id (Lw X la w) (hasse X la w β y) * hinv

theorem hasse_mem_Hfr (u : WeightFamilies.Wt D j) (β : Idx D j N →₀ ℕ) :
    ∀ y : Lw X la w, y ∈ Hfr X la w u → hasse X la w β y ∈ Hfr X la w u := by
  induction β using WellFoundedLT.induction with
  | ind β ih =>
  intro y hy
  obtain ⟨k, g, hg, rfl⟩ := (mem_Hfr X la w).mp hy
  have hG : sec X la w 0 ^ 1 * g ∈ Vw X la N (addL u wL (k + 1)) := sec_pow_mul_mem X la w 0 u k 1 hg
  have hs : sec X la w 0 ^ (k + 1) ∈ Vw X la N (addL (wt0 D j) wL (k + 1)) := by
    rw [pow_succ, Nat.add_comm k 1]
    exact sec_pow_mul_mem X la w 0 (wt0 D j) 1 k (by rw [add_zero_weight_one_eq]; exact sec_mem_Vw X la w 0)
  have E := hasse_frac_eq X la w β (k + 1) (sec X la w 0 ^ 1 * g) (frac X la w k g)
    (frac_pow_mul X la w k 1 g).symm
  refine (congrArg (fun z : Lw X la w => z ∈ Hfr X la w u) E).mpr ?_
  refine Submodule.sub_mem _ (frac_mem_Hfr X la w (hasseRp_mem_Vw X la hG β))
    (Submodule.sum_mem _ fun q hq => ?_)
  obtain ⟨hne, hq⟩ := Finset.mem_erase.mp hq
  rw [mem_antidiagonal] at hq
  have h1 : q.1 ≠ 0 := by
    intro h0
    exact hne (Prod.ext h0 (by rw [← hq, h0, zero_add]))
  have hlt : q.2 < β := by
    refine lt_of_le_of_ne (le_add_self.trans_eq hq) fun e => h1 ?_
    rw [e] at hq
    simpa using hq
  have hm := mul_mem_Hfr X la w (frac_mem_Hfr X la w (hasseRp_mem_Vw X la hs q.1)) (ih q.2 hlt _ hy)
  exact (congrArg (Hfr X la w) (zero_weight_add u)).le hm

theorem main : PI.HassePresH := by
  intro D B P j X la N wL w u β x hx
  exact hasse_mem_Hfr X la w u β x hx

end PI.UnitaryGroupMassFormula.HassePresH
