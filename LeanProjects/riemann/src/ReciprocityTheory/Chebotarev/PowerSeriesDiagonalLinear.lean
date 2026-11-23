import ReciprocityTheory.Chebotarev.SplitB
import ReciprocityTheory.Chebotarev.SplitC
import ReciprocityTheory.Chebotarev.SplitE

open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem power_series_diagonal_linear : S1 := by
  intro E _ _ l _ hirr
  obtain ⟨C, hC⟩ := PE_cyclotomicField_le_mul_Pcl_add_const E l hirr
  obtain ⟨CE, hE⟩ := chebyshev_log_bounded E
  obtain ⟨CM, hM⟩ := chebyshev_log_bounded (CyclotomicField l E)
  refine ⟨CE + CM + C, ?_⟩
  have hmem : Set.Ioc (1:ℝ) 2 ∈ 𝓝[>] (1:ℝ) := Ioc_mem_nhdsGT (by norm_num)
  filter_upwards [hmem] with s hs
  have h1 := hC s hs.1
  have h2 := (abs_le.mp (hE s hs)).2
  have h3 := (abs_le.mp (hM s hs)).1
  linarith

theorem chebyshev_split_estimate : S2 := by
  intro E _ _ l _ hirr χ hχ m hm
  by_contra H
  push Not at H
  obtain ⟨E', _, _, _, k, hk, hsplit⟩ := splitE_split_ext E l hirr χ hχ
  have hlp : l.Prime := Fact.out
  have hml : m * l ≠ 0 := mul_ne_zero hm hlp.ne_zero
  apply splitC_not_almost_split E E' k hk
  refine (splitA_finite_not_coprime E (m * l) hml).subset ?_
  intro q hq
  simp only [Set.mem_ofPred_eq] at hq ⊢
  intro hcop
  apply hq
  apply hsplit q
  · intro hdvd
    have h1 : Nat.Coprime (Nrm q) l := Nat.Coprime.coprime_dvd_right (dvd_mul_left l m) hcop
    exact (Nat.Prime.coprime_iff_not_dvd hlp).1 h1.symm hdvd
  · exact H q hcop

end ReciprocityTheory.Cheb
