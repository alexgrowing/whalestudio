import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.FrobeniusNormBounds.ResiduePadicIntegersToIntegers

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.crystallineComparison.PinP

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem close_dvd (r : Res l K) [FiniteDimensional ℚ_[l] K] (f : ℕ) (hf : 0 < f) :
    ∃ N : ℕ, f ∣ N ∧ ∀ x : OK l K,
      ‖((okToOC l K x ^ l ^ N - PreTilt.untilt (r.s (r.ρ x)) : OC l) : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨fr, hfr, hfz⟩ := Pb.G3.res_frob r
  obtain ⟨c, hc1, hc⟩ := Pb.G3.exists_teichmuller_close r
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc 0)
  have hl : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hl) hc1
  have hN : ∀ (M : ℕ) (z : r.k), z ^ l ^ (fr * M) = z := by
    intro M z
    induction M with
    | zero => simp
    | succ M ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hfz]
  have hjN : j ≤ l ^ (fr * (f * j)) :=
    (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le.trans (Nat.pow_le_pow_right (Fact.out : l.Prime).pos
      ((Nat.le_mul_of_pos_left j hf).trans (Nat.le_mul_of_pos_left (f * j) hfr)))
  refine ⟨fr * (f * j), ⟨fr * j, by ring⟩, fun x => ?_⟩
  have ht : PreTilt.untilt (r.s (r.ρ x)) ^ l ^ (fr * (f * j)) = PreTilt.untilt (r.s (r.ρ x)) := by
    rw [← map_pow, ← map_pow, hN]
  have hp := Pb.G3.pow_close (okToOC l K x) (PreTilt.untilt (r.s (r.ρ x))) c (hc x) (fr * (f * j))
  rw [ht] at hp
  refine hp.trans (max_le le_rfl ?_)
  exact (pow_le_pow_of_le_one hc0 hc1.le hjN).trans hj.le

theorem teich_dvd (r : Res l K) [FiniteDimensional ℚ_[l] K] (f : ℕ) (hf : 0 < f) :
    ∃ N : ℕ, f ∣ N ∧ Pb.Mid.TeichmullerCongruence r N := by
  obtain ⟨N, hfN, hN⟩ := close_dvd r f hf
  refine ⟨N, hfN, fun n x => ?_⟩
  rw [Pb.Mid.phiQ_pow, Pb.G3.struct, ← Pb.G3.cong n _ _ (hN x)]
  rw [map_pow, map_pow]
  rfl

end CrystallineSemistableComparison.crystallineComparison.PinP
