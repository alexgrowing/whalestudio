import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts

noncomputable section

namespace Formalism.MainNotions.DIV.Inh

open Formalism.MainNotions.ModuliIntegralCharts

def cfPadic (p : ℕ) [Fact p.Prime] : CF p where
  C := PadicComplex p
  norm_p := by
    have h1 : ((p : ℕ) : PadicComplex p) = ((((p : ℕ) : PadicAlgCl p)) : PadicComplex p) := by
      simp
    have h2 : ((p : ℕ) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (p : ℚ_[p]) := by
      simp
    rw [h1, PadicComplex.norm_extends, h2, PadicAlgCl.norm_extends, Padic.norm_p]

theorem nonempty_coefficient_field_prime (p : ℕ) (hp : p.Prime) : Nonempty (CF p) :=
  haveI : Fact p.Prime := ⟨hp⟩
  ⟨cfPadic p⟩

section Resc

variable (K : Type) [NormedField K] [IsUltrametricDist K] (s : ℝ) (hs : 0 < s)

def rescAbs : AbsoluteValue K ℝ where
  toFun x := ‖x‖ ^ s
  map_mul' x y := by rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  nonneg' x := Real.rpow_nonneg (norm_nonneg _) _
  eq_zero' x := by rw [Real.rpow_eq_zero (norm_nonneg _) hs.ne', norm_eq_zero]
  add_le' x y := by
    have h := IsUltrametricDist.norm_add_le_max x y
    calc ‖x + y‖ ^ s ≤ (max ‖x‖ ‖y‖) ^ s := Real.rpow_le_rpow (norm_nonneg _) h hs.le
      _ ≤ ‖x‖ ^ s + ‖y‖ ^ s := by
        rcases le_total ‖x‖ ‖y‖ with h | h
        · rw [max_eq_right h]; exact le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)
        · rw [max_eq_left h]; exact le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _)

theorem resc_norm (x : WithAbs (rescAbs K s hs)) : ‖x‖ = ‖x.ofAbs‖ ^ s := rfl

theorem resc_dist (x y : WithAbs (rescAbs K s hs)) : dist x y = ‖x.ofAbs - y.ofAbs‖ ^ s := by
  rw [dist_eq_norm, resc_norm]; rfl

theorem resc_ultra : IsUltrametricDist (WithAbs (rescAbs K s hs)) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm (fun x y => by
    have h := IsUltrametricDist.norm_add_le_max x.ofAbs y.ofAbs
    rw [resc_norm, resc_norm, resc_norm]
    have h2 : ‖(x + y).ofAbs‖ ^ s ≤ (max ‖x.ofAbs‖ ‖y.ofAbs‖) ^ s :=
      Real.rpow_le_rpow (norm_nonneg _) h hs.le
    refine h2.trans ?_
    rcases le_total ‖x.ofAbs‖ ‖y.ofAbs‖ with h | h
    · rw [max_eq_right h]; exact le_max_right _ _
    · rw [max_eq_left h]; exact le_max_left _ _)

theorem resc_complete [CompleteSpace K] : CompleteSpace (WithAbs (rescAbs K s hs)) := by
  refine Metric.complete_of_cauchySeq_tendsto (fun u hu => ?_)
  have hc : CauchySeq (fun n => (u n).ofAbs) := by
    rw [Metric.cauchySeq_iff] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu (ε ^ s) (Real.rpow_pos_of_pos hε s)
    refine ⟨N, fun m hm n hn => ?_⟩
    have := hN m hm n hn
    rw [resc_dist] at this
    rw [dist_eq_norm]
    exact (Real.rpow_lt_rpow_iff (norm_nonneg _) hε.le hs).1 this
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨WithAbs.toAbs _ a, ?_⟩
  rw [Metric.tendsto_atTop] at ha ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := ha (ε ^ (1 / s)) (Real.rpow_pos_of_pos hε _)
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  rw [dist_eq_norm] at this
  rw [resc_dist]
  have h2 := Real.rpow_lt_rpow (norm_nonneg _) this hs
  rwa [← Real.rpow_mul hε.le, one_div, inv_mul_cancel₀ hs.ne', Real.rpow_one] at h2

end Resc

theorem cf_of_norm_lt_one (K : Type) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] [CompleteSpace K]
    [CharZero K] (p : ℕ) (hp : 2 ≤ p) (h1 : ‖(p : K)‖ < 1) : Nonempty (CF p) := by
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have ht : 0 < ‖(p : K)‖ := norm_pos_iff.2 hp0
  have hlt : Real.log ‖(p : K)‖ < 0 := Real.log_neg ht h1
  have hpR : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hlp : 0 < Real.log p := Real.log_pos hpR
  set s : ℝ := Real.log p / (-Real.log ‖(p : K)‖) with hsdef
  have hs : 0 < s := div_pos hlp (by linarith)
  have hnp : ‖((p : ℕ) : WithAbs (rescAbs K s hs))‖ = (p : ℝ)⁻¹ := by
    have e : ((p : ℕ) : WithAbs (rescAbs K s hs)).ofAbs = (p : K) :=
      map_natCast (WithAbs.equiv (rescAbs K s hs)) p
    rw [resc_norm, e, Real.rpow_def_of_pos ht, ← Real.exp_log (inv_pos.2 (by linarith : (0 : ℝ) < p)),
      Real.log_inv, hsdef]
    congr 1
    have hne : Real.log ‖(p : K)‖ ≠ 0 := hlt.ne
    field_simp
  let iN : NontriviallyNormedField (WithAbs (rescAbs K s hs)) :=
    NontriviallyNormedField.ofNormNeOne ⟨((p : ℕ) : WithAbs (rescAbs K s hs)), by
      intro h
      have : ((p : ℕ) : WithAbs (rescAbs K s hs)).ofAbs = (p : K) :=
        map_natCast (WithAbs.equiv (rescAbs K s hs)) p
      rw [h] at this
      exact hp0 this.symm, by
      rw [hnp]
      intro h
      have : (p : ℝ) = 1 := by
        have := congrArg (·⁻¹) h
        simpa using this
      linarith⟩
  exact ⟨{ C := WithAbs (rescAbs K s hs)
           fld := iN
           ultra := resc_ultra K s hs
           ac := IsAlgClosed.of_ringEquiv K _ (WithAbs.equiv (rescAbs K s hs)).symm
           cpl := resc_complete K s hs
           ch0 := (RingHom.charZero_iff (ϕ := (WithAbs.equiv (rescAbs K s hs)).symm.toRingHom)
             (WithAbs.equiv (rescAbs K s hs)).symm.injective).1 inferInstance
           norm_p := hnp }⟩

theorem nonempty_coefficient_field (p : ℕ) : Nonempty (CF p) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge p 2 with h | h
  · exact ⟨{ C := PadicComplex 2
             norm_p := by
               interval_cases p <;> simp }⟩
  · have : Fact p.minFac.Prime := ⟨Nat.minFac_prime (by omega)⟩
    refine cf_of_norm_lt_one (PadicComplex p.minFac) p h ?_
    have h1 : ((p : ℕ) : PadicComplex p.minFac) = ((((p : ℕ) : PadicAlgCl p.minFac)) : PadicComplex p.minFac) := by
      simp
    have h2 : ((p : ℕ) : PadicAlgCl p.minFac) = algebraMap ℚ_[p.minFac] (PadicAlgCl p.minFac) (p : ℚ_[p.minFac]) := by
      simp
    rw [h1, PadicComplex.norm_extends, h2, PadicAlgCl.norm_extends]
    exact (Padic.norm_natCast_lt_one_iff).2 (Nat.minFac_dvd p)

end Formalism.MainNotions.DIV.Inh

end
