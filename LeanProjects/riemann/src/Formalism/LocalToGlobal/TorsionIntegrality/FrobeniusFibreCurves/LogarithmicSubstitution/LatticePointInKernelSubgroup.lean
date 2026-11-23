import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalJ
import Formalism.EllipticTorsion.FormalGroupPointsNoTorsion
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Th0FromPhPrime
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.GoodModelLattice
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementK

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.B.KFin

open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.ELL (InFormalGroupPoints)
open Formalism.L2.Th1.F (MulStable IsKerReps)
open Formalism.L2.Th1.E (Unif ptW inW px py IntCurve OneUnit GaussOne)

theorem norm_coe (q : ℚ_[2]) : ‖((q : ℚ_[2]) : ℂ_[2])‖ = ‖q‖ := PadicComplex.norm_extends' 2 q

theorem norm_two : ‖(2 : ℂ_[2])‖ = 2⁻¹ := by
  have h := norm_coe (2 : ℚ_[2])
  have e : (((2 : ℚ_[2]) : ℚ_[2]) : ℂ_[2]) = 2 := map_ofNat (algebraMap ℚ_[2] ℂ_[2]) 2
  rw [e] at h
  rw [h]
  have := Padic.norm_p (p := 2)
  simpa using this

theorem norm_three : ‖(3 : ℂ_[2])‖ = 1 := by
  have e : (3 : ℂ_[2]) = 1 + 2 := by norm_num
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one, norm_two]; norm_num),
    norm_one, norm_two]
  norm_num

theorem norm_twelve : ‖(12 : ℂ_[2])‖ = 4⁻¹ := by
  have e : (12 : ℂ_[2]) = 2 * 2 * 3 := by norm_num
  rw [e, norm_mul, norm_mul, norm_two, norm_three]
  norm_num

theorem nle_add {a b : ℂ_[2]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

theorem nle_sub {a b : ℂ_[2]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact nle_add ha (by rw [norm_neg]; exact hb)

theorem nle_mul {a b : ℂ_[2]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) hb

theorem unit_sq (b : ℤ_[2]) (hb : ‖b‖ = 1) : ‖1 - b ^ 2‖ ≤ 4⁻¹ := by
  obtain ⟨n, hn, hmem⟩ := PadicInt.exists_mem_range b
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
  have h2 : ‖(2 : ℤ_[2])‖ = 2⁻¹ := by
    have := PadicInt.norm_p (p := 2)
    simpa using this
  interval_cases n
  · exfalso
    have : ‖b‖ < 1 := by
      rw [PadicInt.norm_lt_one_iff_dvd]
      simpa using hmem
    rw [hb] at this
    exact lt_irrefl _ this
  · obtain ⟨c, hc⟩ := hmem
    have e : 1 - b ^ 2 = -(2 * 2 * (c * (c + 1))) := by
      have : b = 1 + 2 * c := by
        have hc' : b - 1 = 2 * c := by simpa using hc
        rw [← hc']; ring
      rw [this]; ring
    rw [e, norm_neg, norm_mul, norm_mul, h2]
    have := PadicInt.norm_le_one (c * (c + 1))
    nlinarith [norm_nonneg (c * (c + 1))]

theorem unit_sq' (b : ℤ_[2]) (hb : ‖b‖ = 1) : ‖1 - (((b : ℚ_[2]) : ℂ_[2])) ^ 2‖ ≤ 4⁻¹ := by
  have e : 1 - (((b : ℚ_[2]) : ℂ_[2])) ^ 2 = ((((1 - b ^ 2 : ℤ_[2]) : ℚ_[2])) : ℂ_[2]) := by
    have : (((1 - b ^ 2 : ℤ_[2]) : ℚ_[2])) = 1 - (b : ℚ_[2]) ^ 2 := by push_cast; ring
    rw [this]
    exact (by simp : algebraMap ℚ_[2] ℂ_[2] (1 - (b : ℚ_[2]) ^ 2)
      = 1 - (algebraMap ℚ_[2] ℂ_[2] (b : ℚ_[2])) ^ 2).symm
  rw [e, norm_coe]
  exact unit_sq b hb

section Pts

variable {L : PeriodPair} {ι : ℂ ≃+* ℂ_[2]} {W : WeierstrassCurve ℂ_[2]}

theorem mem_kernel_subgroup_iff_norm (hU : Unif 2 L ι W) (t : ℂ) (ht : t ∉ L.lattice) :
    InFormalGroupPoints (ptW 2 L ι W t) ↔ 1 < ‖ι (L.weierstrassP t) - W.b₂ / 12‖ := by
  rw [Formalism.L2.Th1.E.AnaSysW.ptW_notMem hU t ht]
  exact Iff.rfl

theorem lattice_point_in_kernel_subgroup (hU : Unif 2 L ι W) (t : ℂ) (ht : t ∈ L.lattice) : InFormalGroupPoints (ptW 2 L ι W t) := by
  rw [(Formalism.L2.Th1.E.ptWZero 2 L ι W hU t).2 ht]
  trivial

open Classical in
theorem ptW_neg (hU : Unif 2 L ι W) (t : ℂ) : ptW 2 L ι W (-t) = - ptW 2 L ι W t := by
  apply eq_neg_of_add_eq_zero_left
  rw [← Formalism.L2.Th1.E.ptWAdd 2 L ι W hU, neg_add_cancel]
  exact (Formalism.L2.Th1.E.ptWZero 2 L ι W hU 0).2 L.lattice.zero_mem

open Classical in
theorem kernel_subgroup_add_mem (hU : Unif 2 L ι W) (hW : IntCurve W) (s t : ℂ) (hs : InFormalGroupPoints (ptW 2 L ι W s))
    (ht : InFormalGroupPoints (ptW 2 L ι W t)) : InFormalGroupPoints (ptW 2 L ι W (s + t)) := by
  obtain ⟨a1, a2, a3, a4, a6, hΔ⟩ := hW
  rw [Formalism.L2.Th1.E.ptWAdd 2 L ι W hU]
  exact (Formalism.ELL.formal_group_points_subgroup.{0} ℂ_[2] W ⟨a1, a2, a3, a4, a6⟩ hΔ _ _ hs ht).1

open Classical in
theorem kernel_subgroup_neg_mem (hU : Unif 2 L ι W) (hW : IntCurve W) (t : ℂ) (ht : InFormalGroupPoints (ptW 2 L ι W t)) :
    InFormalGroupPoints (ptW 2 L ι W (-t)) := by
  obtain ⟨a1, a2, a3, a4, a6, hΔ⟩ := hW
  rw [ptW_neg hU]
  exact (Formalism.ELL.formal_group_points_subgroup.{0} ℂ_[2] W ⟨a1, a2, a3, a4, a6⟩ hΔ _ _ ht ht).2

theorem norm_b2_div_twelve_le_four (hW : IntCurve W) : ‖W.b₂ / 12‖ ≤ 4 := by
  obtain ⟨a1, a2, -⟩ := hW
  have h4 : ‖(4 : ℂ_[2])‖ ≤ 1 := by
    have e : (4 : ℂ_[2]) = 2 * 2 := by norm_num
    rw [e, norm_mul, norm_two]; norm_num
  have hb : ‖W.b₂‖ ≤ 1 := by
    unfold WeierstrassCurve.b₂
    rw [pow_two]
    exact nle_add (nle_mul a1 a1) (nle_mul h4 a2)
  rw [norm_div, norm_twelve]
  rw [div_inv_eq_mul]
  linarith

end Pts

theorem kernel_stable_of_integral_kernel (hK : KernelIntegral) : KernelStableUnderMultiplier := by
  intro L ι W hU hW ha1 α b hα hmul hb hnb t ht
  have hK' := hK L ι W hU hW ha1 α b hα hmul hb hnb
  by_cases htL : t ∈ L.lattice
  · exact lattice_point_in_kernel_subgroup hU _ (hmul t htL)
  have hαt : α * t ∉ L.lattice := fun h => hK' t h htL ht
  obtain ⟨S, hS⟩ := Formalism.L2.Th1.F.kerRepsExist L α hα hmul
  have hiso := Formalism.L2.Th1.F.isogenyP L α S hα hmul hS t hαt
  have hP : ∀ P ∈ S, ‖ι (L.weierstrassP P) - W.b₂ / 12‖ ≤ 1 := by
    intro P hPS
    exact not_lt.1 (mt (mem_kernel_subgroup_iff_norm hU P (hS.1 P hPS).2).2 (hK' P (hS.1 P hPS).1 (hS.1 P hPS).2))
  have htP : ∀ P ∈ S, ‖ι (L.weierstrassP (t + P)) - W.b₂ / 12‖ ≤ 1 := by
    intro P hPS
    have hn : ¬ InFormalGroupPoints (ptW 2 L ι W (t + P)) := by
      intro H
      apply hK' P (hS.1 P hPS).1 (hS.1 P hPS).2
      have e : P = (t + P) + -t := by ring
      rw [e]
      exact kernel_subgroup_add_mem hU hW _ _ H (kernel_subgroup_neg_mem hU hW _ ht)
    have hl : t + P ∉ L.lattice := fun h => hn (lattice_point_in_kernel_subgroup hU _ h)
    exact not_lt.1 (mt (mem_kernel_subgroup_iff_norm hU _ hl).2 hn)
  have h := congrArg ι hiso
  simp only [map_mul, map_pow, map_add, map_sum, map_sub] at h
  rw [hb] at h
  rw [mem_kernel_subgroup_iff_norm hU _ hαt]
  rw [mem_kernel_subgroup_iff_norm hU _ htL] at ht
  by_contra hle
  rw [not_lt] at hle
  have hB : ‖(((b : ℚ_[2]) : ℂ_[2]))‖ ≤ 1 := by
    rw [norm_coe]; exact le_of_eq hnb
  have hsum : ‖∑ P ∈ S, ((ι (L.weierstrassP (t + P)) - W.b₂ / 12) -
      (ι (L.weierstrassP P) - W.b₂ / 12))‖ ≤ 1 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
      (fun P hPS => nle_sub (htP P hPS) (hP P hPS))
  have hc : ‖(1 - (((b : ℚ_[2]) : ℂ_[2])) ^ 2) * (W.b₂ / 12)‖ ≤ 1 := by
    rw [norm_mul]
    have h1 := unit_sq' b hnb
    have h2 := norm_b2_div_twelve_le_four hW
    nlinarith [norm_nonneg (1 - (((b : ℚ_[2]) : ℂ_[2])) ^ 2), norm_nonneg (W.b₂ / 12)]
  have e : ι (L.weierstrassP t) - W.b₂ / 12 =
      (((b : ℚ_[2]) : ℂ_[2])) ^ 2 * (ι (L.weierstrassP (α * t)) - W.b₂ / 12)
        - (1 - (((b : ℚ_[2]) : ℂ_[2])) ^ 2) * (W.b₂ / 12)
        - ∑ P ∈ S, ((ι (L.weierstrassP (t + P)) - W.b₂ / 12) -
            (ι (L.weierstrassP P) - W.b₂ / 12)) := by
    have e2 : ∑ P ∈ S, ((ι (L.weierstrassP (t + P)) - W.b₂ / 12) -
        (ι (L.weierstrassP P) - W.b₂ / 12)) =
        ∑ P ∈ S, (ι (L.weierstrassP (t + P)) - ι (L.weierstrassP P)) :=
      Finset.sum_congr rfl (fun P _ => by ring)
    rw [e2]
    linear_combination -h
  rw [e] at ht
  have : ‖(((b : ℚ_[2]) : ℂ_[2])) ^ 2 * (ι (L.weierstrassP (α * t)) - W.b₂ / 12)
        - (1 - (((b : ℚ_[2]) : ℂ_[2])) ^ 2) * (W.b₂ / 12)
        - ∑ P ∈ S, ((ι (L.weierstrassP (t + P)) - W.b₂ / 12) -
            (ι (L.weierstrassP P) - W.b₂ / 12))‖ ≤ 1 := by
    refine nle_sub (nle_sub (nle_mul ?_ hle) hc) hsum
    rw [pow_two]
    exact nle_mul hB hB
  exact absurd ht (not_lt.2 this)

open Classical in
theorem PointsTwoFinal_of (hK : KernelIntegral) (hS : KernelStableUnderMultiplier) (hU2 : TwoTorsionKernelUnique) :
    PointsTwoFinal := by
  intro L ι W hU hW ha1 α ω₀ b b' hα hmul hb hb' hnb hnb' hω hc
  have hK' := hK L ι W hU hW ha1 α b hα hmul hb hnb
  have hS' := hS L ι W hU hW ha1 α b hα hmul hb hnb
  have hadd := Formalism.L2.Th1.E.ptWAdd 2 L ι W hU
  have hzero := Formalism.L2.Th1.E.ptWZero 2 L ι W hU
  obtain ⟨tr, n, htr, hn, -⟩ := Formalism.L2.Th1.F.mulStableIntegral L α hmul
  have hcm : MulStable L (conj α) := by
    intro ω hω'
    have e : conj α * ω = tr • ω - α * ω := by
      rw [zsmul_eq_mul, ← htr]; ring
    rw [e]
    exact sub_mem (zsmul_mem hω' _) (hmul ω hω')
  have h2n : (2 : ℤ) ∣ n := by
    have h1 : ι α * ι (conj α) = (n : ℂ_[2]) := by rw [← map_mul, hn, map_intCast]
    rw [hb, hb'] at h1
    have h2 : ‖(n : ℂ_[2])‖ < 1 := by
      rw [← h1, norm_mul, norm_coe, norm_coe]
      have e1 : ‖(b : ℚ_[2])‖ = 1 := hnb
      have e2 : ‖(b' : ℚ_[2])‖ < 1 := hnb'
      rw [e1, one_mul]
      exact e2
    have h3 : ‖((n : ℤ_[2]))‖ < 1 := by
      have e : (n : ℂ_[2]) = ((((n : ℤ_[2]) : ℚ_[2])) : ℂ_[2]) := by
        have : (((n : ℤ_[2]) : ℚ_[2])) = (n : ℚ_[2]) := by push_cast; rfl
        rw [this]
        exact (map_intCast (algebraMap ℚ_[2] ℂ_[2]) n).symm
      rw [e, norm_coe] at h2
      exact h2
    exact_mod_cast (PadicInt.norm_int_lt_one_iff_dvd n).1 h3
  obtain ⟨m, rfl⟩ := h2n
  have key : ∀ z, 2 * z ∈ L.lattice → conj α * (α * z) ∈ L.lattice := by
    intro z hz
    have e : conj α * (α * z) = m • (2 * z) := by
      rw [zsmul_eq_mul]
      have : conj α * (α * z) = (α * conj α) * z := by ring
      rw [this, hn]
      push_cast
      ring
    rw [e]
    exact zsmul_mem hz _
  have ht0 : ω₀ / 2 ∉ L.lattice := fun h => hc (hcm _ h)
  have h2t0 : 2 * (ω₀ / 2) ∈ L.lattice := by
    have : 2 * (ω₀ / 2) = ω₀ := by ring
    rw [this]; exact hω
  have first : ¬ InFormalGroupPoints (ptW 2 L ι W (ω₀ / 2)) := by
    intro H
    have h1 := hS' _ H
    have h2 : α * (ω₀ / 2) ∉ L.lattice := fun h => hK' _ h ht0 H
    have d1 : ptW 2 L ι W (α * (ω₀ / 2)) + ptW 2 L ι W (α * (ω₀ / 2)) = 0 := by
      rw [← hadd, hzero]
      have : α * (ω₀ / 2) + α * (ω₀ / 2) = α * ω₀ := by ring
      rw [this]; exact hmul _ hω
    have d2 : ptW 2 L ι W (ω₀ / 2) + ptW 2 L ι W (ω₀ / 2) = 0 := by
      rw [← hadd, hzero]
      have : ω₀ / 2 + ω₀ / 2 = ω₀ := by ring
      rw [this]; exact hω
    have heq := (hU2 ℂ_[2] W hW norm_two ha1 (ptW 2 L ι W (α * (ω₀ / 2))) (ptW 2 L ι W (ω₀ / 2))
      (fun h => h2 ((hzero _).1 h)) d1 h1).2 (fun h => ht0 ((hzero _).1 h)) d2 H
    have hd : α * (ω₀ / 2) - ω₀ / 2 ∈ L.lattice := by
      rw [← hzero, sub_eq_add_neg, hadd, ptW_neg hU, heq, add_neg_cancel]
    apply hc
    have e : conj α * (ω₀ / 2) = conj α * (α * (ω₀ / 2)) - conj α * (α * (ω₀ / 2) - ω₀ / 2) := by
      ring
    rw [e]
    exact sub_mem (key _ h2t0) (hcm _ hd)
  refine ⟨first, ?_, ?_⟩
  · intro Q hQ H
    apply first
    have e : ω₀ / 2 = α * Q + -(α * Q - ω₀ / 2) := by ring
    rw [e]
    exact kernel_subgroup_add_mem hU hW _ _ (hS' _ H) (kernel_subgroup_neg_mem hU hW _ (lattice_point_in_kernel_subgroup hU _ hQ))
  · intro z hz h2z
    apply hc
    have e : conj α * (ω₀ / 2) = conj α * (α * z) - conj α * (α * z - ω₀ / 2) := by ring
    rw [e]
    exact sub_mem (key _ h2z) (hcm _ hz)

theorem Th0TwoFinal_of (hP : PointsTwoFinal) : ThetaZeroAtTwo := by
  intro L ι W hU hW ha1 α ω₀ b b' hα hmul hb hb' hnb hnb' hω hc
  obtain ⟨p1, p2, p3⟩ := hP L ι W hU hW ha1 α ω₀ b b' hα hmul hb hb' hnb hnb' hω hc
  have ht0 : ω₀ / 2 ∉ L.lattice := fun h => p1 (lattice_point_in_kernel_subgroup hU _ h)
  have hx : ‖px W (ptW 2 L ι W (ω₀ / 2))‖ ≤ 1 := Half.norm_x_le_one_of_not_in_kernel _ p1
  have hI : Formalism.L2.Th1.A.IntModel W := ⟨hW.1, hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.1⟩
  obtain ⟨q1, q2⟩ := th0TwoAnalytic L ι W hU hI α ω₀ b b' hα hmul hω ht0 hb hb' hnb hnb' p3 hx
    (fun z hz => Half.norm_x_le_one_of_not_in_kernel _ (p2 z hz))
  exact ⟨q1, q2, Formalism.L2.Th1.E.shiftAnalyticW 2 L ι W hU hW ω₀ hω ht0 hx q2⟩

end Formalism.L2.Th1.B.KFin
