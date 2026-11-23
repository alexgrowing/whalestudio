import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalJ
import Formalism.EllipticTorsion.FormalGroupPointsNoTorsion
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.ShiftAnalyticW
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementK

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.B.KKer

open Formalism.ELL (InFormalGroupPoints)
open Formalism.L2.Th1.F (MulStable IsKerReps)
open Formalism.L2.Th1.E (Unif ptW px IntCurve)

theorem two_dvd_or (x : ℤ_[2]) : (∃ c, x = 2 * c) ∨ ∃ c, x = 1 + 2 * c := by
  obtain ⟨n, hn, h⟩ := PadicInt.exists_mem_range x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  interval_cases n
  · left
    refine ⟨c, ?_⟩
    push_cast at hc
    linear_combination hc
  · right
    refine ⟨c, ?_⟩
    push_cast at hc
    linear_combination hc

theorem norm_unit_pow_four (b : ℤ_[2]) (hb : ‖b‖ = 1) : ‖b ^ 4 - 1‖ ≤ 16⁻¹ := by
  have h2 : ‖(2 : ℤ_[2])‖ = 2⁻¹ := by
    have := PadicInt.norm_p (p := 2)
    simpa using this
  have key : ∃ e : ℤ_[2], b ^ 4 - 1 = 2 ^ 4 * e := by
    rcases two_dvd_or b with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exfalso
      rw [norm_mul, h2] at hb
      have := PadicInt.norm_le_one c
      linarith
    · rcases two_dvd_or c with ⟨e, rfl⟩ | ⟨e, rfl⟩
      · exact ⟨(e + 2 * e ^ 2) * (1 + 4 * (e + 2 * e ^ 2)), by ring⟩
      · exact ⟨(1 + 3 * e + 2 * e ^ 2) * (1 + 4 * (1 + 3 * e + 2 * e ^ 2)), by ring⟩
  obtain ⟨e, he⟩ := key
  rw [he, norm_mul, norm_pow, h2]
  have := PadicInt.norm_le_one e
  have h0 := norm_nonneg e
  norm_num
  linarith

theorem coe_eq_algebraMap (x : ℚ_[2]) : (x : ℂ_[2]) = algebraMap ℚ_[2] ℂ_[2] x := rfl

theorem norm_two : ‖(2 : ℂ_[2])‖ = 2⁻¹ := by
  have e : (2 : ℂ_[2]) = (((2 : ℕ) : ℚ_[2]) : ℂ_[2]) := by
    rw [coe_eq_algebraMap, map_natCast, Nat.cast_ofNat]
  rw [e, PadicComplex.norm_extends', Padic.norm_p]
  norm_num

theorem norm_odd {m : ℕ} (hm : Odd m) : ‖(m : ℂ_[2])‖ = 1 := by
  have h1 := PadicComplex.norm_extends' 2 (m : ℚ_[2])
  rw [Padic.norm_natCast_eq_one_iff.2 (Nat.coprime_two_left.2 hm)] at h1
  simpa using h1

theorem norm_coe_unit_pow_four (b : ℤ_[2]) (hb : ‖b‖ = 1) :
    ‖((b : ℚ_[2]) : ℂ_[2]) ^ 4 - 1‖ ≤ 16⁻¹ := by
  have e : ((b : ℚ_[2]) : ℂ_[2]) ^ 4 - 1 = (((b ^ 4 - 1 : ℤ_[2]) : ℚ_[2]) : ℂ_[2]) := by
    rw [coe_eq_algebraMap, coe_eq_algebraMap]
    push_cast
    simp
  rw [e, PadicComplex.norm_extends', PadicInt.norm_def.symm]
  exact norm_unit_pow_four b hb

section Ultra

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem norm_sum_lt {J : Type*} (s : Finset J) (f : J → K) {C : ℝ} (hC : 0 < C)
    (h : ∀ i ∈ s, ‖f i‖ < C) : ‖∑ i ∈ s, f i‖ < C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hC
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
      (max_lt (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem norm_c₄_le (W : WeierstrassCurve K) (h1 : ‖W.a₁‖ ≤ 1) (h2 : ‖W.a₂‖ ≤ 1) (h3 : ‖W.a₃‖ ≤ 1)
    (h4 : ‖W.a₄‖ ≤ 1) : ‖W.c₄‖ ≤ 1 := by
  have hA : ∀ x y : K, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖x + y‖ ≤ 1 := fun x y hx hy =>
    (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  have hS : ∀ x y : K, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖x - y‖ ≤ 1 := fun x y hx hy => by
    rw [sub_eq_add_neg]
    exact hA _ _ hx (by rwa [norm_neg])
  have hM : ∀ x y : K, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ‖x * y‖ ≤ 1 := fun x y hx hy => by
    rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy
  have hN : ∀ n : ℕ, ‖(n : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K
  have e : W.c₄ = (W.a₁ * W.a₁ + ((4 : ℕ) : K) * W.a₂) * (W.a₁ * W.a₁ + ((4 : ℕ) : K) * W.a₂) -
      ((24 : ℕ) : K) * (((2 : ℕ) : K) * W.a₄ + W.a₁ * W.a₃) := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    push_cast
    ring
  rw [e]
  have hb2 := hA _ _ (hM _ _ h1 h1) (hM _ _ (hN 4) h2)
  exact hS _ _ (hM _ _ hb2 hb2) (hM _ _ (hN 24) (hA _ _ (hM _ _ (hN 2) h4) (hM _ _ h1 h3)))

end Ultra

theorem exists_order_two {G : Type*} [AddCommGroup G] (Q : G) (hQ : Q ≠ 0) (a : ℕ)
    (h : 2 ^ a • Q = 0) : ∃ j : ℕ, 2 ^ j • Q ≠ 0 ∧ 2 ^ j • Q + 2 ^ j • Q = 0 := by
  classical
  have hex : ∃ k, 2 ^ k • Q = 0 := ⟨a, h⟩
  have h0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0] at this
    exact hQ (by simpa using this)
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero h0
  refine ⟨j, Nat.find_min hex (by omega), ?_⟩
  have := Nat.find_spec hex
  rw [hj, Nat.succ_eq_add_one, pow_succ, mul_nsmul, two_nsmul] at this
  exact this

section Main

variable {L : PeriodPair} {ι : ℂ ≃+* ℂ_[2]} {W : WeierstrassCurve ℂ_[2]}

local notation "π" => ptW 2 L ι W

open Classical in
theorem not_in_kernel_of_multiplier_torsion (h1 : TwoTorsionKernelUnique) (h2 : TorsBound) (h3 : KapNorm) (h4 : KappaSum)
    (hU : Unif 2 L ι W) (hW : IntCurve W) (ha1 : ‖W.a₁‖ = 1) (α : ℂ) (b : ℤ_[2]) (hα : α ≠ 0)
    (hst : MulStable L α) (hb : ι α = ((b : ℚ_[2]) : ℂ_[2])) (hb1 : ‖b‖ = 1) (t1 : ℂ)
    (hαt1 : α * t1 ∈ L.lattice) (ht1 : t1 ∉ L.lattice) : ¬ InFormalGroupPoints (π t1) := by
  intro hE
  have hW' := hW
  obtain ⟨a1, a2, a3, a4, a6, hΔ⟩ := hW'
  have hM : Formalism.ELL.IntegralModel W := ⟨a1, a2, a3, a4, a6⟩
  have hIM : Formalism.L2.Th1.A.IntModel W := ⟨a1, a2, a3, a4, a6⟩
  have hsub := Formalism.ELL.formal_group_points_subgroup.{0} ℂ_[2] W hM hΔ
  have htor := Formalism.ELL.formal_group_points_no_torsion.{0} ℂ_[2] W hM hΔ
  have hadd := Formalism.L2.Th1.E.ptWAdd 2 L ι W hU
  have hzero := Formalism.L2.Th1.E.ptWZero 2 L ι W hU
  have hnsmul : ∀ (n : ℕ) (t : ℂ), π ((n : ℂ) * t) = n • π t := by
    intro n t
    induction n with
    | zero =>
      rw [Nat.cast_zero, zero_mul, zero_nsmul]
      exact (hzero 0).2 (zero_mem _)
    | succ n ih =>
      rw [succ_nsmul, ← ih, ← hadd]
      congr 1
      push_cast
      ring
  have hE1n : ∀ (n : ℕ) (P : W.toAffine.Point), InFormalGroupPoints P → InFormalGroupPoints (n • P) := by
    intro n P hP
    induction n with
    | zero =>
      rw [zero_nsmul]
      trivial
    | succ n ih =>
      rw [succ_nsmul]
      exact (hsub _ _ ih hP).1
  have hcong : ∀ s t : ℂ, s - t ∈ L.lattice → π s = π t := by
    intro s t h
    have e : s = (s - t) + t := by ring
    rw [e, hadd, (hzero _).2 h, zero_add]
  have hcong' : ∀ s t : ℂ, π s = π t → s - t ∈ L.lattice := by
    intro s t h
    rw [← hzero]
    have e : π s = π (s - t) + π t := by
      rw [← hadd]
      congr 1
      ring
    rw [h] at e
    simpa using e.symm

  obtain ⟨T, n, hT, hn, -⟩ := Formalism.L2.Th1.F.mulStableIntegral L α hst
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
    exact hα hn
  have hker : ∀ t : ℂ, α * t ∈ L.lattice → ((n.natAbs : ℕ) : ℂ) * t ∈ L.lattice := by
    intro t ht
    have hc : conj α = T - α := by linear_combination hT
    have e : (n : ℂ) * t = (T : ℂ) * (α * t) - α * (α * t) := by
      rw [← hn, hc]
      ring
    have hz : (n : ℂ) * t ∈ L.lattice := by
      rw [e]
      refine L.lattice.sub_mem ?_ (hst _ ht)
      have := L.lattice.smul_mem T ht
      simpa [zsmul_eq_mul] using this
    rcases Int.natAbs_eq n with h | h
    · have e2 : ((n.natAbs : ℕ) : ℂ) = (n : ℂ) := by
        rw [← Int.cast_natCast, ← h]
      rw [e2]
      exact hz
    · have e3 : ((n.natAbs : ℕ) : ℤ) = -n := by omega
      have e2 : ((n.natAbs : ℕ) : ℂ) = -(n : ℂ) := by
        rw [← Int.cast_natCast, e3, Int.cast_neg]
      rw [e2, neg_mul]
      exact L.lattice.neg_mem hz
  obtain ⟨a, m, hm, hN⟩ := Nat.exists_eq_two_pow_mul_odd (n := n.natAbs) (by simpa using hn0)
  have hA : ∀ t : ℂ, α * t ∈ L.lattice → InFormalGroupPoints (π t) → 2 ^ a • π t = 0 := by
    intro t ht hEt
    apply htor m (norm_odd hm) _ (hE1n _ _ hEt)
    rw [← mul_nsmul, ← hN, ← hnsmul]
    exact (hzero _).2 (hker t ht)

  have hQ0 : π t1 ≠ 0 := fun h => ht1 ((hzero _).1 h)
  obtain ⟨j, hj0, hj2⟩ := exists_order_two (π t1) hQ0 a (hA t1 hαt1 hE)
  have hπS : π (((2 ^ j : ℕ) : ℂ) * t1) = 2 ^ j • π t1 := hnsmul _ _
  have hαS : α * (((2 ^ j : ℕ) : ℂ) * t1) ∈ L.lattice := by
    have e : α * (((2 ^ j : ℕ) : ℂ) * t1) = ((2 ^ j : ℕ) : ℂ) * (α * t1) := by ring
    rw [e]
    have := L.lattice.smul_mem ((2 ^ j : ℕ) : ℤ) hαt1
    simpa [zsmul_eq_mul] using this
  have htSn : ((2 ^ j : ℕ) : ℂ) * t1 ∉ L.lattice := fun h => hj0 (by
    rw [← hπS]
    exact (hzero _).2 h)
  obtain ⟨S, hS⟩ := Formalism.L2.Th1.F.kerRepsExist L α hα hst
  obtain ⟨PS, hPS, hPSl⟩ := hS.2.2 _ hαS htSn
  have hπPS : π PS = 2 ^ j • π t1 := by
    rw [← hπS]
    exact (hcong _ _ hPSl).symm
  have hPS0 : π PS ≠ 0 := by
    rw [hπPS]
    exact hj0
  have hPS2 : π PS + π PS = 0 := by
    rw [hπPS]
    exact hj2
  have hPSE : InFormalGroupPoints (π PS) := by
    rw [hπPS]
    exact hE1n _ _ hE
  have h2n : ‖(2 : ℂ_[2])‖ = 2⁻¹ := norm_two
  have hx4 : ‖px W (π PS)‖ = 4 := (h1 ℂ_[2] W hW h2n ha1 (π PS) (π PS) hPS0 hPS2 hPSE).1
  have hxlt : ∀ P ∈ S, P ≠ PS → ‖px W (π P)‖ < 4 := by
    intro P hP hne
    by_cases hPE : InFormalGroupPoints (π P)
    · by_cases hP2 : π P + π P = 0
      · exfalso
        have hP0 : π P ≠ 0 := fun h => (hS.1 P hP).2 ((hzero _).1 h)
        have := (h1 ℂ_[2] W hW h2n ha1 (π PS) (π P) hPS0 hPS2 hPSE).2 hP0 hP2 hPE
        exact hne (hS.2.1 P hP PS hPS (hcong' _ _ this.symm))
      · exact h2 ℂ_[2] W hW h2n (π P) a (hA P (hS.1 P hP).1 hPE) hP2
    · exact lt_of_le_of_lt (Half.norm_x_le_one_of_not_in_kernel _ hPE) (by norm_num)
  have hκ : ∀ P ∈ S, ι (3 * L.weierstrassP P ^ 2 - L.g₂ / 4) =
      3 * (px W (π P) + W.b₂ / 12) ^ 2 - Formalism.L2.Th1.A.g₂ W / 4 := by
    intro P hP
    rw [Formalism.L2.Th1.E.AnaSysW.px_ptW hU P (hS.1 P hP).2, hU.1]
    simp only [Formalism.L2.Th1.E.AnaSysW.xc, map_sub, map_mul, map_pow, map_div₀, map_ofNat,
      sub_add_cancel]
  have hk16 : ‖ι (3 * L.weierstrassP PS ^ 2 - L.g₂ / 4)‖ = 16 := by
    rw [hκ PS hPS]
    exact (h3 ℂ_[2] W hIM h2n _).1 hx4
  have hklt : ∀ P ∈ S.erase PS, ‖ι (3 * L.weierstrassP P ^ 2 - L.g₂ / 4)‖ < 16 := by
    intro P hP
    obtain ⟨hne, hP⟩ := Finset.mem_erase.1 hP
    rw [hκ P hP]
    exact (h3 ℂ_[2] W hIM h2n _).2 (hxlt P hP hne)
  have hsum : ‖ι (∑ P ∈ S, (3 * L.weierstrassP P ^ 2 - L.g₂ / 4))‖ = 16 := by
    rw [map_sum, ← Finset.add_sum_erase S _ hPS]
    have hr := norm_sum_lt (S.erase PS) (fun P => ι (3 * L.weierstrassP P ^ 2 - L.g₂ / 4))
      (by norm_num : (0 : ℝ) < 16) hklt
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hk16]; exact hr.ne'), hk16]
    exact max_eq_left hr.le
  rw [h4 L α S hα hst hS] at hsum
  have h3n : ‖(3 : ℂ_[2])‖ = 1 := by
    have := norm_odd (m := 3) (by decide)
    simpa using this
  have h5n : ‖(5 : ℂ_[2])‖ = 1 := by
    have := norm_odd (m := 5) (by decide)
    simpa using this
  have h12 : ‖(12 : ℂ_[2])‖ = 4⁻¹ := by
    have e : (12 : ℂ_[2]) = 2 * 2 * 3 := by norm_num
    rw [e, norm_mul, norm_mul, h2n, h3n]
    norm_num
  have h20 : ‖(20 : ℂ_[2])‖ = 4⁻¹ := by
    have e : (20 : ℂ_[2]) = 2 * 2 * 5 := by norm_num
    rw [e, norm_mul, norm_mul, h2n, h5n]
    norm_num
  have hg : ‖Formalism.L2.Th1.A.g₂ W‖ ≤ 4 := by
    unfold Formalism.L2.Th1.A.g₂
    rw [norm_div, h12]
    have := norm_c₄_le W a1 a2 a3 a4
    rw [div_inv_eq_mul]
    linarith
  have hle : ‖ι ((α ^ 4 - 1) * L.g₂ / 20)‖ ≤ 1 := by
    rw [map_div₀, map_mul, map_sub, map_pow, map_one, map_ofNat, ← hU.1, hb, norm_div, norm_mul,
      h20, div_inv_eq_mul]
    have hu := norm_coe_unit_pow_four b hb1
    have h0 := norm_nonneg (((b : ℚ_[2]) : ℂ_[2]) ^ 4 - 1)
    have h0' := norm_nonneg (Formalism.L2.Th1.A.g₂ W)
    have : ‖((b : ℚ_[2]) : ℂ_[2]) ^ 4 - 1‖ * ‖Formalism.L2.Th1.A.g₂ W‖ ≤ 16⁻¹ * 4 :=
      mul_le_mul hu hg h0' (by norm_num)
    linarith
  rw [hsum] at hle
  norm_num at hle

end Main

theorem KernelIntegral_of (h1 : TwoTorsionKernelUnique) (h2 : TorsBound) (h3 : KapNorm) (h4 : KappaSum) :
    KernelIntegral := by
  intro L ι W hU hW ha1 α b hα hst hb hb1 t hαt ht
  exact not_in_kernel_of_multiplier_torsion h1 h2 h3 h4 hU hW ha1 α b hα hst hb hb1 t hαt ht

end Formalism.L2.Th1.B.KKer
