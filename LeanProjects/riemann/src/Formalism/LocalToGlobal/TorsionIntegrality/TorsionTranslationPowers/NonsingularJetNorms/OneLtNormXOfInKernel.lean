import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementS
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.FacShapeZero
import Formalism.EllipticTorsion.FormalGroupPointsNoTorsion
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Taylor0ConstMul

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

namespace Shift

section Tools

variable {K : Type} [NormedField K]

theorem norm_cc_of_unitAt {f : K⟦X⟧} (h : UnitAt 0 f) : ‖constantCoeff f‖ = 1 := by
  obtain ⟨a, V, ha, hV, rfl⟩ := h
  simp [hV.1, ha]

theorem tele [IsUltrametricDist K] (g ψ : ℕ → K⟦X⟧) (c : K) (n : ℕ) (hn : ‖((n + 1 : ℕ) : K)‖ = 1)
    (h0 : OneUnit (g 0)) (hper : g (n + 1) = g 0) (hne : ∀ j, constantCoeff (g j) ≠ 0)
    (hψ : ∀ j, UnitAt 0 (ψ j))
    (hrec : ∀ j, g (j + 2) * g j = (C (c ^ 2) * ψ (j + 1)) * g (j + 1) ^ 2) :
    OneUnit (C (constantCoeff (g 1))⁻¹ * g 1) := by
  obtain ⟨-, -, -, -, -, -, oMul, oPow, oInv, -⟩ := intRules K
  obtain ⟨uMul, uPow, -, -, -⟩ := unitAtRules K
  have key := Power.closed g (fun j => C (c ^ 2) * ψ j) 1 (g 0) n (by simp)
    (fun j _ h => hne j (by rw [h, map_zero])) (fun j _ => hrec j) n le_rfl
  have hprod : ∃ (r : ℕ) (f : K⟦X⟧), UnitAt 0 f ∧
      ∏ j ∈ Finset.range n, (C (c ^ 2) * ψ (j + 1)) ^ (n - j) = C (c ^ r) * f := by
    apply Finset.prod_induction _ (fun f => ∃ (r : ℕ) (f' : K⟦X⟧), UnitAt 0 f' ∧ f = C (c ^ r) * f')
    · rintro _ _ ⟨r1, g1, h1, rfl⟩ ⟨r2, g2, h2, rfl⟩
      exact ⟨r1 + r2, g1 * g2, uMul 0 0 _ _ h1 h2, by rw [pow_add, map_mul]; ring⟩
    · exact ⟨0, 1, Main.unitAt_one, by simp⟩
    · intro j _
      exact ⟨2 * (n - j), _, by simpa using uPow 0 (n - j) _ (hψ (j + 1)),
        by rw [mul_pow, ← map_pow, ← pow_mul]⟩
  obtain ⟨r, _, ⟨a, V, ha, hV, rfl⟩, hpr⟩ := hprod
  rw [hpr, hper, one_pow, one_mul, pow_zero, mul_one, ← pow_succ'] at key
  have hh := hne 1
  have hcc := congrArg constantCoeff key
  rw [map_pow, h0.1, one_pow, map_mul, map_pow, map_mul, map_mul, constantCoeff_C, constantCoeff_C,
    hV.1, mul_one] at hcc
  generalize hh' : constantCoeff (g 1) = h at hh hcc ⊢
  have hV0 : constantCoeff V ≠ 0 := by rw [hV.1]; exact one_ne_zero
  have hVi : V * V⁻¹ = 1 := PowerSeries.mul_inv_cancel V hV0
  have hinv : h⁻¹ ^ (n + 1) = c ^ r * a := by
    rw [inv_pow]
    exact inv_eq_of_mul_eq_one_right hcc.symm
  have hY : (C h⁻¹ * g 1) ^ (n + 1) = V⁻¹ * g 0 ^ (n + 1) := by
    calc (C h⁻¹ * g 1) ^ (n + 1) = (V * V⁻¹) * (C (h⁻¹ ^ (n + 1)) * g 1 ^ (n + 1)) := by
          rw [hVi, one_mul, mul_pow, map_pow]
      _ = V⁻¹ * (g 1 ^ (n + 1) * (C (c ^ r) * (C a * V))) := by
          rw [hinv, map_mul]; ring
      _ = _ := by rw [← key]
  have hone : constantCoeff (C h⁻¹ * g 1) = 1 := by
    rw [map_mul, constantCoeff_C, hh', inv_mul_cancel₀ hh]
  refine ⟨hone, rootInt K (n + 1) _ hn hone ?_⟩
  rw [hY]
  exact (oMul _ _ (oInv _ _ hV hVi) (oPow _ _ h0)).2

end Tools

section Pts

variable {K : Type} [NormedField K] (W : WeierstrassCurve K)

theorem in_kernel_of_one_lt_norm_x (R : W.toAffine.Point) (h : 1 < ‖px W R‖) : Formalism.ELL.InFormalGroupPoints R := by
  cases R with
  | zero => trivial
  | some x y hxy => exact h

theorem one_lt_norm_x_of_in_kernel (R : W.toAffine.Point) (hR : R ≠ 0) (h : Formalism.ELL.InFormalGroupPoints R) : 1 < ‖px W R‖ := by
  cases R with
  | zero => exact absurd rfl hR
  | some x y hxy => exact h

theorem py_int [IsUltrametricDist K] (hW : Formalism.ELL.IntegralModel W) (R : W.toAffine.Point)
    (h : ‖px W R‖ ≤ 1) : ‖py W R‖ ≤ 1 := by
  cases R with
  | zero => simp [py]
  | some x y hxy => exact Formalism.ELL.TorsionIntegralEllipticTorsion.y_int W hW hxy.1 h

end Pts

theorem card_kill {G : Type} [AddCommGroup G] (A : AddSubgroup G) [Finite A] (P : G) (hP : P ∈ A) :
    Nat.card A • P = 0 := by
  have h := card_nsmul_eq_zero' (G := A) (x := ⟨P, hP⟩)
  simpa only [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero] using congrArg Subtype.val h

end Shift

open Shift

theorem shifted_points_integral : ShiftPtsInt := by
  intro K _ _ inst W hW A _ hcard S hSA hSS hSx hSy
  have hTor := torsion_integral K W hW
  obtain ⟨h1, h2, h3, h4, h6, hΔ⟩ := hW
  have hM : Formalism.ELL.IntegralModel W := ⟨h1, h2, h3, h4, h6⟩
  have hSub : ∀ P Q : W.toAffine.Point, Formalism.ELL.InFormalGroupPoints P → Formalism.ELL.InFormalGroupPoints Q →
      Formalism.ELL.InFormalGroupPoints (P + Q) ∧ Formalism.ELL.InFormalGroupPoints (-P) := by
    have e : inst = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
    subst e
    exact Formalism.ELL.formal_group_points_subgroup.{0} K W hM hΔ
  have hNoT : ∀ (n : ℕ), ‖(n : K)‖ = 1 → ∀ P : W.toAffine.Point, Formalism.ELL.InFormalGroupPoints P → n • P = 0 →
      P = 0 := by
    have e : inst = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
    subst e
    exact Formalism.ELL.formal_group_points_no_torsion.{0} K W hM hΔ
  refine ⟨fun Q hQ hQ0 => hTor Q _ hcard (card_kill A Q hQ) hQ0, fun P hP => ?_⟩
  have hS0 : S ≠ 0 := fun h => hSA (h ▸ A.zero_mem)
  have hPS0 : P + S ≠ 0 := by
    intro h
    apply hSA
    have : S = -P := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
    rw [this]
    exact A.neg_mem hP
  have hx : ‖px W (P + S)‖ ≤ 1 := by
    by_contra hx
    push Not at hx
    have hE : Formalism.ELL.InFormalGroupPoints (P + S) := in_kernel_of_one_lt_norm_x W _ hx
    have hE2 : Formalism.ELL.InFormalGroupPoints ((P + S) + (P + S)) := (hSub _ _ hE hE).1
    have e2 : (P + S) + (P + S) = P + P := by
      have : (P + S) + (P + S) = (P + P) + (S + S) := by abel
      rw [this, hSS, add_zero]
    have hPP : P + P = 0 := by
      rw [e2] at hE2
      exact hNoT _ hcard _ hE2 (card_kill A _ (A.add_mem hP hP))
    by_cases h2 : 2 ∣ Nat.card A
    · have hn2 : ‖((2 : ℕ) : K)‖ = 1 := Main.norm_natCast_of_dvd h2 hcard
      apply hPS0
      apply hNoT 2 hn2 _ hE
      rw [two_nsmul, e2, hPP]
    · have hP0 : P = 0 := by
        have hd1 : addOrderOf P ∣ 2 := addOrderOf_dvd_of_nsmul_eq_zero (by rw [two_nsmul, hPP])
        have hd2 : addOrderOf P ∣ Nat.card A := addOrderOf_dvd_of_nsmul_eq_zero (card_kill A P hP)
        have hco : Nat.Coprime 2 (Nat.card A) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2
        have := Nat.eq_one_of_dvd_coprimes hco hd1 hd2
        exact AddMonoid.addOrderOf_eq_one_iff.1 this
      rw [hP0, zero_add] at hx
      exact absurd hSx (not_le.2 hx)
  exact ⟨hx, py_int W hM _ hx⟩

theorem shift_unit' : ShiftUnit := by
  intro K _ _ _ W hW A _ hcard S hSA hAint hSint H c hsys
  obtain ⟨hH0, hc0, hid⟩ := hsys
  obtain ⟨-, -, -, -, uC⟩ := unitAtRules K
  have hS0 : ∀ P ∈ A, P + S ≠ 0 := by
    intro P hP h
    apply hSA
    have : S = -P := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
    rw [this]
    exact A.neg_mem hP
  have hfac : ∀ P ∈ A, ∀ Q ∈ A, Q ≠ 0 → UnitAt 0 (C (px W Q) - xT W (P + S)) := by
    intro P hP Q hQ hQ0
    have e1 : P + S + Q = (P + Q) + S := by abel
    have e2 : P + S - Q = (P - Q) + S := by abel
    refine (facShape K W hW (P + S) Q (hS0 P hP) hQ0 (hSint P hP).1 (hSint P hP).2
      (hAint Q hQ hQ0).1 (hAint Q hQ hQ0).2 ?_ ?_).1 ?_ ?_
    · intro _; rw [e1]; exact (hSint _ (A.add_mem hP hQ)).1
    · intro _; rw [e2]; exact (hSint _ (A.sub_mem hP hQ)).1
    · rw [e1]; exact hS0 _ (A.add_mem hP hQ)
    · rw [e2]; exact hS0 _ (A.sub_mem hP hQ)

  have hcc : ∀ P ∈ A, ∀ Q ∈ A, Q ≠ 0 → ∃ b : K, ‖b‖ = 1 ∧
      constantCoeff (H (P + Q)) * constantCoeff (H (P - Q)) =
        b * c Q ^ 2 * constantCoeff (H P) ^ 2 := by
    intro P hP Q hQ hQ0
    obtain ⟨ρ, hρ, h⟩ := hid P hP Q hQ hQ0
    refine ⟨ρ * constantCoeff (C (px W Q) - xT W (P + S)), ?_, ?_⟩
    · rw [norm_mul, hρ, norm_cc_of_unitAt (hfac P hP Q hQ hQ0), one_mul]
    · have := congrArg constantCoeff h
      rw [map_mul, map_mul, map_mul, map_pow, constantCoeff_C] at this
      rw [this]; ring
  have hne : ∀ P ∈ A, constantCoeff (H P) ≠ 0 := by
    intro P hP
    by_cases hP0 : P = 0
    · rw [hP0, hH0.1]; exact one_ne_zero
    · obtain ⟨b, hb, h⟩ := hcc 0 A.zero_mem P hP hP0
      rw [zero_add, hH0.1] at h
      intro h'
      rw [h', zero_mul] at h
      have hb0 : b ≠ 0 := by rintro rfl; simp at hb
      exact mul_ne_zero (mul_ne_zero hb0 (pow_ne_zero 2 (hc0 P hP hP0))) (by simp) h.symm

  have hone : ∀ t ∈ A, OneUnit (C (constantCoeff (H t))⁻¹ * H t) := by
    intro t ht
    by_cases ht0 : t = 0
    · rw [ht0, hH0.1]; simpa using hH0
    · have hdvd : addOrderOf t ∣ Nat.card A := addOrderOf_dvd_of_nsmul_eq_zero (card_kill A t ht)
      have hn0 : addOrderOf t ≠ 0 := by
        intro h
        rw [h] at hdvd
        exact Nat.card_pos.ne' (Nat.eq_zero_of_zero_dvd hdvd)
      obtain ⟨n, hn⟩ : ∃ n, addOrderOf t = n + 1 := Nat.exists_eq_succ_of_ne_zero hn0
      have hnn : ‖((n + 1 : ℕ) : K)‖ = 1 := hn ▸ Main.norm_natCast_of_dvd hdvd hcard
      choose ρ hρ hρid using fun j : ℕ => hid (j • t) (A.nsmul_mem ht j) t ht ht0
      have h := tele (fun j => H (j • t))
        (fun j => C (ρ j) * (C (px W t) - xT W (j • t + S))) (c t) n hnn
        (by simpa using hH0)
        (by rw [← hn, addOrderOf_nsmul_eq_zero, zero_nsmul])
        (fun j => hne _ (A.nsmul_mem ht j))
        (fun j => uC 0 _ _ (hρ j) (hfac _ (A.nsmul_mem ht j) t ht ht0))
        (by
          intro j
          have h := hρid (j + 1)
          have e1 : (j + 1) • t + t = (j + 2) • t := by rw [← succ_nsmul]
          have e2 : (j + 1) • t - t = j • t := by rw [succ_nsmul]; abel
          rw [e1, e2] at h
          rw [h, map_mul]; ring)
      simpa using h

  have hpar := parSumTwo A (fun P => Real.log ‖constantCoeff (H (P : W.toAffine.Point))‖)
    (fun Q => Real.log ‖c (Q : W.toAffine.Point)‖) (by
      rintro ⟨P, hP⟩ ⟨Q, hQ⟩ hQ0
      have hQ0' : Q ≠ 0 := fun h => hQ0 (Subtype.ext h)
      obtain ⟨b, hb, h⟩ := hcc P hP Q hQ hQ0'
      have hl := congrArg (fun z => Real.log ‖z‖) h
      simp only [norm_mul, norm_pow, hb, one_mul] at hl
      rw [Real.log_mul (norm_ne_zero_iff.mpr (hne _ (A.add_mem hP hQ)))
          (norm_ne_zero_iff.mpr (hne _ (A.sub_mem hP hQ))),
        Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr (hc0 Q hQ hQ0')))
          (pow_ne_zero _ (norm_ne_zero_iff.mpr (hne P hP))), Real.log_pow, Real.log_pow] at hl
      push_cast at hl
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_sub]
      linarith)
  obtain ⟨hm, hM⟩ := hpar
  refine ⟨fun Q hQ hQ0 => ?_, fun P hP => ⟨?_, hone P hP⟩⟩
  · have := hm ⟨Q, hQ⟩ (fun h => hQ0 (congrArg Subtype.val h))
    exact Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.mpr (hc0 Q hQ hQ0)) this
  · have := hM ⟨P, hP⟩
    simp only [AddSubgroup.coe_zero, hH0.1, norm_one, Real.log_one] at this
    exact Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.mpr (hne P hP)) this

end Formalism.L2.Th1.E
