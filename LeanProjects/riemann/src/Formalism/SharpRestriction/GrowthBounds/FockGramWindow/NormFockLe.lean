import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.LvlDef
import Formalism.SharpRestriction.GrowthBounds.FockGramWindow.GramWindow2Proved
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.FinPosEqCast
import Formalism.MahlerMeasure.FinalM

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset Formalism.GM Formalism.GM.M.PhiIntegrality

section Ops

variable {p : ℕ} [hp : Fact p.Prime] {σ : Type} {r : ℕ}

theorem one_le_p : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le

theorem bnd_Xl (w e : Fin r → σ) (J l : ℕ) (hl : l ≤ J) (B : ℝ) (hB : 0 ≤ B) (u : MvPolynomial σ ℚ_[p])
    (hu : Bnd B u) :
    Bnd (B * (p : ℝ) ^ ((r + 1) * Nat.log p J))
      ((((l.factorial : ℚ_[p]) ^ 2 * (J.choose l : ℚ_[p]))⁻¹) • ((tieE w e ^ l) ((tieF w e ^ l) u))) := by
  have hp1 : (1 : ℝ) ≤ p := one_le_p
  set Mc : ℝ := (p : ℝ) ^ (Nat.log p J) with hMc
  have hM1 : 1 ≤ Mc := one_le_pow₀ hp1
  have hM : ∀ j ≤ J, ∀ k ≤ j, ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ Mc := fun j hj k hk =>
    (norm_choose_inv_le j k hk).trans (pow_le_pow_right₀ hp1 (Nat.log_mono_right hj))
  let D : Fin r → (MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]) := fun c =>
    (pderiv (w c) : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ∘ₗ
      (pderiv (e c)).toLinearMap
  have hcomm : ∀ a b, Commute (D a) (D b) := by
    intro a b
    simp only [D, ← Module.End.mul_eq_comp]
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_) <;>
      exact commute_pderiv _ _
  have hF := contr_Fsum D hcomm (fun a k => contr_D _ _ k) hM1 J hM Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at hF
  have hFeq : Formalism.GM.tieF (k := ℚ_[p]) w e = ∑ c ∈ Finset.univ, D c := rfl
  have h1 := hF l hl B hB u hu
  rw [← hFeq] at h1
  have h2 := contr_pow zero_le_one (contr_E (p := p) w e) l _ (by positivity) _ h1
  have eq : (((l.factorial : ℚ_[p]) ^ 2 * (J.choose l : ℚ_[p]))⁻¹) • ((tieE w e ^ l) ((tieF w e ^ l) u)) =
      (((J.choose l : ℕ) : ℚ_[p])⁻¹) • ((tieE w e ^ l) (((((l.factorial : ℚ_[p]) ^ 2))⁻¹ • (tieF w e ^ l)) u)) := by
    rw [LinearMap.smul_apply, map_smul, smul_smul, mul_inv, mul_comm]
  rw [eq]
  refine bnd_mono (bnd_smul _ h2) ?_
  have hA := hM J le_rfl l hl
  calc ‖(((J.choose l : ℕ) : ℚ_[p]))⁻¹‖ * (B * Mc ^ r * 1 ^ l) ≤ Mc * (B * Mc ^ r * 1 ^ l) := by gcongr
    _ = B * (p : ℝ) ^ ((r + 1) * Nat.log p J) := by
        rw [hMc, one_pow, mul_one, ← pow_mul, mul_comm ((p : ℝ) ^ Nat.log p J), mul_assoc, ← pow_add]
        congr 2; ring

theorem bnd_pow_iff (k : ℕ) (u : MvPolynomial σ ℚ_[p]) :
    Bnd ((p : ℝ) ^ k) u ↔ M.IsIntegral' p (((p : ℚ_[p]) ^ k) • u) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one one_le_p
  have hk : (0 : ℝ) < (p : ℝ) ^ k := pow_pos hp0 k
  refine forall_congr' fun m => ?_
  rw [coeff_smul, smul_eq_mul, norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ hk, mul_one]

theorem bnd_phi (w e : Fin r → σ) (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (hr : 1 ≤ r) (o n z Λ : ℕ) (hΛ : Nat.log p (o + n + r + z) + 1 ≤ Λ) (k : ℕ) (u : MvPolynomial σ ℚ_[p])
    (hu : Bnd ((p : ℝ) ^ k) u) : Bnd ((p : ℝ) ^ (k + (r + 1) * Λ)) (tiePhi w e o n z u) := by
  have h1 := (bnd_pow_iff k u).1 hu
  have h2 := Formalism.GM.projectorIntegral p σ r w e hw he hwe hr o n z _ h1
  rw [map_smul, smul_smul, ← pow_add] at h2
  refine bnd_mono ((bnd_pow_iff _ _).2 h2) (pow_le_pow_right₀ one_le_p ?_)
  have := Nat.mul_le_mul_left (r + 1) hΛ
  omega

theorem bnd_foldr {ι : Type} (φ : ι → MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]) (c : ℕ) (l : List ι)
    (h : ∀ i ∈ l, ∀ k u, Bnd ((p : ℝ) ^ k) u → Bnd ((p : ℝ) ^ (k + c)) (φ i u)) (k : ℕ) (u : MvPolynomial σ ℚ_[p])
    (hu : Bnd ((p : ℝ) ^ k) u) :
    Bnd ((p : ℝ) ^ (k + l.length * c)) ((l.foldr (fun i acc => φ i ∘ₗ acc) LinearMap.id) u) := by
  induction l with
  | nil => simpa using hu
  | cons i l ih =>
    simp only [List.foldr_cons, LinearMap.comp_apply, List.length_cons]
    have h1 := ih (fun i' hi' => h i' (List.mem_cons_of_mem _ hi'))
    have h2 := h i List.mem_cons_self _ _ h1
    rw [show k + (l.length + 1) * c = k + l.length * c + c by ring]
    exact h2

theorem norm_fock_le (U v : MvPolynomial σ ℚ_[p]) (dF : ℕ) (hdF : dF ≠ 0) (k E : ℕ) (hU : Bnd ((p : ℝ) ^ k) U)
    (hv : Bnd 1 v)
    (hval : ∀ m ∈ v.support, padicValNat p dF ≤ padicValNat p (m.prod fun _ i => i.factorial) + E) :
    ‖M.fockK U v / (dF : ℚ_[p])‖ ≤ (p : ℝ) ^ (k + E) := by
  have hp1 : (1 : ℝ) ≤ p := one_le_p
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp1
  unfold M.fockK
  rw [Finset.sum_div]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun m _ => ?_
  by_cases hm : m ∈ v.support
  · have hne : (m.prod fun _ i => i.factorial) ≠ 0 := by
      rw [Finsupp.prod]
      exact Finset.prod_ne_zero_iff.2 fun i _ => Nat.factorial_ne_zero _
    have hcast : (m.prod fun _ j => (j.factorial : ℚ_[p])) = (((m.prod fun _ i => i.factorial) : ℕ) : ℚ_[p]) := by
      simp [Finsupp.prod]
    rw [hcast, norm_div, norm_mul, norm_mul, Formalism.GM.MeanGammaLemmas.norm_nat p _ hne, Formalism.GM.MeanGammaLemmas.norm_nat p _ hdF,
      mul_div_assoc, ← zpow_sub₀ hp0.ne']
    have h3 : (p : ℝ) ^ (-(padicValNat p (m.prod fun _ i => i.factorial) : ℤ) - -(padicValNat p dF : ℤ)) ≤
        (p : ℝ) ^ E := by
      rw [← zpow_natCast]
      apply zpow_le_zpow_right₀ hp1
      have := hval m hm
      omega
    calc ‖coeff m U‖ * ‖coeff m v‖ *
          (p : ℝ) ^ (-(padicValNat p (m.prod fun _ i => i.factorial) : ℤ) - -(padicValNat p dF : ℤ))
        ≤ (p : ℝ) ^ k * 1 * (p : ℝ) ^ E := by
          gcongr
          · exact hU m
          · exact hv m
      _ = (p : ℝ) ^ (k + E) := by rw [mul_one, pow_add]
  · rw [notMem_support_iff.1 hm, mul_zero, zero_mul, zero_div, norm_zero]
    positivity

end Ops

end Formalism.MainNotions.G.GramWindowAlt

end
