import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MPFConjTranspose

noncomputable section

open MeasureTheory Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL

theorem normSq_line (γ δ : ℂ) (t : ℝ) :
    Complex.normSq (γ + (t : ℂ) * δ) = Complex.normSq γ + t ^ 2 * Complex.normSq δ + 2 * t * (γ * conj δ).re := by
  rw [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_ofReal, map_mul, Complex.conj_ofReal,
    show γ * ((t : ℂ) * conj δ) = (t : ℂ) * (γ * conj δ) by ring, Complex.re_ofReal_mul]
  ring

section Pos

variable {n r k : ℕ} (ε : Fin n → Bool)

def hJL (x : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun v := hJ ε x v
  map_add' v w := UnitaryIsometries.hJ_add_right ε x v w
  map_smul' a v := by simp [UnitaryIsometries.hJ_smul_right]

theorem hJ_self_pos {x : Fin n → ℂ} (hx : ∀ i, ε i = false → x i = 0) (hx0 : x ≠ 0) : 0 < (hJ ε x x).re := by
  have h : hJ ε x x = ∑ i, ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
    unfold hJ Jm
    simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : ε i = true
    · simp only [hi, if_true, one_mul]
      rw [mul_comm]
      push_cast
      exact Complex.mul_conj' (x i)
    · have : x i = 0 := hx i (by simpa using hi)
      simp [this]
  rw [h, Complex.re_sum]
  simp only [Complex.ofReal_re]
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h'
    push_neg at h'
    exact hx0 (funext h')
  exact Finset.sum_pos' (fun j _ => by positivity) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hi) 2⟩

theorem exists_pos {e : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℝ} (hdim : n = 2 * r + 1 + k) (hk : 1 ≤ k)
    (hsig : (Finset.univ.filter (fun i => ε i = false)).card = r + 1) (hez : ∀ a, hJ ε (e a) z = 0)
    (hzz : hJ ε z z = -(T : ℂ)) (hT : 0 < T) :
    ∃ p, (∀ a, hJ ε (e a) p = 0) ∧ hJ ε z p = 0 ∧ 0 < (hJ ε p p).re := by
  set L : (Fin n → ℂ) →ₗ[ℂ] (Fin r → ℂ) := LinearMap.pi fun a => hJL ε (e a) with hL
  set Q : (Fin n → ℂ) →ₗ[ℂ] ({i // ε i = false} → ℂ) := LinearMap.pi fun i => LinearMap.proj i.1 with hQ
  have hcard : Fintype.card {i // ε i = false} = r + 1 := by
    rw [Fintype.card_subtype]; exact hsig
  have h1 := LinearMap.finrank_range_add_finrank_ker L
  have h2 := LinearMap.finrank_range_add_finrank_ker Q
  have h1r : Module.finrank ℂ (LinearMap.range L) ≤ r := by
    have := Submodule.finrank_le (LinearMap.range L)
    simpa using this
  have h2r : Module.finrank ℂ (LinearMap.range Q) ≤ r + 1 := by
    have := Submodule.finrank_le (LinearMap.range Q)
    simpa [hcard] using this
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker L) (LinearMap.ker Q)
  have h4 : Module.finrank ℂ ↥(LinearMap.ker L ⊔ LinearMap.ker Q) ≤ n := by
    have := Submodule.finrank_le (LinearMap.ker L ⊔ LinearMap.ker Q)
    simpa using this
  simp only [Module.finrank_fin_fun] at h1 h2
  have h5 : LinearMap.ker L ⊓ LinearMap.ker Q ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at h3
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h5
  have hxL : ∀ a, hJ ε (e a) x = 0 := fun a => congrFun (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hx).1) a
  have hxQ : ∀ i, ε i = false → x i = 0 := fun i hi =>
    congrFun (LinearMap.mem_ker.1 (Submodule.mem_inf.1 hx).2) ⟨i, hi⟩
  have hxx := hJ_self_pos ε hxQ hx0
  have hTne : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hT.ne'
  set c : ℂ := hJ ε z x / hJ ε z z with hc
  refine ⟨x - c • z, fun a => ?_, ?_, ?_⟩
  · rw [UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_smul_right, hxL a, hez a, mul_zero, sub_zero]
  · rw [UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_smul_right, hc, hzz]
    field_simp
    ring
  · have hzp : hJ ε z (x - c • z) = 0 := by
      rw [UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_smul_right, hc, hzz]
      field_simp
      ring
    rw [UnitaryIsometries.hJ_sub_left, UnitaryIsometries.hJ_smul_left, hzp, mul_zero, sub_zero, UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_smul_right,
      UnitaryIsometries.hJ_conj ε x z, hc, hzz]
    have e1 : hJ ε z x / -(T : ℂ) * conj (hJ ε z x) = ((-(Complex.normSq (hJ ε z x) / T) : ℝ) : ℂ) := by
      rw [div_mul_eq_mul_div, Complex.mul_conj]
      push_cast
      ring
    rw [e1, Complex.sub_re, Complex.ofReal_re]
    have : 0 ≤ Complex.normSq (hJ ε z x) / T := div_nonneg (Complex.normSq_nonneg _) hT.le
    linarith

theorem exists_rho {e : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ} {T T' : ℝ} (hdim : n = 2 * r + 1 + k)
    (hk : 1 ≤ k) (hsig : (Finset.univ.filter (fun i => ε i = false)).card = r + 1) (hez : ∀ a, hJ ε (e a) z = 0)
    (hzz : hJ ε z z = -(T : ℂ)) (hT : 0 < T) (hT' : 0 < T') :
    ∃ ρ : Matrix (Fin n) (Fin n) ℂ, UnitaryIsometries.IsIsom ε ρ ∧ (∀ a, ρ *ᵥ e a = e a) ∧
      Complex.normSq (hJ ε z (ρ *ᵥ z')) ≠ T * T' := by
  have hTT : 0 < T * T' := mul_pos hT hT'
  by_cases hγ : hJ ε z z' = 0
  · refine ⟨1, UnitaryIsometries.isIsom_one ε, fun a => one_mulVec _, ?_⟩
    rw [one_mulVec, hγ, map_zero]
    exact hTT.ne
  obtain ⟨p, hpe, hpz, hpp⟩ := exists_pos ε hdim hk hsig hez hzz hT
  set π := (hJ ε p p).re with hπ
  have hpR : hJ ε p p = (π : ℂ) := (Complex.conj_eq_iff_re.1 (UnitaryIsometries.hJ_self_conj ε p)).symm
  set s := Real.sqrt (T / π) with hs
  have hs2 : s * s * π = T := by
    rw [hs, Real.mul_self_sqrt (div_nonneg hT.le hpp.le)]
    field_simp
  set p1 : Fin n → ℂ := (s : ℂ) • p with hp1
  have hp1p1 : hJ ε p1 p1 = T := by
    rw [hp1, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, hpR, Complex.conj_ofReal]
    exact_mod_cast (by rw [← hs2]; ring : s * (s * π) = T)
  have hzp1 : hJ ε z p1 = 0 := by rw [hp1, UnitaryIsometries.hJ_smul_right, hpz, mul_zero]
  have hp1z : hJ ε p1 z = 0 := by rw [UnitaryIsometries.hJ_conj, hzp1, map_zero]
  have hep1 : ∀ a, hJ ε (e a) p1 = 0 := fun a => by rw [hp1, UnitaryIsometries.hJ_smul_right, hpe a, mul_zero]

  obtain ⟨u, huu, heu, hzu, huz'⟩ : ∃ u : Fin n → ℂ, hJ ε u u = 0 ∧ (∀ a, hJ ε (e a) u = 0) ∧
      hJ ε z u = -(T : ℂ) ∧ hJ ε u z' ≠ 0 := by
    have hiso : ∀ t : ℂ, t * conj t = 1 → hJ ε (z + t • p1) (z + t • p1) = 0 := by
      intro t ht
      simp only [UnitaryIsometries.hJ_add_left, UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_left, UnitaryIsometries.hJ_smul_right, hzz, hzp1, hp1z,
        hp1p1]
      linear_combination (T : ℂ) * ht
    by_cases hplus : hJ ε (z + (1 : ℂ) • p1) z' ≠ 0
    · refine ⟨z + (1 : ℂ) • p1, hiso 1 (by simp), fun a => ?_, ?_, hplus⟩
      · rw [UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, hez a, hep1 a]; ring
      · rw [UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, hzz, hzp1]; ring
    · refine ⟨z + (-1 : ℂ) • p1, hiso (-1) (by simp), fun a => ?_, ?_, ?_⟩
      · rw [UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, hez a, hep1 a]; ring
      · rw [UnitaryIsometries.hJ_add_right, UnitaryIsometries.hJ_smul_right, hzz, hzp1]; ring
      · push_neg at hplus
        intro hminus
        apply hγ
        rw [UnitaryIsometries.hJ_add_left, UnitaryIsometries.hJ_smul_left] at hplus hminus
        simp only [map_one, map_neg, one_mul, neg_mul] at hplus hminus
        linear_combination (hplus + hminus) / 2
  have hue : ∀ a, hJ ε u (e a) = 0 := fun a => by rw [UnitaryIsometries.hJ_conj, heu a, map_zero]
  set δ : ℂ := Complex.I * hJ ε u z' * T with hδ
  have hδ0 : δ ≠ 0 := mul_ne_zero (mul_ne_zero Complex.I_ne_zero huz') (Complex.ofReal_ne_zero.2 hT.ne')
  have hval : ∀ t : ℝ, hJ ε z (UnitaryIsometries.tv ε u (Complex.I * t) *ᵥ z') = hJ ε z z' + (t : ℂ) * δ := by
    intro t
    rw [UnitaryIsometries.tv_apply, UnitaryIsometries.hJ_sub_right, UnitaryIsometries.hJ_smul_right, hzu, hδ]
    ring
  have hsq : ∀ t : ℝ, Complex.normSq (hJ ε z z' + (t : ℂ) * δ) =
      Complex.normSq (hJ ε z z') + t ^ 2 * Complex.normSq δ + 2 * t * (hJ ε z z' * conj δ).re :=
    fun t => normSq_line _ _ t
  have hex : ∃ t : ℝ, Complex.normSq (hJ ε z z' + (t : ℂ) * δ) ≠ T * T' := by
    by_contra hall
    push_neg at hall
    have e0 := hall 0
    have e1 := hall 1
    have e2 := hall 2
    rw [hsq] at e0 e1 e2
    have : Complex.normSq δ = 0 := by nlinarith
    exact hδ0 (Complex.normSq_eq_zero.1 this)
  obtain ⟨t, ht⟩ := hex
  refine ⟨UnitaryIsometries.tv ε u (Complex.I * t), UnitaryIsometries.tv_isIsom ε u ?_, fun a => UnitaryIsometries.tv_fix ε u _ (hue a), ?_⟩
  · rw [huu, mul_zero, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  · rw [hval]
    exact ht

end Pos

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames
