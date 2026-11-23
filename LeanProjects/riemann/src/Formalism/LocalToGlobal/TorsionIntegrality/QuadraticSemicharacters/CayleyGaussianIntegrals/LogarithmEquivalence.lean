import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.SemiCharBasic
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.LineTransport

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

namespace Inv

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem altE_swap {H : Sesq V} (hH : IsHerm H) (x y : V) : altE H y x = -altE H x y := by
  show (H y x).im = -(H x y).im
  rw [hH x y, Complex.conj_im]

theorem altE_add_left (H : Sesq V) (x x' y : V) : altE H (x + x') y = altE H x y + altE H x' y := by
  simp only [Formalism.L2.Th1.H.altE, map_add, LinearMap.add_apply, Complex.add_im]

theorem altE_neg_right (H : Sesq V) (x y : V) : altE H x (-y) = -altE H x y := by
  simp only [Formalism.L2.Th1.H.altE, map_neg, Complex.neg_im]

theorem exp_two_pi_int (m : ℤ) :
    Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (((m : ℝ)) : ℂ)) = 1 := by
  have h : -(2 * (Real.pi : ℂ)) * Complex.I * (((m : ℝ)) : ℂ) = ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

theorem int_of_exp_two_pi {t : ℝ}
    (h : Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (t : ℂ)) = 1) : ∃ m : ℤ, t = (m : ℝ) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨-n, ?_⟩
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have h3 : ((t : ℝ) : ℂ) = (((-n : ℤ) : ℝ) : ℂ) := by
    apply mul_right_cancel₀ h2
    push_cast
    linear_combination -hn
  exact_mod_cast h3

theorem sum_reps {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S) (g : V → ℂ)
    (hg : ∀ y ∈ S, y ∉ Λ₁ → g y = 0) : ∃ y₀ ∈ S, y₀ ∈ Λ₁ ∧ ∑ y ∈ S, g y = g y₀ := by
  obtain ⟨_, hdist, hcov⟩ := hS
  obtain ⟨y₀, hy₀S, hy₀⟩ := hcov 0 (zero_mem _)
  have hy₀' : y₀ ∈ Λ₁ := by simpa using Λ₁.neg_mem hy₀
  refine ⟨y₀, hy₀S, hy₀', ?_⟩
  exact Finset.sum_eq_single y₀
    (fun y hyS hne => hg y hyS (fun hy => hne (hdist y hyS y₀ hy₀S (Λ₁.sub_mem hy hy₀'))))
    (fun h => absurd hy₀S h)

theorem opU_const_mul (H : Sesq V) (x : V) (c : ℂ) (G : V → ℂ) (z : V) :
    opU H x (fun v => c * G v) z = c * opU H x G z := by
  simp only [Formalism.L2.Th1.H.opU]
  ring

theorem opU_finset_sum {ι : Type} (H : Sesq V) (x : V) (S : Finset ι) (G : ι → V → ℂ) (z : V) :
    opU H x (fun v => ∑ i ∈ S, G i v) z = ∑ i ∈ S, opU H x (G i) z := by
  simp only [Formalism.L2.Th1.H.opU, Finset.sum_mul]

private theorem finsum_const_mul' {ι : Type*} (c : ℂ) (f : ι → ℂ) : ∑ᶠ i, c * f i = c * ∑ᶠ i, f i := by
  have h := smul_finsum c f
  simpa only [smul_eq_mul] using h.symm

private theorem hermitian_character_exp_add_left (H : Formalism.L2.Th1.H.Sesq V) (u w y : V) :
    Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (Formalism.L2.Th1.H.altE H (u + w) y : ℂ)) = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (Formalism.L2.Th1.H.altE H u y : ℂ)) * Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (Formalism.L2.Th1.H.altE H w y : ℂ)) := by
  rw [altE_add_left, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem hermitian_character_exp_eq_one_of_mem_dual_lattice {H : Formalism.L2.Th1.H.Sesq V} (hH : Formalism.L2.Th1.H.IsHerm H) {Λ : AddSubgroup V} {y : V}
    (hy : y ∈ Formalism.L2.Th1.H.dualLat H Λ) {d : V} (hd : d ∈ Λ) : Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (Formalism.L2.Th1.H.altE H d y : ℂ)) = 1 := by
  have hy' : ∀ x ∈ Λ, ∃ m : ℤ, Formalism.L2.Th1.H.altE H y x = m := hy
  obtain ⟨m, hm⟩ := hy' d hd
  have h : Formalism.L2.Th1.H.altE H d y = ((-m : ℤ) : ℝ) := by
    rw [altE_swap hH y d, hm, Int.cast_neg]
  rw [h]
  exact exp_two_pi_int (-m)

private theorem sum_char_isReps_eq_zero_of_nontrivial {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (hS : Formalism.L2.Th1.H.IsReps Λ₂ Λ₁ S)
    (χ : V → ℂ) (hadd : ∀ u w, χ (u + w) = χ u * χ w) (htriv : ∀ d ∈ Λ₂, χ d = 1)
    {x' : V} (hx' : x' ∈ Λ₁) (hne : χ x' ≠ 1) : ∑ x ∈ S, χ x = 0 := by
  classical
  have : Nonempty V := ⟨0⟩
  obtain ⟨hsub, hdist, hcov⟩ := hS
  choose! rep hrepS hrepd using hcov
  have hrep : ∀ v ∈ Λ₁, χ (rep v) = χ v := by
    intro v hv
    have h := hadd (rep v) (v - rep v)
    rw [show rep v + (v - rep v) = v by abel, htriv _ (hrepd v hv), mul_one] at h
    exact h.symm
  have hperm : ∑ x ∈ S, χ (rep (x + x')) = ∑ x ∈ S, χ x := by
    refine Finset.sum_nbij' (i := fun x => rep (x + x')) (j := fun x => rep (x - x')) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      exact hrepS _ (Λ₁.add_mem (hsub a ha) hx')
    · intro a ha
      exact hrepS _ (Λ₁.sub_mem (hsub a ha) hx')
    · intro a ha
      have h1 : a + x' ∈ Λ₁ := Λ₁.add_mem (hsub a ha) hx'
      have h2 : rep (a + x') - x' ∈ Λ₁ := Λ₁.sub_mem (hsub _ (hrepS _ h1)) hx'
      show rep (rep (a + x') - x') = a
      refine hdist _ (hrepS _ h2) a ha ?_
      have hmem := Λ₂.neg_mem (Λ₂.add_mem (hrepd _ h2) (hrepd _ h1))
      convert hmem using 1
      abel
    · intro a ha
      have h1 : a - x' ∈ Λ₁ := Λ₁.sub_mem (hsub a ha) hx'
      have h2 : rep (a - x') + x' ∈ Λ₁ := Λ₁.add_mem (hsub _ (hrepS _ h1)) hx'
      show rep (rep (a - x') + x') = a
      refine hdist _ (hrepS _ h2) a ha ?_
      have hmem := Λ₂.neg_mem (Λ₂.add_mem (hrepd _ h2) (hrepd _ h1))
      convert hmem using 1
      abel
    · intro a _
      rfl
  have hshift : ∑ x ∈ S, χ (rep (x + x')) = χ x' * ∑ x ∈ S, χ x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hrep _ (Λ₁.add_mem (hsub x hx) hx'), hadd, mul_comm]
  have h0 : (1 - χ x') * ∑ x ∈ S, χ x = 0 := by
    rw [sub_mul, one_mul, ← hshift, hperm, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (sub_eq_zero.mp h).symm hne
  · exact h

private theorem inv_sqrt_mul_inv_sqrt_mul_natCast_mul {n : ℕ} (hn : n ≠ 0) (w : ℂ) :
    ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ * (((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ * ((n : ℂ) * w)) = w := by
  have hs : ((Real.sqrt (n : ℝ) : ℝ) : ℂ) * ((Real.sqrt (n : ℝ) : ℝ) : ℂ) = (n : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have hne : ((Real.sqrt (n : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)))
  rw [← hs, show ∀ s : ℂ, s⁻¹ * (s⁻¹ * (s * s * w)) = (s⁻¹ * s) * (s⁻¹ * s) * w from fun s => by ring,
    inv_mul_cancel₀ hne, one_mul, one_mul]

theorem inter_smul (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ : AddSubgroup V) (c : ℂ) (F : V → ℂ) :
    inter H α Λ₁ Λ₂ (c • F) = c • inter H α Λ₁ Λ₂ F := by
  funext z
  simp only [Formalism.L2.Th1.H.inter, Pi.smul_apply, smul_eq_mul]
  rw [mul_left_comm c]
  congr 1
  rw [← finsum_const_mul']
  refine finsum_congr fun q => ?_
  simp only [Formalism.L2.Th1.H.opU, Pi.smul_apply, smul_eq_mul]
  ring

theorem inter_zero (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ : AddSubgroup V) :
    inter H α Λ₁ Λ₂ 0 = 0 := by
  funext z
  simp [Formalism.L2.Th1.H.inter, Formalism.L2.Th1.H.opU]

end Inv

open Inv

theorem characterSum : CharSum := by
  intro V _ _ H hH Λ₁ Λ₂ h₁ h₂ S hS y hy
  have h₁' : dualLat H Λ₁ = Λ₁ := h₁
  have h₂' : dualLat H Λ₂ = Λ₂ := h₂
  have hy₂ : y ∈ dualLat H Λ₂ := by rw [h₂']; exact hy
  by_cases hy₁ : y ∈ Λ₁
  · rw [if_pos hy₁]
    have hy₁' : y ∈ dualLat H Λ₁ := by rw [h₁']; exact hy₁
    rw [Finset.sum_congr rfl fun x hx => _root_.Formalism.L2.Th1.H.Inv.hermitian_character_exp_eq_one_of_mem_dual_lattice hH hy₁' (hS.1 x hx)]
    simp
  · rw [if_neg hy₁]
    have hy₁' : y ∉ dualLat H Λ₁ := by rw [h₁']; exact hy₁
    have hx' : ∃ x' ∈ Λ₁, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x' y : ℂ)) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      apply hy₁'
      show ∀ x ∈ Λ₁, ∃ m : ℤ, altE H y x = m
      intro x hx
      obtain ⟨m, hm⟩ := Formalism.L2.Th1.H.Inv.int_of_exp_two_pi (hcon x hx)
      exact ⟨-m, by rw [Formalism.L2.Th1.H.Inv.altE_swap hH x y, hm, Int.cast_neg]⟩
    obtain ⟨x', hx'Λ, hne⟩ := hx'
    exact _root_.Formalism.L2.Th1.H.Inv.sum_char_isReps_eq_zero_of_nontrivial hS (fun v => Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H v y : ℂ))) (fun u w => _root_.Formalism.L2.Th1.H.Inv.hermitian_character_exp_add_left H u w y)
      (fun d hd => _root_.Formalism.L2.Th1.H.Inv.hermitian_character_exp_eq_one_of_mem_dual_lattice hH hy₂ hd) hx'Λ hne

theorem IndexEq_of (hc : CharSum) (hr : RepsExist) : IndexEq := by
  intro V _ _ H hH Λ₁ Λ₂ h₁ h₂ h12 h21
  obtain ⟨⟨S₂, hS₂⟩, hcard₂⟩ := hr V Λ₁ Λ₂ h12
  obtain ⟨⟨S₁, hS₁⟩, hcard₁⟩ := hr V Λ₂ Λ₁ h21
  rw [← hcard₂ S₂ hS₂, ← hcard₁ S₁ hS₁]
  have hA : ∑ y ∈ S₂, ∑ x ∈ S₁, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x y : ℂ)) = (S₁.card : ℂ) := by
    obtain ⟨y₀, hy₀S, hy₀, hsum⟩ := Formalism.L2.Th1.H.Inv.sum_reps hS₂ (fun y => ∑ x ∈ S₁, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x y : ℂ))) (by
      intro y hy hyn
      rw [hc V H hH Λ₁ Λ₂ h₁ h₂ S₁ hS₁ y (hS₂.1 y hy), if_neg hyn])
    rw [hsum, hc V H hH Λ₁ Λ₂ h₁ h₂ S₁ hS₁ y₀ (hS₂.1 y₀ hy₀S), if_pos hy₀]
  have hB : ∑ x ∈ S₁, ∑ y ∈ S₂, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H y (-x) : ℂ)) = (S₂.card : ℂ) := by
    obtain ⟨x₀, hx₀S, hx₀, hsum⟩ := Formalism.L2.Th1.H.Inv.sum_reps hS₁ (fun x => ∑ y ∈ S₂, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H y (-x) : ℂ))) (by
      intro x hx hxn
      rw [hc V H hH Λ₂ Λ₁ h₂ h₁ S₂ hS₂ (-x) (Λ₁.neg_mem (hS₁.1 x hx)),
        if_neg (fun h => hxn (by simpa using Λ₂.neg_mem h))])
    rw [hsum, hc V H hH Λ₂ Λ₁ h₂ h₁ S₂ hS₂ (-x₀) (Λ₁.neg_mem (hS₁.1 x₀ hx₀S)), if_pos (Λ₂.neg_mem hx₀)]
  have key : (S₁.card : ℂ) = (S₂.card : ℂ) := by
    rw [← hA, ← hB, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Formalism.L2.Th1.H.Inv.altE_neg_right, Formalism.L2.Th1.H.Inv.altE_swap hH a b, neg_neg]
  exact_mod_cast key.symm

theorem InterInv_of (hcomm : OpUComm) (hreps : InterReps) (hfix : InterFixed) (hr : RepsExist) :
    InterInv := by
  intro V _ _ H hH Λ₁ Λ₂ α h₁ h₂ hα₁ hα₂ h12 h21 F hF z
  have hidx : relIdx Λ₁ Λ₂ = relIdx Λ₂ Λ₁ :=
    IndexEq_of characterSum hr V H hH Λ₁ Λ₂ h₁ h₂ h12 h21
  obtain ⟨⟨S₂, hS₂⟩, -⟩ := hr V Λ₁ Λ₂ h12
  obtain ⟨⟨S₁, hS₁⟩, hcard₁⟩ := hr V Λ₂ Λ₁ h21
  have hF' : ∀ x ∈ Λ₁, ∀ w, α x * opU H x F w = F w := hF
  have hG := hfix V H hH Λ₁ Λ₂ α hα₂ h12 F hF
  have hIF : inter H α Λ₁ Λ₂ F = fun v =>
      ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹ * ∑ y ∈ S₂, α y * opU H y F v := by
    funext v
    exact hreps V H hH Λ₁ Λ₂ α hα₂ F hF S₂ hS₂ v
  have hfixop : ∀ x ∈ Λ₁, ∀ y, α x * opU H y (opU H x F) z = opU H y F z := by
    intro x hx y
    have hfun : (fun v => α x * opU H x F v) = F := funext (hF' x hx)
    rw [← Formalism.L2.Th1.H.Inv.opU_const_mul, hfun]
  have hterm : ∀ x ∈ Λ₁, ∀ y, α x * (α y * opU H x (opU H y F) z)
      = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x y : ℂ)) * (α y * opU H y F z) := by
    intro x hx y
    rw [(hcomm V H hH F z).2 x y, ← hfixop x hx y]
    ring
  have e1 : ∀ x ∈ S₁, α x * opU H x (fun v =>
        ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹ * ∑ y ∈ S₂, α y * opU H y F v) z
      = ((Real.sqrt (relIdx Λ₁ Λ₂) : ℝ) : ℂ)⁻¹ * ∑ y ∈ S₂, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x y : ℂ)) * (α y * opU H y F z) := by
    intro x hx
    rw [Formalism.L2.Th1.H.Inv.opU_const_mul, Formalism.L2.Th1.H.Inv.opU_finset_sum, mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Formalism.L2.Th1.H.Inv.opU_const_mul]
    exact hterm x (hS₁.1 x hx) y
  rw [hreps V H hH Λ₂ Λ₁ α hα₁ _ hG S₁ hS₁ z, sumU, hIF, Finset.sum_congr rfl e1,
    ← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.sum_mul]
  obtain ⟨y₀, hy₀S, hy₀, hsum⟩ := Formalism.L2.Th1.H.Inv.sum_reps hS₂
    (fun y => (∑ x ∈ S₁, Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H x y : ℂ))) * (α y * opU H y F z)) (by
      intro y hy hyn
      rw [characterSum V H hH Λ₁ Λ₂ h₁ h₂ S₁ hS₁ y (hS₂.1 y hy), if_neg hyn, zero_mul])
  rw [hsum, characterSum V H hH Λ₁ Λ₂ h₁ h₂ S₁ hS₁ y₀ (hS₂.1 y₀ hy₀S), if_pos hy₀, hF' y₀ hy₀ z,
    hcard₁ S₁ hS₁, hidx]
  exact _root_.Formalism.L2.Th1.H.Inv.inv_sqrt_mul_inv_sqrt_mul_natCast_mul h21 (F z)

theorem LineTransport_of (hinv : InterInv) (hth : InterTh) : LineTransport := by
  intro V _ _ _ H hH Λ₁ Λ₂ α h₁ h₂ hα₁ hα₂ h12 h21 θ₁ hθ₁ hne hline
  have hθ' : AnalyticOnNhd ℂ θ₁ Set.univ ∧ θ₁ ∈ fixedBy H α Λ₁ := hθ₁
  refine ⟨fun h0 => hne ?_, fun F hF => ?_⟩
  · funext z
    have h := hinv V H hH Λ₁ Λ₂ α h₁ h₂ hα₁ hα₂ h12 h21 θ₁ hθ'.2 z
    rw [h0, Formalism.L2.Th1.H.Inv.inter_zero] at h
    simpa using h.symm
  · have hF' : AnalyticOnNhd ℂ F Set.univ ∧ F ∈ fixedBy H α Λ₂ := hF
    obtain ⟨c, hc⟩ := hline _ (hth V H hH Λ₂ Λ₁ α hα₁ h21 F hF)
    refine ⟨c, funext fun z => ?_⟩
    rw [← hinv V H hH Λ₂ Λ₁ α h₂ h₁ hα₂ hα₁ h21 h12 F hF'.2 z, hc, Formalism.L2.Th1.H.Inv.inter_smul]

end Formalism.L2.Th1.H
