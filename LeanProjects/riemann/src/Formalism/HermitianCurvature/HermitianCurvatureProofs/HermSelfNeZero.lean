import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermZeroOfTrace

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem herm_self_ne_zero {z : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) : herm (Hpk k r) z z ≠ 0 := by
  intro h
  rw [Tz, h] at hT
  simp at hT

theorem herm_proj_zero (x z : Fin (2 * r + k + 1) → ℂ) (hc : herm (Hpk k r) z z ≠ 0) :
    herm (Hpk k r) (x - (herm (Hpk k r) x z / herm (Hpk k r) z z) • z) z = 0 := by
  rw [herm_sub_left, herm_smul_left]
  field_simp
  ring

theorem coreW {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (ξ : B.Mat k r)
    (h1 : ∀ u, inWb k r u → inWb k r (ξ *ᵥ u))
    (h2 : ∀ u v, inWb k r u → inWb k r v → herm (Hpk k r) (ξ *ᵥ u) v = -herm (Hpk k r) u (ξ *ᵥ v))
    (h3 : ∀ u v, inWb k r u → inWb k r v → herm (Hpk k r) u z = 0 → herm (Hpk k r) v z = 0 →
      herm (Hpk k r) (ξ *ᵥ u) v = 0)
    (N : ℕ) (h4 : ∀ u, inWb k r u → (ξ ^ N) *ᵥ u = 0) :
    ∀ u, inWb k r u → ξ *ᵥ u = 0 := by
  set c := herm (Hpk k r) z z with hcdef
  have hc0 : c ≠ 0 := herm_self_ne_zero hT

  have stepA : ∀ w, inWb k r w → herm (Hpk k r) w z = 0 →
      ξ *ᵥ w = (herm (Hpk k r) (ξ *ᵥ w) z / c) • z := by
    intro w hw hwz
    set y := ξ *ᵥ w - (herm (Hpk k r) (ξ *ᵥ w) z / c) • z with hydef
    have hy : inWb k r y := inWb_sub (h1 w hw) (inWb_smul _ hz)
    have hyz : herm (Hpk k r) y z = 0 := herm_proj_zero _ _ hc0
    have hyy : herm (Hpk k r) y y = 0 := by
      have e1 : herm (Hpk k r) (ξ *ᵥ w) y = 0 := h3 w y hw hy hwz hyz
      have e2 : herm (Hpk k r) z y = 0 := by rw [herm_swap, hyz, star_zero]
      calc herm (Hpk k r) y y
          = herm (Hpk k r) (ξ *ᵥ w) y - (herm (Hpk k r) (ξ *ᵥ w) z / c) * herm (Hpk k r) z y := by
            conv_lhs => rw [hydef]
            rw [herm_sub_left, herm_smul_left]
        _ = 0 := by rw [e1, e2]; ring
    have : y = 0 := wb_definite hz hT hy hyz (by rw [hyy]; simp)
    exact sub_eq_zero.1 this
  set μ := herm (Hpk k r) (ξ *ᵥ z) z / c with hμ
  set b := ξ *ᵥ z - μ • z with hbdef
  have hb : inWb k r b := inWb_sub (h1 z hz) (inWb_smul _ hz)
  have hbz : herm (Hpk k r) b z = 0 := herm_proj_zero _ _ hc0
  have hξz : ξ *ᵥ z = μ • z + b := by rw [hbdef]; abel

  have stepB : ∀ w, inWb k r w → herm (Hpk k r) w z = 0 →
      ξ *ᵥ w = (-(herm (Hpk k r) w b) / c) • z := by
    intro w hw hwz
    rw [stepA w hw hwz, h2 w z hw hz, hξz, herm_add_right, herm_smul_right, hwz]
    congr 1
    ring
  have hξb : ξ *ᵥ b = (-(herm (Hpk k r) b b) / c) • z := stepB b hb hbz
  have hNz := h4 z hz

  have hb0 : b = 0 := by
    by_contra hb0
    have hbb : herm (Hpk k r) b b ≠ 0 := by
      intro h
      exact hb0 (wb_definite hz hT hb hbz (by rw [h]; simp))
    set l := -(herm (Hpk k r) b b) / c with hl
    have hl0 : l ≠ 0 := div_ne_zero (neg_ne_zero.2 hbb) hc0
    let f : ℕ → ℂ × ℂ := fun m => Nat.rec (motive := fun _ => ℂ × ℂ) (1, 0)
      (fun _ pq => (μ * pq.1 + l * pq.2, pq.1)) m
    have hf0 : f 0 = (1, 0) := rfl
    have hfs : ∀ m, f (m + 1) = (μ * (f m).1 + l * (f m).2, (f m).1) := fun m => rfl
    have hpow : ∀ m, (ξ ^ m) *ᵥ z = (f m).1 • z + (f m).2 • b := by
      intro m
      induction m with
      | zero => rw [hf0, pow_zero, one_mulVec]; simp
      | succ m ih =>
        rw [pow_succ', ← mulVec_mulVec, ih, mulVec_add, mulVec_smul, mulVec_smul, hξz, hξb, hfs]
        module
    rw [hpow] at hNz
    have hp : (f N).1 = 0 := by
      have := congrArg (fun x => herm (Hpk k r) x z) hNz
      simp only [herm_add_left, herm_smul_left, hbz, herm_zero_left, mul_zero, add_zero] at this
      exact (mul_eq_zero.1 this).resolve_right hc0
    have hq : (f N).2 = 0 := by
      rw [hp, zero_smul, zero_add] at hNz
      exact (smul_eq_zero.1 hNz).resolve_right hb0
    have hnz : ∀ m, (f m).1 ≠ 0 ∨ (f m).2 ≠ 0 := by
      intro m
      induction m with
      | zero => left; rw [hf0]; exact one_ne_zero
      | succ m ih =>
        by_contra hcon
        push Not at hcon
        rw [hfs] at hcon
        obtain ⟨e1, e2⟩ := hcon
        simp only at e1 e2
        rw [e2, mul_zero, zero_add] at e1
        have : (f m).2 = 0 := (mul_eq_zero.1 e1).resolve_left hl0
        rcases ih with h | h
        · exact h e2
        · exact h this
    rcases hnz N with h | h
    · exact h hp
    · exact h hq

  have hξz' : ξ *ᵥ z = μ • z := by rw [hξz, hb0, add_zero]
  have hpow2 : ∀ m, (ξ ^ m) *ᵥ z = μ ^ m • z := by
    intro m
    induction m with
    | zero => rw [pow_zero, one_mulVec, pow_zero, one_smul]
    | succ m ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hξz', smul_smul, pow_succ]
  rw [hpow2] at hNz
  have hμ0 : μ = 0 := by
    have := congrArg (fun x => herm (Hpk k r) x z) hNz
    simp only [herm_smul_left, herm_zero_left] at this
    exact pow_eq_zero_iff'.1 ((mul_eq_zero.1 this).resolve_right hc0) |>.1
  have hξz0 : ξ *ᵥ z = 0 := by rw [hξz', hμ0, zero_smul]
  intro u hu
  set α := herm (Hpk k r) u z / c
  have hu' : inWb k r (u - α • z) := inWb_sub hu (inWb_smul _ hz)
  have hu'z : herm (Hpk k r) (u - α • z) z = 0 := herm_proj_zero _ _ hc0
  have e : u = α • z + (u - α • z) := by abel
  rw [e, mulVec_add, mulVec_smul, hξz0, stepB _ hu' hu'z, hb0, herm_zero_right]
  simp

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
