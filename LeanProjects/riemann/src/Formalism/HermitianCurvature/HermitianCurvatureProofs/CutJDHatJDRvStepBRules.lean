import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRStepB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVRules
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVGrp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVCoef

open Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.StepB

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx3 Formalism.FourierDecayAlt.P.WeylCellAction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem exists_wCell_eq_wCell_succ_mul_tail_factor (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (b : Fin r) : ∀ n : ℕ, ∀ i : Fin (r + 1), i.val = b.val + 1 + n →
    ∃ T : Mx k r, wCell k r i c = wCell k r b.succ c * T ∧ T ∈ Glev k r b.succ ∧
      (∀ a : Fin r, i.val ≤ a.val → T *ᵥ bvec (eI k r a) = bvec (eI k r a)) ∧
      (∀ a : Fin r, b.val < a.val → a.val < i.val → T *ᵥ bvec (esI k r a) = (star (c a))⁻¹ • bvec (eI k r a))
  | 0, i, hi => by
    have : i = b.succ := Fin.ext (by simp [hi])
    subst this
    refine ⟨1, by simp, glev_one _, fun a _ => by simp, fun a h1 h2 => ?_⟩
    simp at h2
    omega
  | n + 1, i, hi => by
    have hl : b.val + 1 + n < r := by have := i.isLt; omega
    set l : Fin r := ⟨b.val + 1 + n, hl⟩ with hldef
    have hil : i = l.succ := Fin.ext (by simp [l, hi]; omega)
    subst hil
    obtain ⟨T, hT, hTG, hTe, hTs⟩ := exists_wCell_eq_wCell_succ_mul_tail_factor c hc b n l.castSucc (by simp [l])
    have hw := (Formalism.FourierDecayAlt.P.weyl_level_element_properties k r l (c l) (hc l)).1
    refine ⟨T * w1 k r l (c l), ?_, ?_, ?_, ?_⟩
    · rw [Formalism.FourierDecayAlt.P.Qx6.wCell_succ, hT, Matrix.mul_assoc]
    · exact glev_mul hTG (glev_mono (by rw [Fin.le_def]; simp [l]) hw)
    · intro a ha
      have ha' : l.val + 1 ≤ a.val := by simpa using ha
      have h1 : eI k r a ≠ eI k r l := by simp [eI, Fin.ext_iff]; omega
      have h2 : eI k r a ≠ esI k r l := by simp [eI, esI, Fin.ext_iff]; have := l.isLt; omega
      rw [← Matrix.mulVec_mulVec, weyl_cell_mulVec_basis, sw_o l h1 h2, dd_o l _ h1 h2, one_smul,
        hTe a (by simp; omega)]
    · intro a ha1 ha2
      have ha2' : a.val ≤ l.val := by simp at ha2; omega
      by_cases hal : a = l
      · rw [hal, ← Matrix.mulVec_mulVec, Formalism.FourierDecayAlt.P.CutMP.TVCoefPf.w1_mulVec_bvec_esI, Matrix.mulVec_smul, hTe l (by simp)]
      · have hav : a.val < l.val := by
          rcases Nat.lt_or_ge a.val l.val with h | h
          · exact h
          · exact absurd (Fin.ext (by omega)) hal
        have h1 : esI k r a ≠ eI k r l := by simp [eI, esI, Fin.ext_iff]; have := a.isLt; omega
        have h2 : esI k r a ≠ esI k r l := by simp [esI, Fin.ext_iff]; have := a.isLt; omega
        rw [← Matrix.mulVec_mulVec, weyl_cell_mulVec_basis, sw_o l h1 h2, dd_o l _ h1 h2, one_smul,
          hTs a ha1 (by simp; omega)]

section rules

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rightRuleBv (z' : Fin (2 * r + k + 1) → ℂ) (D : Set (Mx k r)) (f : Mx k r → E) (hz' : inWb k r z')
    (hD : IsOpen D) (hS : SmoothLev k r 0 D f) (hR : RightEq k r z' 0 D f) (g : Mx k r) (hg : g ∈ Glev k r 0 ∩ D)
    (a : Fin r) (ha : a.val + 1 < r) (w : Fin (k + 1)) : EH k r (wI k r w) (esI k r a) f g = 0 := by
  have hc : Continuous fun x : Mx k r => g * x := cont_lmul g
  have hD' : IsOpen {x : Mx k r | g * x ∈ D} := hD.preimage hc
  have hS' : SmoothLev k r a.castSucc {x | g * x ∈ D} (fun x => f (g * x)) :=
    smooth_left g (fun x hx => glev0 hg.1 hx) hS
  have hR' : RightEq k r z' a.castSucc {x | g * x ∈ D} (fun x => f (g * x)) := by
    intro x hx n hn
    have := hR (g * x) ⟨glev0 hg.1 hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)
    simpa [Matrix.mul_assoc] using this
  have h1 : (1 : Mx k r) ∈ Glev k r a.castSucc ∩ {x | g * x ∈ D} :=
    ⟨glev_one _, by simpa using hg.2⟩
  have hrule := (Formalism.FourierDecayAlt.P.right_action_rule E k r z' a {x | g * x ∈ D} (fun x => f (g * x)) hz' hD' hS' hR'
    1 h1).2.1
  have hjlt : r + w.val - a.val - 1 < mdim k r a.succ := by simp [mdim]; omega
  have hpos : posL k r a.succ ⟨r + w.val - a.val - 1, hjlt⟩ = wI k r w := by
    simp [posL, wI, Fin.ext_iff]; omega
  have h := hrule ⟨r + w.val - a.val - 1, hjlt⟩
  rw [hpos, eH_left, Matrix.mul_one] at h
  rw [h]
  have hx : xbv k r z' a.succ ⟨r + w.val - a.val - 1, hjlt⟩ = 0 := by
    simp only [xbv, fvec, hpos]
    rw [dif_pos (show (a.succ : Fin (r + 1)).val < r by simp; omega), Formalism.FourierDecayAlt.P.SignAntidiagonal.herm_bvec_eI]
    simp only [bvec, Pi.single_apply]
    rw [if_neg]
    intro h'
    have := congrArg Fin.val h'
    simp [wI, esI] at this
    omega
  rw [hx, zero_smul]

theorem leftRuleBv (z : Fin (2 * r + k + 1) → ℂ) (D : Set (Mx k r)) (f : Mx k r → E) (hz : inWb k r z)
    (hD : IsOpen D) (hDN : ∀ g ∈ Glev k r 0 ∩ D, ∀ n ∈ Nlev k r 0, n * g ∈ D) (hS : SmoothLev k r 0 D f)
    (hL : LeftEq k r z 0 D f) (c : Fin r → ℂ) (hc : c ∈ OmX r) (g : Mx k r) (hg : g ∈ Glev k r (Fin.last r))
    (hWD : wCell k r (Fin.last r) c * g ∈ D) (b : Fin r) (hb : b.val + 1 < r) (v : Fin (k + 1)) :
    EH k r (esI k r b) (wI k r v) f (wCell k r (Fin.last r) c * g) = 0 := by
  have hcne : ∀ l, c l ≠ 0 := hc
  obtain ⟨hW0, hWcomm⟩ := head_comm (k := k) c hcne b.val b.castSucc (by simp)
  obtain ⟨T, hT, hTG, -, hTs⟩ := exists_wCell_eq_wCell_succ_mul_tail_factor (k := k) c hcne b (r - b.val - 1) (Fin.last r) (by simp; omega)
  have hg₁ : T * g ∈ Glev k r b.succ := glev_mul hTG (glev_mono (Fin.le_last _) hg)
  have hsplit : wCell k r (Fin.last r) c * g = wCell k r b.castSucc c * (w1 k r b (c b) * (T * g)) := by
    simp only [hT, Formalism.FourierDecayAlt.P.Qx6.wCell_succ, Matrix.mul_assoc]
  have hWx : ∀ x ∈ Glev k r b.castSucc, wCell k r b.castSucc c * x ∈ Glev k r 0 := fun x hx => glev0 hW0 hx
  have hS' := smooth_left (E := E) (f := f) (D := D) (wCell k r b.castSucc c) hWx hS
  have hcont : Continuous fun x : Mx k r => wCell k r b.castSucc c * x := cont_lmul _
  have hD' : IsOpen {x : Mx k r | wCell k r b.castSucc c * x ∈ D} := hD.preimage hcont
  have hN' : ∀ x ∈ Glev k r b.castSucc ∩ {x | wCell k r b.castSucc c * x ∈ D}, ∀ n ∈ Nlev k r b.castSucc,
      n * x ∈ {x | wCell k r b.castSucc c * x ∈ D} := by
    intro x hx n hn
    show wCell k r b.castSucc c * (n * x) ∈ D
    rw [← Matrix.mul_assoc, hWcomm b.castSucc le_rfl n hn.2, Matrix.mul_assoc]
    exact hDN _ ⟨hWx x hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)
  have hL' : LeftEq k r z b.castSucc {x | wCell k r b.castSucc c * x ∈ D}
      (fun x => f (wCell k r b.castSucc c * x)) := by
    intro x hx n hn
    show f (wCell k r b.castSucc c * (n * x)) = _ • f (wCell k r b.castSucc c * x)
    rw [← Matrix.mul_assoc, hWcomm b.castSucc le_rfl n hn.2, Matrix.mul_assoc]
    exact hL _ ⟨hWx x hx.1, hx.2⟩ n (nlev_mono (zero_le' _) hn)
  have hpt : w1 k r b (c b) * (T * g) ∈ {x | wCell k r b.castSucc c * x ∈ D} := by
    show _ ∈ D
    rw [← hsplit]; exact hWD
  have hrule := (Formalism.FourierDecayAlt.P.left_action_rule E k r z b {x | wCell k r b.castSucc c * x ∈ D}
    (fun x => f (wCell k r b.castSucc c * x)) hz hD' hS' hN' hL' (c b) (hcne b) (T * g) hg₁ hpt).2.1
  have hjlt : r + v.val - b.val - 1 < mdim k r b.succ := by simp [mdim]; omega
  have hpos : posL k r b.succ ⟨r + v.val - b.val - 1, hjlt⟩ = wI k r v := by
    simp [posL, wI, Fin.ext_iff]; omega
  have h := hrule ⟨r + v.val - b.val - 1, hjlt⟩
  rw [hpos, eH_left, ← hsplit] at h
  rw [h]
  have hb1 : (b.succ : Fin (r + 1)).val < r := by simp; omega
  set b1 : Fin r := ⟨b.val + 1, by omega⟩ with hb1def
  have hU : T * g ∈ UH (Hpk k r) := hg₁.1
  have hgs : g *ᵥ bvec (esI k r b1) = bvec (esI k r b1) := (hg.2 b1 (by simp)).2
  have hx : (T * g) *ᵥ (star (c b1) • bvec (esI k r b1)) = bvec (eI k r b1) := by
    rw [Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, hgs, hTs b1 (by simp [b1]) (by simp [b1]; omega), smul_smul,
      mul_inv_cancel₀ (star_ne_zero.2 (hcne b1)), one_smul]
  have hinv : (T * g)⁻¹ *ᵥ bvec (eI k r b1) = star (c b1) • bvec (esI k r b1) := by
    rw [← hx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hU), Matrix.one_mulVec]
  have hy : yv k r z b.succ (T * g) ⟨r + v.val - b.val - 1, hjlt⟩ = 0 := by
    simp only [yv, hpos, fvec, dif_pos hb1]
    have e1 : (eI k r ⟨(b.succ : Fin (r + 1)).val, hb1⟩) = eI k r b1 := by simp [b1, eI]
    rw [e1, hinv]
    simp only [Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul]
    rw [if_neg, mul_zero]
    intro h'
    have := congrArg Fin.val h'
    simp [wI, esI, b1] at this
    omega
  rw [hy, mul_zero, zero_smul]

end rules

section gauge

theorem gauge_scalar_bar (z : ℂ) (hz : z ≠ 0) (m : ℕ) (P : ℝ) :
    star z * ((1 / 2 : ℂ) * ((((m : ℝ) * P * ((1 * conj z).re / ‖z‖ ^ 2) : ℝ) : ℂ) +
      Complex.I * (((m : ℝ) * P * ((Complex.I * conj z).re / ‖z‖ ^ 2) : ℝ) : ℂ))) = (P : ℂ) * ((m : ℂ) / 2) := by
  have h1 : (1 * conj z).re = z.re := by simp
  have h2 : (Complex.I * conj z).re = z.im := by simp
  have hc : ((z.re : ℂ)) + Complex.I * (z.im : ℂ) = z := by apply Complex.ext <;> simp
  have hzz : star z * z = (‖z‖ : ℂ) ^ 2 := by
    rw [mul_comm, show star z = conj z from rfl, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hN0 : (‖z‖ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  rw [h1, h2]
  push_cast
  calc _ = ((m : ℂ) * P / 2) * (star z * ((z.re : ℂ) + Complex.I * (z.im : ℂ))) / (‖z‖ : ℂ) ^ 2 := by ring
    _ = (P : ℂ) * ((m : ℂ) / 2) := by
      have hN1 : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
      rw [hc, hzz]; field_simp

theorem gaugePb {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (r : ℕ) (n : Fin r → ℕ) (H : (Fin r → ℂ) → E)
    (c : Fin r → ℂ) (hc : c ∈ OmX r) (hH : DifferentiableAt ℝ H c) (l : Fin r) :
    pbOp l (fun c' => ((∏ a, ‖c' a‖ ^ n a : ℝ) : ℂ) • H c') c =
      ((∏ a, ‖c a‖ ^ n a : ℝ) : ℂ) • (pbOp l H c + ((n l : ℂ) / 2) • H c) := by
  obtain ⟨hψ, hψ'⟩ := Formalism.FourierDecayAlt.P.GaugeNormPower.fderiv_prodPow r n c hc l 1
  obtain ⟨-, hψI⟩ := Formalism.FourierDecayAlt.P.GaugeNormPower.fderiv_prodPow r n c hc l Complex.I
  have hfun : (fun c' : Fin r → ℂ => ((∏ a, ‖c' a‖ ^ n a : ℝ) : ℂ) • H c') =
      (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) • H := by
    funext c'; exact Complex.coe_smul _ _
  rw [hfun]
  have hD : ∀ w, fderiv ℝ ((fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) • H) c w =
      (∏ a, ‖c a‖ ^ n a) • fderiv ℝ H c w + fderiv ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c w • H c := by
    intro w
    rw [(hψ.hasFDerivAt.smul hH.hasFDerivAt).fderiv]
    simp
  have hs : star (c l) * ((1 / 2 : ℂ) * (((fderiv ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c (Pi.single l 1) : ℝ) : ℂ) +
      Complex.I * ((fderiv ℝ (fun x : Fin r → ℂ => ∏ a, ‖x a‖ ^ n a) c (Pi.single l Complex.I) : ℝ) : ℂ))) =
      ((∏ a, ‖c a‖ ^ n a : ℝ) : ℂ) * ((n l : ℂ) / 2) := by
    rw [hψ', hψI]
    exact gauge_scalar_bar (c l) (hc l) (n l) _
  simp only [pbOp, if_pos hc, wirtBar]
  rw [hD, hD]
  simp only [← Complex.coe_smul]
  linear_combination (norm := module) hs • H c

end gauge

section ring

theorem comm_qminor {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (p : Fin n)
    {a b : Fin t → Fin n} (ha : ∀ i, a i ≠ p) (hb : ∀ i, b i ≠ p) (w : ℂ) : Commute (E p p) (qminor E a b w) := by
  unfold qminor
  refine Commute.sum_right _ _ _ fun σ _ => ?_
  refine ((Int.cast_commute _ _).symm).mul_right ?_
  apply Commute.list_prod_right
  intro T hT
  rw [List.mem_ofFn] at hT
  obtain ⟨i, rfl⟩ := hT
  unfold Tm
  refine Commute.add_right ?_ ?_
  · split_ifs
    · exact Algebra.commute_algebraMap_right _ _
    · exact Commute.zero_right _
  · have h := hE p p (a (σ i)) (b i)
    rw [if_neg (Ne.symm (ha _)), if_neg (hb _), sub_zero] at h
    exact sub_eq_zero.1 h

theorem stepBv_ring {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    {M : Type} [AddCommGroup M] [Module ℂ M] (Λ : A →ₗ[ℂ] M) (q0 q1 : Fin n) (h01 : q0 ≠ q1) (κ : ℂ)
    {t : ℕ} (a b : Fin (t + 2) → Fin n) (ha0 : a (Fin.last (t + 1)) = q0) (ha1 : a (Fin.last t).castSucc = q1)
    (hb0 : b (Fin.last (t + 1)) = q0) (hb1 : b (Fin.last t).castSucc = q1)
    (haR : ∀ m : Fin t, a m.castSucc.castSucc ≠ q0) (hbR : ∀ m : Fin t, b m.castSucc.castSucc ≠ q0)
    (hR0 : ∀ m : Fin t, ∀ X, Λ (X * E (a m.castSucc.castSucc) q0) = 0) (hR1 : ∀ X, Λ (X * E q1 q0) = Λ X)
    (hL0 : ∀ m : Fin t, ∀ X, Λ (E q0 (b m.castSucc.castSucc) * X) = 0) (hL1 : ∀ X, Λ (E q0 q1 * X) = κ • Λ X)
    (u : ℂ) :
    Λ (qminor E a b u) = Λ (qminor E (a ∘ Fin.castSucc) (b ∘ Fin.castSucc) u * Tm E (u - ((t + 1 : ℕ) : ℂ)) q0 q0) -
      κ • Λ (qminor E (a ∘ Fin.castSucc ∘ Fin.castSucc) (b ∘ Fin.castSucc ∘ Fin.castSucc) u) := by
  set a' : Fin (t + 1) → Fin n := a ∘ (Fin.last t).castSucc.succAbove with ha'
  set b' : Fin (t + 1) → Fin n := b ∘ Fin.castSucc with hb'
  set a'' : Fin (t + 1) → Fin n := Fin.cons q0 (a' ∘ Fin.castSucc) with ha''
  set τ : Equiv.Perm (Fin (t + 1)) := (Fin.last t).cycleRange with hτ
  have hsq : ((Equiv.Perm.sign τ : ℤ) : A) * ((Equiv.Perm.sign τ : ℤ) : A) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hsg : ((Equiv.Perm.sign τ : ℤ) : A) = (((-1 : ℤ) ^ t : ℤ) : A) := by
    rw [hτ, Fin.sign_cycleRange]
    simp
  have hperm : a'' ∘ τ = a' := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Function.comp_apply, hτ, Fin.cycleRange_self, ha'', Fin.cons_zero, ha']
      rw [Fin.succAbove_of_le_castSucc _ _ le_rfl, Fin.succ_last, ha0]
    · simp only [Function.comp_apply, hτ]
      rw [Fin.cycleRange_of_lt (Fin.castSucc_lt_last i), Fin.coeSucc_eq_succ, ha'', Fin.cons_succ]
      rfl
  have hcs2 : a' ∘ Fin.castSucc = a ∘ Fin.castSucc ∘ Fin.castSucc := by
    funext i
    simp only [Function.comp_apply, ha']
    rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.castSucc_lt_castSucc_iff]; exact Fin.castSucc_lt_last i)]
  have hQ' : Λ (qminor E a' b' u) =
      κ • Λ (qminor E (a ∘ Fin.castSucc ∘ Fin.castSucc) (b ∘ Fin.castSucc ∘ Fin.castSucc) u) := by
    have hsk := Formalism.REAL.quantumMinorRowSkew_holds A n (t + 1) E a'' b' τ u
    rw [hperm] at hsk
    rw [hsk, Formalism.FourierDecayAlt.P.expansion_first_line A n t E hE a'' b' u, Finset.mul_sum, map_sum, Fin.sum_univ_castSucc]
    have hrest : ∀ m : Fin t, Λ (((Equiv.Perm.sign τ : ℤ) : A) * ((((-1 : ℤ) ^ ((m.castSucc : Fin (t + 1)) : ℕ) : ℤ) : A) *
        (Tm E (u - (t : ℂ)) (a'' 0) (b' m.castSucc) * qminor E (a'' ∘ Fin.succ) (b' ∘ m.castSucc.succAbove) u))) = 0 := by
      intro m
      have hbm : b' m.castSucc = b m.castSucc.castSucc := rfl
      rw [hbm, ha'', Fin.cons_zero]
      unfold Tm
      rw [if_neg (Ne.symm (hbR m)), zero_add, zcomm _ (E q0 _), zcomm _ (E q0 _)]
      exact hL0 m _
    rw [Finset.sum_eq_zero (fun m _ => hrest m), zero_add]
    have hbl : b' (Fin.last t) = q1 := hb1
    rw [hbl, ha'', Fin.cons_zero]
    unfold Tm
    rw [if_neg h01, zero_add, zcomm _ (E q0 q1), zcomm _ (E q0 q1), hL1, ← mul_assoc, hsg, ← Int.cast_mul]
    have h11 : ((-1 : ℤ) ^ t * (-1) ^ ((Fin.last t : Fin (t + 1)) : ℕ)) = 1 := by
      rw [Fin.val_last, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [h11, Int.cast_one, one_mul, Fin.succAbove_last]
    congr 3
    all_goals (funext i; simp only [Function.comp_apply, Fin.cons_succ]; exact congrFun hcs2 i)
  rw [Formalism.FourierDecayAlt.P.expansion_last_column A n (t + 1) E a b u, map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hrest : ∀ m : Fin t, Λ ((((-1 : ℤ) ^ (t + 1 + ((m.castSucc.castSucc : Fin (t + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ m.castSucc.castSucc.succAbove) (b ∘ Fin.castSucc) u *
        Tm E (u - ((t + 1 : ℕ) : ℂ)) (a m.castSucc.castSucc) (b (Fin.last (t + 1))))) = 0 := by
    intro m
    rw [hb0]
    unfold Tm
    rw [if_neg (haR m), zero_add, ← mul_assoc]
    exact hR0 m _
  rw [Finset.sum_eq_zero (fun m _ => hrest m), zero_add]
  have hsl : Λ ((((-1 : ℤ) ^ (t + 1 + (((Fin.last t).castSucc : Fin (t + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.last t).castSucc.succAbove) (b ∘ Fin.castSucc) u *
        Tm E (u - ((t + 1 : ℕ) : ℂ)) (a (Fin.last t).castSucc) (b (Fin.last (t + 1))))) =
      -Λ (qminor E a' b' u) := by
    rw [ha1, hb0]
    unfold Tm
    rw [if_neg (Ne.symm h01), zero_add, ← mul_assoc, hR1, zmul, map_smul]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [show t + 1 + t = 2 * t + 1 by ring, pow_succ, pow_mul]
    simp
    try rfl
  rw [hsl, hQ']
  have hl : Λ ((((-1 : ℤ) ^ (t + 1 + ((Fin.last (t + 1) : Fin (t + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.last (t + 1)).succAbove) (b ∘ Fin.castSucc) u *
        Tm E (u - ((t + 1 : ℕ) : ℂ)) (a (Fin.last (t + 1))) (b (Fin.last (t + 1))))) =
      Λ (qminor E (a ∘ Fin.castSucc) (b ∘ Fin.castSucc) u * Tm E (u - ((t + 1 : ℕ) : ℂ)) q0 q0) := by
    rw [ha0, hb0, Fin.succAbove_last, Fin.val_last, ← two_mul, pow_mul]
    norm_num
  rw [hl]
  abel

end ring

end Formalism.FourierDecayAlt.P.CutMP.StepB
