import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CmHalfIntegralGeneratorMemAlgebraicClosure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition

open Matrix Formalism.YangianSpanCharacter.T

noncomputable section

namespace Formalism.FourierDecayAlt.P.Qx7

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Qdet

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem rtt_entry (QQ : ℂ → Matrix (Fin 2) (Fin 2) A) (h : Formalism.FourierDecayAlt.W.IsRTT QQ) (Y Y' : ℂ) (a b c d : Fin 2) :
    (Y' - Y) • (QQ Y' a b * QQ Y c d - QQ Y c d * QQ Y' a b) =
      QQ Y' c b * QQ Y a d - QQ Y c b * QQ Y' a d := by
  have h0 := congrFun (congrFun (h Y Y') (a, c)) (b, d)
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [E1, E2, Pf, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, sub_mul, mul_sub] at h0 ⊢ <;>
    (rw [smul_sub]; linear_combination (norm := abel) h0)

macro "distrib_module" : tactic =>
  `(tactic| (simp only [mul_sub, sub_mul, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_assoc, smul_sub, smul_add,
      smul_smul]; module))

theorem idempotent_mul_comm (r s t : Matrix (Fin 2) (Fin 2) A) (D : ℂ)
    (hst : ∀ a b c d, (1 : ℂ) • (s a b * t c d - t c d * s a b) = s c b * t a d - t c b * s a d)
    (hts : ∀ a b c d, (-1 : ℂ) • (t a b * s c d - s c d * t a b) = t c b * s a d - s c b * t a d)
    (hsr : ∀ a b c d, (1 - D) • (s a b * r c d - r c d * s a b) = s c b * r a d - r c b * s a d)
    (hrt : ∀ a b c d, D • (r a b * t c d - t c d * r a b) = r c b * t a d - t c b * r a d)
    (a b : Fin 2) :
    (s 0 0 * t 1 1 - s 1 0 * t 0 1) * r a b = r a b * (s 0 0 * t 1 1 - s 1 0 * t 0 1) := by
  fin_cases a <;> fin_cases b
  · show (s 0 0 * t 1 1 - s 1 0 * t 0 1) * r 0 0 = r 0 0 * (s 0 0 * t 1 1 - s 1 0 * t 0 1)
    linear_combination (norm := distrib_module) (1 : ℂ) • (r 0 1 * hst 0 0 1 0) +
      (1 : ℂ) • (r 0 0 * hst 1 0 0 1) +
      (1 : ℂ) • (r 0 0 * hst 1 1 0 0) +
      (1 : ℂ) • (hsr 0 0 0 1 * t 1 0) +
      (-1 : ℂ) • (hsr 1 0 0 1 * t 0 0) +
      (D/2 : ℂ) • (r 0 1 * hts 0 0 1 0) +
      (-D/2 : ℂ) • (hts 0 0 1 0 * r 0 1) +
      (-D/2 : ℂ) • (r 0 1 * hts 1 0 0 0) +
      (D/2 : ℂ) • (hts 1 0 0 0 * r 0 1) +
      (-1 : ℂ) • (s 1 0 * hrt 0 1 0 0) +
      (1 : ℂ) • (s 0 0 * hrt 0 1 1 0)
  · show (s 0 0 * t 1 1 - s 1 0 * t 0 1) * r 0 1 = r 0 1 * (s 0 0 * t 1 1 - s 1 0 * t 0 1)
    linear_combination (norm := distrib_module) (1 : ℂ) • (r 0 0 * hst 1 1 0 1) +
      (D : ℂ) • (hst 1 1 0 1 * r 0 0) +
      (-1 : ℂ) • (hsr 0 1 0 0 * t 1 1) +
      (1 : ℂ) • (hsr 1 1 0 0 * t 0 1) +
      (-1 : ℂ) • (hts 0 0 1 1 * r 0 1) +
      (-D/2 : ℂ) • (r 0 0 * hts 0 1 1 1) +
      (1 : ℂ) • (hts 1 0 0 1 * r 0 1) +
      (D/2 : ℂ) • (r 0 0 * hts 1 1 0 1) +
      (1 : ℂ) • (s 1 1 * hrt 0 0 0 1) +
      (-1 : ℂ) • (s 0 1 * hrt 0 0 1 1)
  · show (s 0 0 * t 1 1 - s 1 0 * t 0 1) * r 1 0 = r 1 0 * (s 0 0 * t 1 1 - s 1 0 * t 0 1)
    linear_combination (norm := distrib_module) (1 : ℂ) • (hst 0 0 1 1 * r 1 0) +
      (1 : ℂ) • (r 1 0 * hst 1 0 0 1) +
      (-1 : ℂ) • (t 1 1 * hsr 1 0 0 0) +
      (1 : ℂ) • (t 1 0 * hsr 1 1 0 0) +
      (D/2 : ℂ) • (r 0 0 * hts 1 0 1 1) +
      (1/2 - D/2 : ℂ) • (hts 1 0 1 1 * r 0 0) +
      (-D/2 : ℂ) • (r 0 0 * hts 1 1 1 0) +
      (D/2 - 1/2 : ℂ) • (hts 1 1 1 0 * r 0 0) +
      (1 : ℂ) • (hrt 0 0 1 0 * s 1 1) +
      (-1 : ℂ) • (hrt 0 0 1 1 * s 1 0)
  · show (s 0 0 * t 1 1 - s 1 0 * t 0 1) * r 1 1 = r 1 1 * (s 0 0 * t 1 1 - s 1 0 * t 0 1)
    linear_combination (norm := distrib_module) (D/2 : ℂ) • (r 1 0 * hst 0 1 1 1) +
      (1/2 : ℂ) • (r 1 1 * hst 1 0 0 1) +
      (-1/2 : ℂ) • (hst 1 0 0 1 * r 1 1) +
      (D/2 : ℂ) • (hst 1 0 1 1 * r 0 1) +
      (1/2 : ℂ) • (r 1 0 * hst 1 1 0 1) +
      (-1/2 : ℂ) • (hsr 0 1 1 0 * t 1 1) +
      (-1/2 : ℂ) • (t 1 1 * hsr 1 0 0 1) +
      (1/2 : ℂ) • (t 1 0 * hsr 1 1 0 1) +
      (1/2 : ℂ) • (hsr 1 1 1 0 * t 0 1) +
      (-1/2 : ℂ) • (hts 0 0 1 1 * r 1 1) +
      (D/4 : ℂ) • (hts 0 1 1 1 * r 1 0) +
      (D/4 : ℂ) • (r 0 1 * hts 1 0 1 1) +
      (1/4 : ℂ) • (hts 1 0 1 1 * r 0 1) +
      (1/2 : ℂ) • (hts 1 1 0 0 * r 1 1) +
      (-D/4 : ℂ) • (hts 1 1 0 1 * r 1 0) +
      (-D/4 : ℂ) • (r 0 1 * hts 1 1 1 0) +
      (-1/4 : ℂ) • (hts 1 1 1 0 * r 0 1) +
      (1/2 : ℂ) • (hrt 0 1 1 0 * s 1 1) +
      (-1/2 : ℂ) • (hrt 0 1 1 1 * s 1 0) +
      (1/2 : ℂ) • (s 1 1 * hrt 1 0 0 1) +
      (-1/2 : ℂ) • (s 0 1 * hrt 1 0 1 1)

end Qdet

theorem qdet_main : Formalism.FourierDecayAlt.Q.QdetFromRTT := by
  intro A _ _ QQ h Y
  have hst : ∀ a b c d, (1 : ℂ) • (QQ (Y + 1) a b * QQ Y c d - QQ Y c d * QQ (Y + 1) a b) =
      QQ (Y + 1) c b * QQ Y a d - QQ Y c b * QQ (Y + 1) a d := fun a b c d => by
    have h0 := rtt_entry QQ h Y (Y + 1) a b c d
    rwa [show Y + 1 - Y = 1 by ring] at h0
  have hts : ∀ a b c d, (-1 : ℂ) • (QQ Y a b * QQ (Y + 1) c d - QQ (Y + 1) c d * QQ Y a b) =
      QQ Y c b * QQ (Y + 1) a d - QQ (Y + 1) c b * QQ Y a d := fun a b c d => by
    have h0 := rtt_entry QQ h (Y + 1) Y a b c d
    rwa [show Y - (Y + 1) = -1 by ring] at h0
  refine ⟨QQ (Y + 1) 0 0 * QQ Y 1 1 - QQ (Y + 1) 1 0 * QQ Y 0 1, ?_, ?_, ?_⟩
  · ext c d
    fin_cases c <;> fin_cases d <;>
      simp [Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
    · linear_combination (norm := distrib_module) hst 0 0 1 0
    · abel
    · linear_combination (norm := distrib_module) hst 0 1 1 0 + hst 0 0 1 1
    · linear_combination (norm := distrib_module) hst 0 1 1 1
  · ext c a
    fin_cases c <;> fin_cases a <;>
      simp [Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
    · linear_combination (norm := distrib_module) hst 0 0 0 1
    · linear_combination (norm := distrib_module) hst 1 0 0 1
    · linear_combination (norm := distrib_module) hst 0 0 1 1
    · linear_combination (norm := distrib_module) hst 1 0 1 1
  · intro Y' a b
    refine idempotent_mul_comm (QQ Y') (QQ (Y + 1)) (QQ Y) (Y' - Y) hst hts (fun a b c d => ?_)
      (fun a b c d => rtt_entry QQ h Y Y' a b c d) a b
    have h0 := rtt_entry QQ h Y' (Y + 1) a b c d
    rwa [show Y + 1 - Y' = 1 - (Y' - Y) by ring] at h0

section Mono

def logD (A B c : ℂ) : ℂ →L[ℝ] ℂ :=
  (A / c) • (ContinuousLinearMap.id ℝ ℂ) + (B / star c) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)

theorem logD_apply (A B c h : ℂ) : logD A B c h = A / c * h + B / star c * star h := by
  simp [logD]

def LD (f : ℂ → ℂ) (c A B : ℂ) : Prop := HasFDerivAt f (f c • logD A B c) c

theorem LD.mul {f g : ℂ → ℂ} {c A B A' B' : ℂ} (hf : LD f c A B) (hg : LD g c A' B') :
    LD (fun x => f x * g x) c (A + A') (B + B') := by
  have h := HasFDerivAt.mul hf hg
  refine h.congr_fderiv (ContinuousLinearMap.ext fun x => ?_)
  simp [logD_apply]
  ring

theorem LD.star {f : ℂ → ℂ} {c A B : ℂ} (hf : LD f c A B) :
    LD (fun x => star (f x)) c (star B) (star A) := by
  have h := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp c hf
  refine h.congr_fderiv (ContinuousLinearMap.ext fun x => ?_)
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply, logD_apply, smul_eq_mul,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul, map_add, map_div₀, Complex.star_def,
    Complex.conj_conj]
  ring

theorem LD_zpow (n : ℤ) {c : ℂ} (hc : c ≠ 0) : LD (fun x => x ^ n) c n 0 := by
  have h := ((hasDerivAt_zpow n c (Or.inl hc)).hasFDerivAt).restrictScalars ℝ
  refine h.congr_fderiv (ContinuousLinearMap.ext fun x => ?_)
  simp [logD_apply, zpow_sub_one₀ hc]
  field_simp

theorem cpow_norm_eq (γ : ℂ) {x : ℂ} (hx : x ≠ 0) :
    ((‖x‖ : ℝ) : ℂ) ^ (2 * γ) = Complex.exp (γ * ((Real.log (‖x‖ ^ 2) : ℝ) : ℂ)) := by
  have h0 : ((‖x‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hx)
  rw [Complex.cpow_def_of_ne_zero h0, ← Complex.ofReal_log (norm_nonneg x), Real.log_pow]
  push_cast
  ring_nf

theorem LD_norm (γ : ℂ) {c : ℂ} (hc : c ≠ 0) : LD (fun x => ((‖x‖ : ℝ) : ℂ) ^ (2 * γ)) c γ γ := by
  have hn : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hc)
  have h1 : HasFDerivAt (fun x : ℂ => ‖x‖ ^ 2) (2 • (innerSL ℝ c)) c := (hasStrictFDerivAt_norm_sq c).hasFDerivAt
  have h2 := h1.log hn
  have h3 : HasFDerivAt (fun x : ℂ => ((Real.log (‖x‖ ^ 2) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((‖c‖ ^ 2)⁻¹ • (2 • (innerSL ℝ c)))) c :=
    (Complex.ofRealCLM.hasFDerivAt (x := Real.log (‖c‖ ^ 2))).comp c h2
  have h4a : HasFDerivAt (fun x : ℂ => γ * ((Real.log (‖x‖ ^ 2) : ℝ) : ℂ))
      (γ • (Complex.ofRealCLM.comp ((‖c‖ ^ 2)⁻¹ • (2 • (innerSL ℝ c))))) c := h3.const_mul γ
  have h4 := h4a.cexp
  have hev : (fun x : ℂ => ((‖x‖ : ℝ) : ℂ) ^ (2 * γ)) =ᶠ[nhds c]
      fun x : ℂ => Complex.exp (γ * ((Real.log (‖x‖ ^ 2) : ℝ) : ℂ)) := by
    filter_upwards [isOpen_ne.mem_nhds hc] with x hx
    exact cpow_norm_eq γ hx
  have h5 := h4.congr_of_eventuallyEq hev
  refine h5.congr_fderiv (ContinuousLinearMap.ext fun x => ?_)
  have e1 : ((‖c‖ : ℝ) : ℂ) ^ 2 = c * star c := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  have e2 : ((2 * (inner ℝ c x : ℝ) : ℝ) : ℂ) = star c * x + c * star x := by
    rw [Complex.inner, Complex.star_def]
    have := Complex.add_conj (x * (starRingEnd ℂ) c)
    rw [map_mul, Complex.conj_conj] at this
    rw [← this]
    ring
  have hsc : star c ≠ 0 := star_ne_zero.2 hc
  simp only [logD_apply, cpow_norm_eq γ hc, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul, innerSL_apply_apply, Complex.ofRealCLM_apply, nsmul_eq_mul, Nat.cast_ofNat]
  have e3 : (((‖c‖ ^ 2)⁻¹ * (2 * (inner ℝ c x : ℝ)) : ℝ) : ℂ) = 1 / c * x + 1 / star c * star x := by
    rw [Complex.ofReal_mul, e2, Complex.ofReal_inv, Complex.ofReal_pow, e1]
    field_simp
  rw [e3]; ring

def mu (β : ℂ) (n : ℤ) (s s' : ℕ) (c : ℂ) : ℂ :=
  ((‖c‖ : ℝ) : ℂ) ^ (2 * β) * c ^ n * (c ^ s)⁻¹ * (star c ^ s')⁻¹

theorem LD_mu (β : ℂ) (n : ℤ) (s s' : ℕ) {c : ℂ} (hc : c ≠ 0) :
    LD (mu β n s s') c (β + n - s) (β - s') := by
  have h1 := ((LD_norm β hc).mul (LD_zpow n hc)).mul (LD_zpow (-(s : ℤ)) hc)
  have h2 := h1.mul (LD_zpow (-(s' : ℤ)) hc).star
  have e : (fun x : ℂ => ((‖x‖ : ℝ) : ℂ) ^ (2 * β) * x ^ n * x ^ (-(s : ℤ)) * star (x ^ (-(s' : ℤ)))) = mu β n s s' := by
    funext x
    simp [mu, _root_.zpow_neg, star_inv₀]
  rw [e] at h2
  have eA : β + (n : ℂ) + ((-(s : ℤ) : ℤ) : ℂ) + star (0 : ℂ) = β + n - s := by push_cast; simp; ring
  have eB : β + 0 + 0 + star (((-(s' : ℤ) : ℤ) : ℂ)) = β - s' := by push_cast; simp; ring
  rw [eA, eB] at h2
  exact h2

end Mono

section Rep

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

structure Term (k r : ℕ) (E : Type*) where
  co : ℂ
  s : ℕ
  s' : ℕ
  Ψ : Mx k r → E

def ev (β : ℂ) (n : ℤ) (l : Fin r) (L : List (Term k r E)) (c : Fin r → ℂ) (g : Mx k r) : E :=
  (L.map fun t => (t.co * mu β n t.s t.s' (c l)) • t.Ψ g).sum

variable (β : ℂ) (n : ℤ) (l : Fin r)

@[simp] theorem ev_nil (c : Fin r → ℂ) (g : Mx k r) : ev β n l ([] : List (Term k r E)) c g = 0 := rfl

@[simp] theorem ev_cons (t : Term k r E) (L : List (Term k r E)) (c : Fin r → ℂ) (g : Mx k r) :
    ev β n l (t :: L) c g = (t.co * mu β n t.s t.s' (c l)) • t.Ψ g + ev β n l L c g := by
  simp [ev]

@[simp] theorem ev_append (L L' : List (Term k r E)) (c : Fin r → ℂ) (g : Mx k r) :
    ev β n l (L ++ L') c g = ev β n l L c g + ev β n l L' c g := by
  simp [ev]

def WD (l : Fin r) (F : (Fin r → ℂ) → E) (c : Fin r → ℂ) (P Pb : E) : Prop :=
  ∃ F' : (Fin r → ℂ) →L[ℝ] E, HasFDerivAt F F' c ∧
    c l • ((1 / 2 : ℂ) • (F' (Pi.single l 1) - Complex.I • F' (Pi.single l Complex.I))) = P ∧
    star (c l) • ((1 / 2 : ℂ) • (F' (Pi.single l 1) + Complex.I • F' (Pi.single l Complex.I))) = Pb

theorem WD.pOp {F : (Fin r → ℂ) → E} {c : Fin r → ℂ} {P Pb : E} (h : WD l F c P Pb) (hc : c ∈ OmX r) :
    pOp l F c = P ∧ pbOp l F c = Pb := by
  obtain ⟨F', hF, h1, h2⟩ := h
  constructor
  · simp only [Formalism.QuantumDeterminants.pOp, if_pos hc, wirt, hF.fderiv, h1]
  · simp only [Formalism.QuantumDeterminants.pbOp, if_pos hc, wirtBar, hF.fderiv, h2]

theorem WD.add {F G : (Fin r → ℂ) → E} {c : Fin r → ℂ} {P Pb Q Qb : E} (hF : WD l F c P Pb) (hG : WD l G c Q Qb) :
    WD l (fun x => F x + G x) c (P + Q) (Pb + Qb) := by
  obtain ⟨F', hF', h1, h2⟩ := hF
  obtain ⟨G', hG', g1, g2⟩ := hG
  refine ⟨F' + G', hF'.add hG', ?_, ?_⟩
  · rw [← h1, ← g1]; simp only [_root_.add_apply]; module
  · rw [← h2, ← g2]; simp only [_root_.add_apply]; module

theorem WD.zero (c : Fin r → ℂ) : WD l (fun _ => (0 : E)) c 0 0 :=
  ⟨0, hasFDerivAt_const _ _, by simp, by simp⟩

theorem WD.congr {F G : (Fin r → ℂ) → E} {c : Fin r → ℂ} {P Pb : E} (hG : WD l G c P Pb)
    (h : F =ᶠ[nhds c] G) : WD l F c P Pb := by
  obtain ⟨G', hG', g1, g2⟩ := hG
  exact ⟨G', hG'.congr_of_eventuallyEq h, g1, g2⟩

theorem WD_term (co : ℂ) (s s' : ℕ) (v : E) {c : Fin r → ℂ} (hc : c l ≠ 0) :
    WD l (fun x : Fin r → ℂ => (co * mu β n s s' (x l)) • v) c
      ((((β + n - s) * co) * mu β n s s' (c l)) • v) ((((β - s') * co) * mu β n s s' (c l)) • v) := by
  have h0 : HasFDerivAt (mu β n s s') (mu β n s s' (c l) • logD (β + n - s) (β - s') (c l)) (c l) := LD_mu β n s s' hc
  have h1 : HasFDerivAt (fun x : Fin r → ℂ => mu β n s s' (x l))
      ((mu β n s s' (c l) • logD (β + n - s) (β - s') (c l)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) l)) c :=
    HasFDerivAt.comp (g := mu β n s s') c h0
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) l).hasFDerivAt (x := c))
  have h2 := (h1.const_mul co).smul_const v
  have hs : (starRingEnd ℂ) (c l) ≠ 0 := (map_ne_zero _).2 hc
  refine ⟨_, h2, ?_, ?_⟩
  · simp only [ContinuousLinearMap.smulRight_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, Pi.single_eq_same, logD_apply, smul_eq_mul, smul_smul, ← sub_smul]
    congr 1
    simp only [star_one, Complex.star_def, Complex.conj_I]
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  · simp only [ContinuousLinearMap.smulRight_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, Pi.single_eq_same, logD_apply, smul_eq_mul, smul_smul, ← add_smul]
    congr 1
    simp only [star_one, Complex.star_def, Complex.conj_I]
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring

def sc (κ : ℕ → ℕ → ℂ) (L : List (Term k r E)) : List (Term k r E) :=
  L.map fun t => { t with co := κ t.s t.s' * t.co }

theorem WD_ev (L : List (Term k r E)) (g : Mx k r) {c : Fin r → ℂ} (hc : c l ≠ 0) :
    WD l (fun x => ev β n l L x g) c (ev β n l (sc (fun s _ => β + n - s) L) c g)
      (ev β n l (sc (fun _ s' => β - s') L) c g) := by
  induction L with
  | nil => exact WD.zero l c
  | cons t L ih =>
    simp only [sc, List.map_cons, ev_cons] at ih ⊢
    exact (WD_term β n l t.co t.s t.s' (t.Ψ g) hc).add l ih

theorem ev_sc_add (a : ℂ) (κ : ℕ → ℕ → ℂ) (L : List (Term k r E)) (c : Fin r → ℂ) (g : Mx k r) :
    ev β n l (sc (fun s s' => a + κ s s') L) c g = a • ev β n l L c g + ev β n l (sc κ L) c g := by
  induction L with
  | nil => simp [sc]
  | cons t L ih =>
    simp only [sc, List.map_cons, ev_cons] at ih ⊢
    rw [ih]; module

theorem ev_sc_sub (a : ℂ) (κ : ℕ → ℕ → ℂ) (L : List (Term k r E)) (c : Fin r → ℂ) (g : Mx k r) :
    ev β n l (sc (fun s s' => a - κ s s') L) c g = a • ev β n l L c g - ev β n l (sc κ L) c g := by
  induction L with
  | nil => simp [sc]
  | cons t L ih =>
    simp only [sc, List.map_cons, ev_cons] at ih ⊢
    rw [ih]; module

end Rep

section Rep2

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (β : ℂ) (n : ℤ) (l : Fin r)

theorem isOpen_omX (r : ℕ) : IsOpen (OmX r) := by
  have h : OmX r = ⋂ l, {x : Fin r → ℂ | x l ≠ 0} := by ext; simp [OmX]
  rw [h]
  exact isOpen_iInter_of_finite fun l => isOpen_ne.preimage (continuous_apply l)

def Rep (G : Set (Mx k r)) (Φ : Fn k r E) (L : List (Term k r E)) : Prop :=
  ∀ c ∈ OmX r, ∀ g ∈ G, Φ c g = ev β n l L c g

def shS (L : List (Term k r E)) : List (Term k r E) := L.map fun t => { t with s := t.s + 1 }

def shS' (L : List (Term k r E)) : List (Term k r E) := L.map fun t => { t with s' := t.s' + 1 }

def opQ (T : (Mx k r → E) → Mx k r → E) (L : List (Term k r E)) : List (Term k r E) :=
  L.map fun t => { t with Ψ := T t.Ψ }

def AllP (P : (Mx k r → E) → Prop) (L : List (Term k r E)) : Prop := ∀ t ∈ L, P t.Ψ

theorem AllP.sc {P : (Mx k r → E) → Prop} {L : List (Term k r E)} (h : AllP P L) (κ : ℕ → ℕ → ℂ) :
    AllP P (sc κ L) := by
  intro t ht
  simp only [Qx7.sc, List.mem_map] at ht
  obtain ⟨t', ht', rfl⟩ := ht
  exact h t' ht'

theorem AllP.shS {P : (Mx k r → E) → Prop} {L : List (Term k r E)} (h : AllP P L) : AllP P (shS L) := by
  intro t ht
  simp only [Qx7.shS, List.mem_map] at ht
  obtain ⟨t', ht', rfl⟩ := ht
  exact h t' ht'

theorem AllP.shS' {P : (Mx k r → E) → Prop} {L : List (Term k r E)} (h : AllP P L) : AllP P (shS' L) := by
  intro t ht
  simp only [Qx7.shS', List.mem_map] at ht
  obtain ⟨t', ht', rfl⟩ := ht
  exact h t' ht'

theorem AllP.opQ {P : (Mx k r → E) → Prop} {L : List (Term k r E)} (h : AllP P L)
    {T : (Mx k r → E) → Mx k r → E} (hT : ∀ f, P f → P (T f)) : AllP P (opQ T L) := by
  intro t ht
  simp only [Qx7.opQ, List.mem_map] at ht
  obtain ⟨t', ht', rfl⟩ := ht
  exact hT _ (h t' ht')

theorem AllP.append {P : (Mx k r → E) → Prop} {L L' : List (Term k r E)} (h : AllP P L) (h' : AllP P L') :
    AllP P (L ++ L') := by
  intro t ht
  rcases List.mem_append.1 ht with h1 | h1
  · exact h t h1
  · exact h' t h1

variable {β n l}

theorem Rep.pp {G : Set (Mx k r)} {Φ : Fn k r E} {L : List (Term k r E)} (h : Rep β n l G Φ L) (Y : ℂ) :
    Rep β n l G (crd (fun f => Y • f + pOp l f) Φ) (sc (fun s _ => Y + (β + n - s)) L) := by
  intro c hc g hg
  have hev : (fun c' => Φ c' g) =ᶠ[nhds c] fun c' => ev β n l L c' g := by
    filter_upwards [(isOpen_omX r).mem_nhds hc] with x hx using h x hx g hg
  have h1 := (((WD_ev β n l L g (hc l)).congr l hev).pOp l hc).1
  show (Y • (fun c' => Φ c' g) + pOp l (fun c' => Φ c' g)) c = _
  rw [Pi.add_apply, Pi.smul_apply, h1, h c hc g hg]
  exact (ev_sc_add β n l Y (fun s _ => β + n - s) L c g).symm

theorem Rep.pb {G : Set (Mx k r)} {Φ : Fn k r E} {L : List (Term k r E)} (h : Rep β n l G Φ L) (Y : ℂ) :
    Rep β n l G (crd (fun f => Y • f - pbOp l f) Φ) (sc (fun _ s' => Y - (β - s')) L) := by
  intro c hc g hg
  have hev : (fun c' => Φ c' g) =ᶠ[nhds c] fun c' => ev β n l L c' g := by
    filter_upwards [(isOpen_omX r).mem_nhds hc] with x hx using h x hx g hg
  have h1 := (((WD_ev β n l L g (hc l)).congr l hev).pOp l hc).2
  show (Y • (fun c' => Φ c' g) - pbOp l (fun c' => Φ c' g)) c = _
  rw [Pi.sub_apply, Pi.smul_apply, h1, h c hc g hg]
  exact (ev_sc_sub β n l Y (fun _ s' => β - s') L c g).symm

theorem ev_shS (L : List (Term k r E)) (c : Fin r → ℂ) (g : Mx k r) :
    ev β n l (shS L) c g = (c l)⁻¹ • ev β n l L c g := by
  induction L with
  | nil => simp [shS]
  | cons t L ih =>
    simp only [shS, List.map_cons, ev_cons] at ih ⊢
    rw [ih, smul_add, smul_smul]
    congr 2
    simp only [mu, pow_succ, mul_inv]
    ring

theorem ev_shS' (L : List (Term k r E)) (c : Fin r → ℂ) (g : Mx k r) :
    ev β n l (shS' L) c g = (star (c l))⁻¹ • ev β n l L c g := by
  induction L with
  | nil => simp [shS']
  | cons t L ih =>
    simp only [shS', List.map_cons, ev_cons] at ih ⊢
    rw [ih, smul_add, smul_smul]
    congr 2
    simp only [mu, pow_succ, mul_inv]
    ring

theorem Rep.ci {G : Set (Mx k r)} {Φ : Fn k r E} {L : List (Term k r E)} (h : Rep β n l G Φ L) :
    Rep β n l G (crd (ciOp l) Φ) (shS L) := by
  intro c hc g hg
  show (c l)⁻¹ • Φ c g = _
  rw [h c hc g hg, ev_shS]

theorem Rep.cbi {G : Set (Mx k r)} {Φ : Fn k r E} {L : List (Term k r E)} (h : Rep β n l G Φ L) :
    Rep β n l G (crd (cbiOp l) Φ) (shS' L) := by
  intro c hc g hg
  show (star (c l))⁻¹ • Φ c g = _
  rw [h c hc g hg, ev_shS']

theorem Rep.add {G : Set (Mx k r)} {Φ Φ' : Fn k r E} {L L' : List (Term k r E)} (h : Rep β n l G Φ L)
    (h' : Rep β n l G Φ' L') : Rep β n l G (Φ + Φ') (L ++ L') := by
  intro c hc g hg
  show Φ c g + Φ' c g = _
  rw [h c hc g hg, h' c hc g hg, ev_append]

theorem smooth_ev {i : Fin (r + 1)} {D : Set (Mx k r)} {L : List (Term k r E)}
    (hL : AllP (SmoothLev k r i D) L) (c : Fin r → ℂ) : SmoothLev k r i D (fun x => ev β n l L c x) := by
  induction L with
  | nil => exact Qx2.smooth_zero
  | cons t L ih =>
    simp only [ev_cons]
    exact Qx2.smooth_add (Qx2.smooth_smul (hL t (by simp)) _) (ih fun t' ht' => hL t' (by simp [ht']))

theorem LL_ev {i : Fin (r + 1)} {D : Set (Mx k r)} {T : (Mx k r → E) → Mx k r → E} (hT : Qx2.LL k r i D T)
    {L : List (Term k r E)} (hL : AllP (SmoothLev k r i D) L) (c : Fin r → ℂ) {g : Mx k r}
    (hg : g ∈ Glev k r i ∩ D) : T (fun x => ev β n l L c x) g = ev β n l (opQ T L) c g := by
  induction L with
  | nil =>
    have h := hT.lin (fun _ => 0) (fun _ => 0) 1 Qx2.smooth_zero Qx2.smooth_zero g hg
    simp only [smul_zero, add_zero, one_smul] at h
    simpa [opQ] using h
  | cons t L ih =>
    have hL' : AllP (SmoothLev k r i D) L := fun t' ht' => hL t' (by simp [ht'])
    have e : (fun x => ev β n l (t :: L) c x) =
        fun y => ev β n l L c y + (t.co * mu β n t.s t.s' (c l)) • t.Ψ y := by
      funext y; rw [ev_cons, add_comm]
    rw [e, hT.lin _ _ _ (smooth_ev hL' c) (hL t (by simp)) g hg, ih hL']
    simp only [opQ, List.map_cons, ev_cons]
    rw [add_comm]

theorem Rep.qq {i : Fin (r + 1)} {D : Set (Mx k r)} {T : (Mx k r → E) → Mx k r → E} (hT : Qx2.LL k r i D T)
    {Φ : Fn k r E} {L : List (Term k r E)} (h : Rep β n l (Glev k r i ∩ D) Φ L)
    (hL : AllP (SmoothLev k r i D) L) : Rep β n l (Glev k r i ∩ D) (grp T Φ) (opQ T L) := by
  intro c hc g hg
  show T (Φ c) g = _
  rw [hT.loc (Φ c) (fun x => ev β n l L c x) (fun x hx => h c hc x hx) g hg, LL_ev hT hL c hg]

end Rep2

section Chain

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def capelliCorner11OnTermSums (β : ℂ) (n : ℤ) (T : Fin 2 → Fin 2 → (Mx k r → E) → Mx k r → E) (Y : ℂ) (L : List (Term k r E)) :
    List (Term k r E) :=
  sc (fun _ s' => Y - (β - s')) (opQ (T 0 0) (sc (fun s _ => Y + (β + n - s)) L) ++ opQ (T 0 1) (shS L)) ++
    shS' (opQ (T 1 0) (sc (fun s _ => Y + (β + n - s)) L) ++ opQ (T 1 1) (shS L))

theorem AllP.capelliCorner11OnTermSums {P : (Mx k r → E) → Prop} {L : List (Term k r E)} (h : AllP P L) (β : ℂ) (n : ℤ)
    {T : Fin 2 → Fin 2 → (Mx k r → E) → Mx k r → E} (hT : ∀ a b f, P f → P (T a b f)) (Y : ℂ) :
    AllP P (capelliCorner11OnTermSums β n T Y L) :=
  ((((h.sc _).opQ (hT 0 0)).append (h.shS.opQ (hT 0 1))).sc _).append
    ((((h.sc _).opQ (hT 1 0)).append (h.shS.opQ (hT 1 1))).shS')

theorem Rep.chain {β : ℂ} {n : ℤ} {l : Fin r} {D : Set (Mx k r)} (hD : IsOpen D) (z z' : Fin (2 * r + k + 1) → ℂ)
    (Y : ℂ) {Φ : Fn k r E} {L : List (Term k r E)} (h : Rep β n l (Glev k r l.succ ∩ D) Φ L)
    (hL : AllP (SmoothLev k r l.succ D) L) :
    Rep β n l (Glev k r l.succ ∩ D) (oMul (TLs k l Y) (oMul (QL k r z z' l.succ Y) (TL k l Y)) 0 0 Φ)
      (capelliCorner11OnTermSums β n (tL k r z z' l.succ Y) Y L) := by
  have e : oMul (TLs k l Y) (oMul (QL k r z z' l.succ Y) (TL k l Y)) 0 0 Φ =
      crd (fun f => Y • f - pbOp l f)
        (grp (tL k r z z' l.succ Y 0 0) (crd (fun f => Y • f + pOp l f) Φ) +
          grp (tL k r z z' l.succ Y 0 1) (crd (ciOp l) Φ)) +
      crd (cbiOp l)
        (grp (tL k r z z' l.succ Y 1 0) (crd (fun f => Y • f + pOp l f) Φ) +
          grp (tL k r z z' l.succ Y 1 1) (crd (ciOp l) Φ)) := by
    simp only [oMul, Fin.sum_univ_two]
    rfl
  rw [e]
  have ll := fun a b => Qx2.ll_tL (E := E) (i := l.succ) hD z z' Y a b
  exact ((((h.pp Y).qq (ll 0 0) (hL.sc _)).add (h.ci.qq (ll 0 1) hL.shS)).pb Y).add
    ((((h.pp Y).qq (ll 1 0) (hL.sc _)).add (h.ci.qq (ll 1 1) hL.shS)).cbi)

end Chain

theorem smooth_phi (γ : ℂ) (n : ℤ) :
    ContDiffOn ℝ ∞ (fun x : ℂ => ((‖x‖ : ℝ) : ℂ) ^ (2 * γ) * x ^ n) {c | c ≠ 0} := by
  have h1 : ContDiffOn ℝ ∞ (fun x : ℂ => Complex.exp (γ * ((Real.log (‖x‖ ^ 2) : ℝ) : ℂ))) {c | c ≠ 0} := by
    refine (Complex.contDiff_exp (𝕜 := ℝ)).comp_contDiffOn (contDiffOn_const.mul
      (Complex.ofRealCLM.contDiff.comp_contDiffOn ?_))
    exact (contDiff_norm_sq ℝ).contDiffOn.log fun x hx => pow_ne_zero 2 (norm_ne_zero_iff.2 hx)
  have h2 : ContDiffOn ℝ ∞ (fun x : ℂ => ((‖x‖ : ℝ) : ℂ) ^ (2 * γ)) {c | c ≠ 0} :=
    h1.congr fun x hx => cpow_norm_eq γ hx
  have h3 : ContDiffOn ℝ ∞ (fun x : ℂ => x ^ n) {c | c ≠ 0} := by
    rcases n with m | m
    · simp only [Int.ofNat_eq_natCast, zpow_natCast]
      exact (contDiff_id.pow m).contDiffOn
    · simp only [zpow_negSucc]
      exact (contDiff_id.pow (m + 1)).contDiffOn.inv fun x hx => pow_ne_zero _ hx
  exact h2.mul h3

section W1

open scoped ComplexConjugate

variable {k r : ℕ}

local notation "⟪" u ", " v "⟫" => herm (Hpk k r) u v

lemma Hh : (Hpk k r)ᴴ = Hpk k r := B2x8.Hpk_herm k r

lemma herm_bvec_right (u : Fin (2 * r + k + 1) → ℂ) (j : Fin (2 * r + k + 1)) :
    ⟪u, bvec j⟫ = (Hpk k r *ᵥ u) j := by
  simp [herm, bvec, Pi.star_single]

lemma herm_e_right (u : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : ⟪u, bvec (eI k r a)⟫ = u (esI k r a) := by
  rw [herm_bvec_right, B2x6.hpk_mulVec]
  have h1 : WeylGroupFacts.tau k r (eI k r a) = esI k r a := by
    apply Fin.ext; rw [B2x6.tau_out _ (by simp only [eI]; omega)]; simp [eI, esI]
  have h2 : WeylGroupFacts.sgn k r (eI k r a) = 1 := by
    unfold WeylGroupFacts.sgn; rw [if_neg (by simp only [eI]; omega)]
  rw [h1, h2, one_mul]

lemma herm_es_right (u : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : ⟪u, bvec (esI k r a)⟫ = u (eI k r a) := by
  rw [herm_bvec_right, B2x6.hpk_mulVec]
  have h1 : WeylGroupFacts.tau k r (esI k r a) = eI k r a := by
    apply Fin.ext; rw [B2x6.tau_out _ (by simp only [esI]; omega)]; simp only [eI, esI]; omega
  have h2 : WeylGroupFacts.sgn k r (esI k r a) = 1 := by
    unfold WeylGroupFacts.sgn; rw [if_neg (by simp only [esI]; omega)]
  rw [h1, h2, one_mul]

lemma eI_ne_esI (a b : Fin r) : eI k r a ≠ esI k r b := by
  intro h; have := congrArg Fin.val h; simp only [eI, esI] at this; omega

lemma eI_inj {a b : Fin r} : eI k r a = eI k r b ↔ a = b := by
  constructor
  · intro h; have := congrArg Fin.val h; simp only [eI] at this; exact Fin.ext this
  · rintro rfl; rfl

lemma esI_inj {a b : Fin r} : esI k r a = esI k r b ↔ a = b := by
  constructor
  · intro h; have := congrArg Fin.val h; simp only [esI] at this; exact Fin.ext (by omega)
  · rintro rfl; rfl

lemma h_e_e (a b : Fin r) : ⟪bvec (eI k r a), bvec (eI k r b)⟫ = 0 := by
  rw [herm_e_right]; exact Pi.single_eq_of_ne (eI_ne_esI a b).symm _
lemma h_es_es (a b : Fin r) : ⟪bvec (esI k r a), bvec (esI k r b)⟫ = 0 := by
  rw [herm_es_right]; exact Pi.single_eq_of_ne (eI_ne_esI b a) _
lemma h_e_es (a b : Fin r) : ⟪bvec (eI k r a), bvec (esI k r b)⟫ = if a = b then 1 else 0 := by
  rw [herm_es_right]; simp only [bvec, Pi.single_apply, eI_inj]
  by_cases h : a = b
  · simp [h]
  · rw [if_neg h, if_neg (Ne.symm h)]
lemma h_es_e (a b : Fin r) : ⟪bvec (esI k r a), bvec (eI k r b)⟫ = if a = b then 1 else 0 := by
  rw [herm_e_right]; simp only [bvec, Pi.single_apply, esI_inj]
  by_cases h : a = b
  · simp [h]
  · rw [if_neg h, if_neg (Ne.symm h)]

variable {l : Fin r}

local notation "𝐞" => bvec (eI k r l)
local notation "𝐬" => bvec (esI k r l)

lemma weyl_cell_apply_dual_basis (c : ℂ) (q : Fin (2 * r + k + 1)) :
    w1 k r l c (esI k r l) q = if q = eI k r l then c else 0 := by
  unfold w1
  by_cases h : q = eI k r l
  · simp [h]
  · simp [h, (eI_ne_esI l l).symm]

lemma weyl_cell_apply_basis (c : ℂ) (q : Fin (2 * r + k + 1)) :
    w1 k r l c (eI k r l) q = if q = esI k r l then (star c)⁻¹ else 0 := by
  unfold w1
  by_cases h : q = esI k r l
  · simp [h, eI_ne_esI l l]
  · simp [h, eI_ne_esI l l]

lemma weyl_cell_apply_other (c : ℂ) {p : Fin (2 * r + k + 1)} (h1 : p ≠ eI k r l) (h2 : p ≠ esI k r l)
    (q : Fin (2 * r + k + 1)) : w1 k r l c p q = if q = p then 1 else 0 := by
  unfold w1
  by_cases h : q = p
  · simp [h, h1, h2]
  · simp [h1, h2, h, Ne.symm h]

lemma weyl_cell_mulVec (c : ℂ) (y : Fin (2 * r + k + 1) → ℂ) :
    w1 k r l c *ᵥ y = y + (c * ⟪y, 𝐬⟫ - ⟪y, 𝐞⟫) • 𝐬 + ((conj c)⁻¹ * ⟪y, 𝐞⟫ - ⟪y, 𝐬⟫) • 𝐞 := by
  ext p
  rw [herm_e_right, herm_es_right]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply, mulVec, dotProduct]
  by_cases h2 : p = esI k r l
  · subst h2
    simp only [weyl_cell_apply_dual_basis, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, (eI_ne_esI l l).symm, if_false]
    ring
  · by_cases h1 : p = eI k r l
    · subst h1
      simp only [weyl_cell_apply_basis, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, eI_ne_esI l l, if_false]
      rw [Complex.star_def]; ring
    · simp only [weyl_cell_apply_other c h1 h2, ite_mul, zero_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, h1, h2,
        if_false]
      ring

lemma weyl_cell_mem_level_group {c : ℂ} (hc : c ≠ 0) : w1 k r l c ∈ Glev k r l.castSucc := by
  have hc' : conj c ≠ 0 := (map_ne_zero _).2 hc
  refine ⟨?_, fun a ha => ?_⟩
  · apply B2x8.mem_UH_of
    intro u w
    have h1 : ⟪𝐞, w⟫ = conj ⟪w, 𝐞⟫ := (B2x8.herm_conj _ Hh _ _).symm
    have h2 : ⟪𝐬, w⟫ = conj ⟪w, 𝐬⟫ := (B2x8.herm_conj _ Hh _ _).symm
    rw [weyl_cell_mulVec, weyl_cell_mulVec]
    simp only [B2x8.herm_add_left, B2x8.herm_add_right, B2x8.herm_smul_left, B2x8.herm_smul_right, h_e_e, h_es_es,
      h_e_es, h_es_e, if_true, h1, h2, map_sub, map_mul, map_inv₀, Complex.conj_conj]
    field_simp
    ring
  · have hne : a ≠ l := fun h' => by
      rw [h', Fin.val_castSucc] at ha; exact lt_irrefl l.val ha
    constructor
    · rw [weyl_cell_mulVec, h_e_e, h_e_es, if_neg hne]; simp
    · rw [weyl_cell_mulVec, h_es_e, h_es_es, if_neg hne]; simp

lemma reflection_mul_mem_lower_level {c : ℂ} (hc : c ≠ 0) {g : Mx k r} (hg : g ∈ Glev k r l.succ) :
    w1 k r l c * g ∈ Glev k r l.castSucc := by
  have hw := weyl_cell_mem_level_group (k := k) (r := r) (l := l) hc
  have hlt : ∀ a : Fin r, a.val < l.castSucc.val → a.val < l.succ.val := fun a ha => by
    simp only [Fin.val_castSucc, Fin.val_succ] at *; omega
  exact ⟨B2x8.al_mul_mem hw.1 hg.1, fun a ha =>
    ⟨by rw [← Matrix.mulVec_mulVec, (hg.2 a (hlt a ha)).1, (hw.2 a ha).1],
      by rw [← Matrix.mulVec_mulVec, (hg.2 a (hlt a ha)).2, (hw.2 a ha).2]⟩⟩

end W1

section Generic

theorem AllP.mono {k r : ℕ} {E : Type*} {P Q : (Mx k r → E) → Prop} {L : List (Term k r E)} (h : AllP P L)
    (hPQ : ∀ f, P f → Q f) : AllP Q L := fun t ht => hPQ _ (h t ht)

def xAB {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (r + 1)) (J : Mx k r → E) (g : Mx k r) (Y Y' : ℂ) (A B : Fin 2 × Fin 2) : E :=
  (Y' - Y) • (tL k r z z' i Y' A.1 B.1 (tL k r z z' i Y A.2 B.2 J) g -
      tL k r z z' i Y A.2 B.2 (tL k r z z' i Y' A.1 B.1 J) g) -
    (tL k r z z' i Y' A.2 B.1 (tL k r z z' i Y A.1 B.2 J) g - tL k r z z' i Y A.2 B.1 (tL k r z z' i Y' A.1 B.2 J) g)

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

theorem rtt_generic (hCS : ChainStep) (hRS : ResSurj) (hCC : CapCommute) (hTP : TPreservesFF) (hInd : RTTIndependence)
    (k r : ℕ) (l : Fin r) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Mx k r)) (hz : inWb k r z) (hz' : inWb k r z') (hD : IsDom k r z z' l.succ D)
    (J : Mx k r → (Wq →L[ℂ] Wp)) (hJ : J ∈ FFl k r z z' π π' l.succ D) (g : Mx k r) (hg : g ∈ Glev k r l.succ ∩ D)
    (Y Y' : ℂ) (hne : Y' ≠ Y + 1) (A B : Fin 2 × Fin 2) : xAB k r z z' l.succ J g Y Y' A B = 0 := by
  refine hInd (Wq →L[ℂ] Wp) (xAB k r z z' l.succ J g Y Y') Y Y' hne ?_ A B
  intro c₀ hc₀ β n
  obtain ⟨D₀, hD₀, -, hiff, Jt, hJt, hval⟩ := hRS Wp Wq k r z z' π π' l D
    (fun x : ℂ => ((‖x‖ : ℝ) : ℂ) ^ (2 * (β - ((Mdim k r l - 1 : ℕ) : ℂ) / 2)) * x ^ n) J hz hz' hD (smooth_phi _ n) hJ
  have rep0 : Rep β n l (Glev k r l.succ ∩ D) (res1 k r l Jt) [⟨1, 0, 0, J⟩] := by
    intro c hc x hx
    show ((‖c l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ) • Jt (w1 k r l (c l) * x) = _
    rw [hval (c l) (hc l) x hx, smul_smul]
    simp only [ev_cons, ev_nil, add_zero]
    congr 1
    have h0 : ((‖c l‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 (hc l)
    have e : ((‖c l‖ : ℝ) : ℂ) ^ (2 * β) = ((‖c l‖ : ℝ) : ℂ) ^ (((Mdim k r l - 1 : ℕ)) : ℂ) *
        ((‖c l‖ : ℝ) : ℂ) ^ (2 * (β - ((Mdim k r l - 1 : ℕ) : ℂ) / 2)) := by
      rw [← Complex.cpow_add _ _ h0]; congr 1; ring
    rw [mu, e, Complex.cpow_natCast]
    push_cast
    simp only [pow_zero, inv_one, mul_one, one_mul]
    ring
  have step : ∀ (y : ℂ) (J' : Mx k r → (Wq →L[ℂ] Wp)) (L : List (Term k r (Wq →L[ℂ] Wp))),
      J' ∈ FFl k r z z' π π' l.castSucc D₀ → Rep β n l (Glev k r l.succ ∩ D) (res1 k r l J') L →
      AllP (fun f => f ∈ FFl k r z z' π π' l.succ D) L →
      Rep β n l (Glev k r l.succ ∩ D) (res1 k r l (tL k r z z' l.castSucc y 0 0 J'))
        (capelliCorner11OnTermSums β n (tL k r z z' l.succ y) y L) := by
    intro y J' L hJ' hR hL c hc x hx
    rw [hCS Wp Wq k r z z' π π' l D₀ y 0 0 hz hz' hD₀ J' hJ' c hc x hx.1 ((hiff (c l) (hc l) x hx.1).2 hx.2)]
    exact Rep.chain hD.1 z z' y hR (hL.mono fun f hf => hf.1) c hc x hx
  have all0 : AllP (fun f => f ∈ FFl k r z z' π π' l.succ D) [(⟨1, 0, 0, J⟩ : Term k r (Wq →L[ℂ] Wp))] := by
    intro t ht
    rw [List.mem_singleton] at ht
    subst ht
    exact hJ
  have hP : ∀ (y : ℂ) (a b : Fin 2) (f : Mx k r → (Wq →L[ℂ] Wp)), f ∈ FFl k r z z' π π' l.succ D →
      tL k r z z' l.succ y a b f ∈ FFl k r z z' π π' l.succ D :=
    fun y a b f hf => hTP Wp Wq k r z z' π π' l.succ D y a b hz hz' hD f hf
  have hA : ∀ y : ℂ, tL k r z z' l.castSucc y 0 0 Jt ∈ FFl k r z z' π π' l.castSucc D₀ :=
    fun y => hTP Wp Wq k r z z' π π' l.castSucc D₀ y 0 0 hz hz' hD₀ Jt hJt
  have r1 := step Y' _ _ (hA Y) (step Y Jt _ hJt rep0 all0) (all0.capelliCorner11OnTermSums β n (hP Y) Y)
  have r2 := step Y _ _ (hA Y') (step Y' Jt _ hJt rep0 all0) (all0.capelliCorner11OnTermSums β n (hP Y') Y')
  have hc : (fun _ : Fin r => c₀) ∈ OmX r := fun _ => hc₀
  have hmem : w1 k r l c₀ * g ∈ Glev k r l.castSucc ∩ D₀ :=
    ⟨reflection_mul_mem_lower_level hc₀ hg.1, (hiff c₀ hc₀ g hg.1).2 hg.2⟩
  have comm := hCC (Wq →L[ℂ] Wp) k r l.castSucc D₀ Jt hD₀.1 hJt.1 _ hmem (uC k r l.castSucc Y') (uC k r l.castSucc Y)
  have key := (r1 _ hc g hg).symm.trans ((congrArg (fun v => ((‖c₀‖ ^ (Mdim k r l - 1) : ℝ) : ℂ) • v) comm).trans (r2 _ hc g hg))
  simp only [capelliCorner11OnTermSums, sc, shS, shS', opQ, List.map_cons, List.map_nil, List.cons_append, List.nil_append, ev_cons, ev_nil,
    mu] at key
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, xAB, Prod.mk.injEq, Fin.isValue, zero_ne_one, one_ne_zero,
    and_true, and_false, ↓reduceIte, Fin.val_zero, Fin.val_one]
  linear_combination (norm := module) (Y' - Y - 1) • key

end Generic

section Cont

open Polynomial in
theorem polyAt_interp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {N : ℕ} {φ : ℂ → E}
    (h : Qx2.PolyAt N φ) (Y : ℂ) :
    φ Y = ∑ i ∈ Finset.range N,
      (Lagrange.basis (Finset.range N) (fun i : ℕ => (i : ℂ)) i).eval Y • φ (i : ℂ) := by
  obtain ⟨c, hc⟩ := h
  have hinj : Set.InjOn (fun i : ℕ => (i : ℂ)) (Finset.range N) := fun a _ b _ h => Nat.cast_injective h
  have hpow : ∀ j ∈ Finset.range N, Y ^ j = ∑ i ∈ Finset.range N,
      (Lagrange.basis (Finset.range N) (fun i : ℕ => (i : ℂ)) i).eval Y * (i : ℂ) ^ j := by
    intro j hj
    have hdeg : (X ^ j : ℂ[X]).degree < (Finset.range N).card := by
      rw [degree_X_pow, Finset.card_range]; exact_mod_cast Finset.mem_range.1 hj
    have h1 := congrArg (Polynomial.eval Y) (Lagrange.eq_interpolate hinj hdeg)
    simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X] at h1
    rw [h1]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  simp only [hc, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← Finset.sum_smul, ← hpow j hj]

theorem polyAt_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {N : ℕ} {φ : ℂ → E}
    (h : Qx2.PolyAt N φ) : Continuous φ := by
  obtain ⟨c, hc⟩ := h
  rw [show φ = fun Y => ∑ j ∈ Finset.range N, Y ^ j • c j from funext hc]
  exact continuous_finsetSum _ fun j _ => (continuous_pow j).smul continuous_const

theorem LL_sum {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
    {T : (Mx k r → E) → Mx k r → E} (hT : Qx2.LL k r i D T) (a : ℕ → ℂ)
    {c : ℕ → Mx k r → E} (hc : ∀ j, SmoothLev k r i D (c j)) {x : Mx k r} (hx : x ∈ Glev k r i ∩ D) (N : ℕ) :
    T (fun y => ∑ j ∈ Finset.range N, a j • c j y) x = ∑ j ∈ Finset.range N, a j • T (c j) x := by
  induction N with
  | zero =>
    have h := hT.lin (fun _ => 0) (fun _ => 0) 1 Qx2.smooth_zero Qx2.smooth_zero x hx
    simp only [smul_zero, add_zero, one_smul] at h
    simpa using h
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    rw [hT.lin _ _ (a N) (Qx2.smooth_lin_sum a hc N) (hc N) x hx, ih]

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem polyAt_tL (hLead : Leading) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (hz : inWb k r z)
    (hz' : inWb k r z') {D : Set (Mx k r)} (hD : IsOpen D) {f : Mx k r → E} (hf : SmoothLev k r i D f)
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) (a b : Fin 2) :
    Qx2.PolyAt (mdim k r i + 1) (fun Y => tL k r z z' i Y a b f g) := by
  obtain ⟨A, hA⟩ := hLead E k r z z' i hz hz'
  have h := hA D f hD hf g hg
  have hm : mdim k r i - 1 + 1 = mdim k r i := by unfold mdim; omega
  have low : ∀ p q : Fin 2, Qx2.PolyAt (mdim k r i)
      (fun Y : ℂ => ∑ j ∈ Finset.range (mdim k r i - 1), Y ^ j • A p q j f g) := by
    intro p q
    have h1 : Qx2.PolyAt (mdim k r i - 1 + 1)
        (fun Y : ℂ => ∑ j ∈ Finset.range (mdim k r i - 1), Y ^ j • A p q j f g) :=
      Qx2.PolyAt.succ ⟨fun j => A p q j f g, fun _ => rfl⟩
    rwa [hm] at h1
  have top : ∀ e : E, Qx2.PolyAt (mdim k r i) (fun Y : ℂ => Y ^ (mdim k r i - 1) • e) := by
    intro e
    have h1 := Qx2.polyAt_monomial (mdim k r i - 1) e
    rwa [hm] at h1
  have h00 : Qx2.PolyAt (mdim k r i + 1) (fun Y => tL k r z z' i Y 0 0 f g) :=
    ((Qx2.polyAt_monomial (mdim k r i) (f g)).add
      (Qx2.PolyAt.succ ⟨fun j => A 0 0 j f g, fun _ => rfl⟩)).congr fun Y => (h Y).1
  have h01 : Qx2.PolyAt (mdim k r i + 1) (fun Y => tL k r z z' i Y 0 1 f g) :=
    (((top (zetaL k r z z' i g • f g)).neg.add (low 0 1)).succ).congr fun Y => by
      rw [(h Y).2.1, smul_smul, mul_comm]
  have h10 : Qx2.PolyAt (mdim k r i + 1) (fun Y => tL k r z z' i Y 1 0 f g) :=
    (((top (star (zetaL k r z z' i g) • f g)).neg.add (low 1 0)).succ).congr fun Y => by
      rw [(h Y).2.2.1, smul_smul, mul_comm]
  have h11 : Qx2.PolyAt (mdim k r i + 1) (fun Y => tL k r z z' i Y 1 1 f g) :=
    ((low 1 1).succ).congr fun Y => (h Y).2.2.2
  fin_cases a <;> fin_cases b
  exacts [h00, h01, h10, h11]

theorem cont_inner (hLead : Leading) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (hz : inWb k r z)
    (hz' : inWb k r z') {D : Set (Mx k r)} (hD : IsOpen D) {f : Mx k r → E} (hf : SmoothLev k r i D f)
    (a b : Fin 2) (hs : ∀ u : ℂ, SmoothLev k r i D (tL k r z z' i u a b f))
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) (v : ℂ) (c d : Fin 2) :
    Continuous (fun u => tL k r z z' i v c d (tL k r z z' i u a b f) g) := by
  have ll := Qx2.ll_tL (E := E) (i := i) hD z z' v c d
  have hrep : ∀ u : ℂ, tL k r z z' i v c d (tL k r z z' i u a b f) g =
      ∑ j ∈ Finset.range (mdim k r i + 1),
        (Lagrange.basis (Finset.range (mdim k r i + 1)) (fun j : ℕ => (j : ℂ)) j).eval u •
          tL k r z z' i v c d (tL k r z z' i (j : ℂ) a b f) g := by
    intro u
    rw [ll.loc (tL k r z z' i u a b f) (fun x => ∑ j ∈ Finset.range (mdim k r i + 1),
        (Lagrange.basis (Finset.range (mdim k r i + 1)) (fun j : ℕ => (j : ℂ)) j).eval u •
          tL k r z z' i (j : ℂ) a b f x)
      (fun x hx => polyAt_interp (polyAt_tL hLead z z' i hz hz' hD hf hx a b) u) g hg]
    exact LL_sum ll _ (fun j => hs (j : ℂ)) hg _
  rw [show (fun u => tL k r z z' i v c d (tL k r z z' i u a b f) g) = _ from funext hrep]
  exact continuous_finsetSum _ fun j _ => (Polynomial.continuous _).smul continuous_const

end Cont

theorem upper_from_steps : Formalism.FourierDecayAlt.Q.RTTUpperFromSteps := by
  intro hCS hRS hCC hTP _ _ hInd hLead _ k r l Wp Wq _ _ _ _ z z' π π' D hz hz' hD J hJ g hg u v a b c d
  have hP : ∀ (y : ℂ) (p q : Fin 2), tL k r z z' l.succ y p q J ∈ FFl k r z z' π π' l.succ D :=
    fun y p q => hTP Wp Wq k r z z' π π' l.succ D y p q hz hz' hD J hJ
  have c1 : ∀ (p q p' q' : Fin 2),
      Continuous (fun u' => tL k r z z' l.succ u' p q (tL k r z z' l.succ v p' q' J) g) := fun p q p' q' =>
    polyAt_continuous (polyAt_tL hLead z z' l.succ hz hz' hD.1 (hP v p' q').1 hg p q)
  have c2 : ∀ (p q p' q' : Fin 2),
      Continuous (fun u' => tL k r z z' l.succ v p q (tL k r z z' l.succ u' p' q' J) g) := fun p q p' q' =>
    cont_inner hLead z z' l.succ hz hz' hD.1 hJ.1 p' q' (fun y => (hP y p' q').1) hg v p q
  have hcont : Continuous (fun u' => xAB k r z z' l.succ J g v u' (a, c) (b, d)) :=
    ((continuous_id.sub continuous_const).smul ((c1 a b c d).sub (c2 c d a b))).sub ((c1 c b a d).sub (c2 c b a d))
  have hcl : IsClosed {u' : ℂ | xAB k r z z' l.succ J g v u' (a, c) (b, d) = 0} := isClosed_eq hcont continuous_const
  have hsub : {u' : ℂ | u' ≠ v + 1} ⊆ {u' : ℂ | xAB k r z z' l.succ J g v u' (a, c) (b, d) = 0} := fun u' hu' =>
    rtt_generic hCS hRS hCC hTP hInd k r l z z' π π' D hz hz' hD J hJ g hg v u' hu' (a, c) (b, d)
  have hden : Dense {u' : ℂ | u' ≠ v + 1} := dense_compl_singleton (v + 1)
  have h0 : xAB k r z z' l.succ J g v u (a, c) (b, d) = 0 :=
    (closure_minimal hsub hcl) (hden.closure_eq ▸ Set.mem_univ u)
  exact sub_eq_zero.1 h0

end Formalism.FourierDecayAlt.P.Qx7

namespace Formalism.FourierDecayAlt.P

theorem quantum_determinant_from_rtt : Formalism.FourierDecayAlt.Q.QdetFromRTT := Qx7.qdet_main

theorem rtt_upper_relations_from_descent : Formalism.FourierDecayAlt.Q.RTTUpperFromSteps := Qx7.upper_from_steps

end Formalism.FourierDecayAlt.P
