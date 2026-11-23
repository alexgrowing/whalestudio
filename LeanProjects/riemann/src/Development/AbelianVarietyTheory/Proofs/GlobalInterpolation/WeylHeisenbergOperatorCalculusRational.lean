import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.Heis

theorem HV_conj {ι : Type} [Fintype ι] {a b : ℕ} (sc : ℝ) (x y : VV ι a b) :
    Formalism.L2.Ker.HV sc y x = (starRingEnd ℂ) (Formalism.L2.Ker.HV sc x y) := by
  simp only [Formalism.L2.Ker.HV, LinearMap.mk₂'ₛₗ_apply, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem alpha_opU_mul {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V)
    (hH : ∀ x y, H y x = (starRingEnd ℂ) (H x y)) (c : ℝ) (x y : V) (F : V → ℂ) (z : V) :
    alphaQ (c / 2) H x * opU H x (fun w => alphaQ (c / 2) H y * opU H y F w) z =
      Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (((c * (H x y).re + (H x y).im) / 2 : ℝ) : ℂ)) *
        (alphaQ (c / 2) H (x + y) * opU H (x + y) F z) := by
  simp only [alphaQ, opU, Formalism.L2.Th1.H.qOf]
  rw [← add_assoc z x y]
  have key : ∀ a b c d e f g u : ℂ, a + b + c + d = e + f + g →
      Complex.exp a * (Complex.exp b * (u * Complex.exp c) * Complex.exp d) =
        Complex.exp e * (Complex.exp f * (u * Complex.exp g)) := by
    intro a b c d e f g u h
    have : Complex.exp a * Complex.exp b * Complex.exp c * Complex.exp d =
        Complex.exp e * Complex.exp f * Complex.exp g := by
      simp only [← Complex.exp_add, h]
    linear_combination u * this
  apply key
  simp only [map_add, LinearMap.add_apply]
  rw [hH x y]
  have h1 : H x y = ((H x y).re : ℂ) + ((H x y).im : ℂ) * Complex.I := (Complex.re_add_im _).symm
  have h2 : (starRingEnd ℂ) (H x y) = ((H x y).re : ℂ) - ((H x y).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  simp only [Complex.add_re, Complex.conj_re]
  rw [h2]
  generalize (H x y).re = r at *
  generalize (H x y).im = s at *
  rw [h1]
  push_cast
  ring

variable {X : Fields} (A : Amb X) {a b : ℕ}

theorem emb_add (x y : HomE X.E a b) : emb A (x + y) = emb A x + emb A y := map_add _ x y

theorem Wx_Wx (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ) :
    Wx A x (Wx A y F) = fun z => Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (coc A x y : ℂ)) * Wx A (x + y) F z := by
  funext z
  have := alpha_opU_mul (Formalism.L2.Ker.HV A.sc) (fun x y => HV_conj A.sc x y) (Real.sqrt A.d) (emb A x) (emb A y) F z
  rw [← emb_add] at this
  exact this

theorem imH_eq (x y : HomE X.E a b) : imH A x y = coc A x y - coc A y x := by
  simp only [coc, imH, altE]
  rw [HV_conj A.sc (emb A x) (emb A y)]
  simp only [Complex.conj_re, Complex.conj_im]
  ring

theorem imH_add_left (x y z : HomE X.E a b) : imH A (x + y) z = imH A x z + imH A y z := by
  simp only [imH, altE, emb_add, map_add, LinearMap.add_apply, Complex.add_im]

theorem imH_add_right (x y z : HomE X.E a b) : imH A x (y + z) = imH A x y + imH A x z := by
  simp only [imH, altE, emb_add, map_add, LinearMap.add_apply, Complex.add_im]

theorem Wx_comm (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ) :
    Wx A x (Wx A y F) = fun z => brkE A y x * Wx A y (Wx A x F) z := by
  rw [Wx_Wx, Wx_Wx, add_comm y x]
  funext z
  have : brkE A y x = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (imH A x y : ℂ)) := rfl
  rw [this, ← mul_assoc, ← Complex.exp_add, imH_eq]
  congr 2
  push_cast
  ring

theorem contDiff_Wx (x : HomE X.E a b) (F : VCx X.Tau a b → ℂ) (k : ℕ) (hF : ContDiff ℂ k F) :
    ContDiff ℂ k (Wx A x F) := by
  have h : ContDiff ℂ k (fun z : VCx X.Tau a b => Formalism.L2.Ker.HV A.sc z (emb A x)) := by
    simp only [Formalism.L2.Ker.HV, LinearMap.mk₂'ₛₗ_apply]
    fun_prop
  unfold Wx opU
  exact contDiff_const.mul ((hF.comp (contDiff_id.add contDiff_const)).mul
    (((contDiff_const.mul h).sub contDiff_const).cexp))

theorem jetC_sum (κ : Type) (T : Finset κ) (c : κ → ℂ) (F : κ → VCx X.Tau a b → ℂ)
    (hF : ∀ i ∈ T, ∀ k : ℕ, ContDiff ℂ k (F i)) (m : DVar X.Tau a b →₀ ℕ) :
    jetC A.cD (fun z => ∑ i ∈ T, c i * F i z) m = ∑ i ∈ T, c i * jetC A.cD (F i) m := by
  classical
  have hd : ∀ n : ℕ, iteratedFDeriv ℂ n (fun z => ∑ i ∈ T, c i * F i z) 0 = ∑ i ∈ T, c i • iteratedFDeriv ℂ n (F i) 0 := by
    intro n
    have e : (fun z => ∑ i ∈ T, c i * F i z) = ∑ i ∈ T, c i • F i := by
      funext z; simp
    rw [e, iteratedFDeriv_sum_apply (f := fun i => c i • F i) (fun i hi => ((hF i hi n).const_smul (c i)).contDiffAt)]
    exact Finset.sum_congr rfl fun i hi => iteratedFDeriv_const_smul_apply (hF i hi n).contDiffAt
  simp only [jetC, derivAt0, hd, ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem calculus : ∀ (X : Fields) (A : Amb X) (a b : ℕ), (∀ (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ), Wx A x (Wx A y F) = fun z => Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (coc A x y : ℂ)) * Wx A (x + y) F z) ∧ (∀ (x y : HomE X.E a b) (F : VCx X.Tau a b → ℂ), Wx A x (Wx A y F) = fun z => brkE A y x * Wx A y (Wx A x F) z) ∧ (∀ x y : HomE X.E a b, imH A x y = coc A x y - coc A y x) ∧ (∀ x y z : HomE X.E a b, coc A (x + y) z = coc A x z + coc A y z ∧ coc A x (y + z) = coc A x y + coc A x z ∧ imH A (x + y) z = imH A x z + imH A y z ∧ imH A x (y + z) = imH A x y + imH A x z) ∧ (∀ y t : HomE X.E a b, brkE A y t = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (imH A t y : ℂ))) ∧ (∀ y t : HomE X.E a b, brkE A y t = 1 ↔ ∃ n : ℤ, imH A t y = n) ∧ (∀ (x : HomE X.E a b) (F : VCx X.Tau a b → ℂ), (∀ k : ℕ, ContDiff ℂ k F) → ∀ k : ℕ, ContDiff ℂ k (Wx A x F)) ∧ (∀ (κ : Type) (T : Finset κ) (c : κ → ℂ) (F : κ → VCx X.Tau a b → ℂ), (∀ i ∈ T, ∀ k : ℕ, ContDiff ℂ k (F i)) → ∀ m, jetC A.cD (fun z => ∑ i ∈ T, c i * F i z) m = ∑ i ∈ T, c i * jetC A.cD (F i) m) := by
  intro X A a b
  refine ⟨Wx_Wx A, Wx_comm A, imH_eq A, fun x y z => ⟨?_, ?_, imH_add_left A x y z, imH_add_right A x y z⟩,
    fun _ _ => rfl, fun y t => ?_, fun x F hF k => contDiff_Wx A x F k (hF k), fun κ T c F hF m => jetC_sum A κ T c F hF m⟩
  · simp only [coc, imH_add_left, emb_add, map_add, LinearMap.add_apply, Complex.add_re]; ring
  · simp only [coc, imH_add_right, emb_add, map_add, LinearMap.add_apply, Complex.add_re]; ring
  · have : brkE A y t = Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (imH A t y : ℂ)) := rfl
    rw [this, Complex.exp_eq_one_iff]
    have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨-n, ?_⟩
      have : ((imH A t y : ℝ) : ℂ) = ((-n : ℤ) : ℂ) := by
        apply mul_left_cancel₀ hne
        push_cast
        linear_combination -hn
      exact_mod_cast this
    · rintro ⟨n, hn⟩
      refine ⟨-n, ?_⟩
      rw [hn]
      push_cast
      ring

end GlobalTheory.MomT.Heis
