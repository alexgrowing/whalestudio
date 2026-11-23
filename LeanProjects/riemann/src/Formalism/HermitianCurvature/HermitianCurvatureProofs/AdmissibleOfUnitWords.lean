import Formalism.HermitianCurvature.HermitianCurvatureProofs.SplLen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.PolynomialBound

open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def sc (ε x : ℝ) : ℝ := Real.smoothTransition ((x - ε / 4) / (ε / 4))

lemma sc_zero {ε x : ℝ} (hε : 0 < ε) (hx : x ≤ ε / 4) : sc ε x = 0 := by
  unfold sc
  exact Real.smoothTransition.zero_of_nonpos (div_nonpos_iff.2 (Or.inr ⟨by linarith, by linarith⟩))

lemma sc_one {ε x : ℝ} (hε : 0 < ε) (hx : ε / 2 ≤ x) : sc ε x = 1 := by
  unfold sc
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by linarith)]
  linarith

lemma sc_cd (ε : ℝ) : ContDiff ℝ ∞ (sc ε) := by
  show ContDiff ℝ ∞ (fun x => Real.smoothTransition ((x - ε / 4) / (ε / 4)))
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

def hh (ε x : ℝ) : ℝ := sc ε x * x ^ (-(1 / 2 : ℝ))

lemma hh_cd {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (hh ε) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : ε / 8 < x
  · have hx0 : 0 < x := by linarith
    show ContDiffAt ℝ ∞ (fun y => sc ε y * y ^ (-(1 / 2 : ℝ))) x
    exact ((sc_cd ε).contDiffAt).mul (Real.contDiffAt_rpow_const_of_ne hx0.ne')
  · have h0 : hh ε =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show x < ε / 4 by linarith)] with y hy
      simp [hh, sc_zero hε (le_of_lt hy)]
    exact contDiffAt_const.congr_of_eventuallyEq h0

lemma hh_ev {ε x : ℝ} (hε : 0 < ε) (hx : ε / 2 < x) :
    hh ε =ᶠ[nhds x] fun y => y ^ (-(1 / 2 : ℝ)) := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  simp only [hh, sc_one hε (le_of_lt hy), one_mul]

lemma hh_bound {ε : ℝ} (hε : 0 < ε) (j : ℕ) {x : ℝ} (hx : ε ≤ x) :
    ‖iteratedFDeriv ℝ j (hh ε) x‖ ≤ |(descPochhammer ℝ j).eval (-(1 / 2 : ℝ))| * ε ^ (-(1 / 2 : ℝ) - j) := by
  have hx0 : 0 < x := lt_of_lt_of_le hε hx
  have h2 : ε / 2 < x := by linarith
  have heq : iteratedFDeriv ℝ j (hh ε) x = iteratedFDeriv ℝ j (fun y : ℝ => y ^ (-(1 / 2 : ℝ))) x := by
    first
    | exact ((hh_ev hε h2).iteratedFDeriv ℝ j).eq_of_nhds
    | exact (hh_ev hε h2).iteratedFDeriv_eq j
  rw [heq, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate]
  simp only [Real.iter_deriv_rpow_const]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hexp : -(1 / 2 : ℝ) - j ≤ 0 := by linarith
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  first
  | exact Real.rpow_le_rpow_of_exponent_nonpos hε hx hexp
  | exact Real.rpow_le_rpow_of_nonpos hε hx hexp

def Phh (ε : ℝ) (z : ℂ) : ℂ := ((hh ε z.re : ℝ) : ℂ)

lemma Phh_cd {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (Phh ε) := by
  show ContDiff ℝ ∞ (fun z : ℂ => ((hh ε z.re : ℝ) : ℂ))
  exact Complex.ofRealCLM.contDiff.comp ((hh_cd hε).comp Complex.reCLM.contDiff)

lemma Phh_bound {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    ∃ B : ℝ, ∀ z ∈ {z : ℂ | ε ≤ z.re}, ‖iteratedFDeriv ℝ j (Phh ε) z‖ ≤ B := by
  refine ⟨‖Complex.ofRealCLM‖ * (|(descPochhammer ℝ j).eval (-(1 / 2 : ℝ))| * ε ^ (-(1 / 2 : ℝ) - j) *
    ‖Complex.reCLM‖ ^ j), fun z hz => ?_⟩
  have hh' : ContDiff ℝ ∞ (hh ε ∘ Complex.reCLM) := (hh_cd hε).comp Complex.reCLM.contDiff
  have e : Phh ε = Complex.ofRealCLM ∘ (hh ε ∘ Complex.reCLM) := rfl
  rw [e]
  calc ‖iteratedFDeriv ℝ j (Complex.ofRealCLM ∘ (hh ε ∘ Complex.reCLM)) z‖
      ≤ ‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ j (hh ε ∘ Complex.reCLM) z‖ :=
        by
          first
          | exact Complex.ofRealCLM.norm_iteratedFDeriv_comp_left hh'.contDiffAt (by exact_mod_cast le_top)
          | exact Complex.ofRealCLM.norm_iteratedFDeriv_comp_left hh' z (by exact_mod_cast le_top)
          | exact Complex.ofRealCLM.norm_iteratedFDeriv_comp_left hh'.contDiffAt z (by exact_mod_cast le_top)
    _ ≤ _ := by
        gcongr
        calc ‖iteratedFDeriv ℝ j (hh ε ∘ Complex.reCLM) z‖
            = ‖(iteratedFDeriv ℝ j (hh ε) (Complex.reCLM z)).compContinuousLinearMap
                fun _ => Complex.reCLM‖ := by
              first
              | rw [Complex.reCLM.iteratedFDeriv_comp_right (hh_cd hε) z (by exact_mod_cast le_top)]
              | rw [Complex.reCLM.iteratedFDeriv_comp_right (hh_cd hε).contDiffAt (by exact_mod_cast le_top)]
              | rw [Complex.reCLM.iteratedFDeriv_comp_right (hh_cd hε) (by exact_mod_cast le_top)]
          _ ≤ ‖iteratedFDeriv ℝ j (hh ε) (Complex.reCLM z)‖ * ∏ _i : Fin j, ‖Complex.reCLM‖ :=
              ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
          _ = ‖iteratedFDeriv ℝ j (hh ε) (Complex.reCLM z)‖ * ‖Complex.reCLM‖ ^ j := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          _ ≤ _ := by
              gcongr
              exact hh_bound hε j hz

lemma sqrt_div_eq {T x : ℝ} (hT : 0 < T) (hx : 0 < x) : Real.sqrt (T / x) = Real.sqrt T * x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_div hT.le x, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]

end Formalism.FourierDecayAlt.P.AdmissibleLieWords

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma admissible_of_unit_words {k r i : ℕ} {u v : List (Mat k r)} (h : C6.UnitWords k r u v i) : admitted i (wL u ++ wR v) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨u, v, h1, h2, h3.le, rfl⟩

lemma poly_adm {k r d n : ℕ} {P : Mat k r → ℂ} (hP : U.IsPolyDeg d P) :
    ContDiff ℝ ∞ P ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ w, admitted n w → ∀ g ∈ GV k r, ‖Dw w P g‖ ≤ C * gN g ^ d := by
  obtain ⟨hc, hb⟩ := PI.UnitaryCorollaryDerivatives.polynomial_bound k r d P hP
  refine ⟨hc, ?_⟩
  obtain ⟨C, hC⟩ := hb n
  refine ⟨max C 0, le_max_right _ _, fun w hw g hg => ?_⟩
  obtain ⟨u, v, hu, hv, hl, rfl⟩ := hw
  have := hC u v hu hv hl g hg
  simp only [List.map_const', List.sum_replicate, smul_zero, Nat.cast_zero, add_zero, Real.rpow_natCast] at this
  rw [← dLR_eq]
  exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by have := gN_pos hg; positivity))

theorem fibre_unit_normalization : C6.FibUnit := by
  intro k r m om Gp T hom hGp hT _ ε hε i
  set ψ : Mat k r → ℂ := fun g => ((Gp g : ℝ) : ℂ) with hψdef
  obtain ⟨hψc, CG, hCG0, hCG⟩ := poly_adm (n := i) hGp
  have hGpc : Continuous Gp := by
    have : Gp = fun g => (ψ g).re := by funext g; simp [hψdef]
    rw [this]; exact Complex.continuous_re.comp hψc.continuous

  obtain ⟨C₁, hC₁0, hC₁⟩ := fdb ψ hψc {g | g ∈ GV k r ∧ ε ≤ Gp g} {z : ℂ | ε ≤ z.re}
    (fun g hg => by simpa [hψdef] using hg.2) gN (fun g hg => gN_ge_one hg.1) (2 * r + 2) 0 CG i
    (by
      intro w hw hne g hg
      have h1 := hCG w hw g hg.1
      have hl : 1 ≤ w.length := List.length_pos_iff.mpr hne
      refine h1.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (gN_ge_one hg.1) ?_) hCG0)
      nlinarith)
    i ℂ (Phh ε) (Phh_cd hε) (Phh_bound hε)

  have hoa : ∀ a, ContDiff ℝ ∞ (fun g => om g a) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ w, admitted i w → ∀ g ∈ GV k r,
      ‖Dw w (fun g => om g a) g‖ ≤ C * gN g ^ (r + 1) := fun a => poly_adm (hom a)
  choose hoc Co hCo0 hCo using hoa
  set C₂ : ℝ := ∑ a, Co a with hC₂
  have hC₂0 : 0 ≤ C₂ := Finset.sum_nonneg fun a _ => hCo0 a
  have hCoa : ∀ a, Co a ≤ C₂ := fun a => Finset.single_le_sum (fun b _ => hCo0 b) (Finset.mem_univ a)
  refine ⟨Real.sqrt T * (2 ^ i * (C₁ * C₂)), fun u v huv g hg hεg => ?_⟩
  set w := wL u ++ wR v with hw
  have hwA : admitted i w := admissible_of_unit_words huv
  have hwl : w.length = i := by rw [hw, len_LR]; exact huv.2.2
  have hlie : ∀ x ∈ w, inLie k r x.2 := lie_LR (unit_lie huv.1) (unit_lie huv.2.1)

  set Ut : Mat k r → (Fin m → ℂ) := fun g a => (Real.sqrt T : ℂ) * (Phh ε (ψ g) * om g a) with hUt
  have hUtc : ContDiff ℝ ∞ Ut :=
    contDiff_pi.2 fun a => contDiff_const.mul (((Phh_cd hε).comp hψc).mul (hoc a))
  have hO : IsOpen {g : Mat k r | ε / 2 < Gp g} := isOpen_lt continuous_const hGpc
  have heq : ∀ g' ∈ GV k r, g' ∈ {g : Mat k r | ε / 2 < Gp g} →
      (fun g' => C6.unitOf T (Gp g') (om g')) g' = Ut g' := by
    intro g' _ hg'
    have hp : 0 < Gp g' := by simp only [Set.mem_setOf_eq] at hg'; linarith
    funext a
    simp only [C6.unitOf, hUt, Phh, hψdef, Complex.ofReal_re, Pi.smul_apply, smul_eq_mul]
    rw [AdmissibleLieWords.hh, sc_one hε (le_of_lt hg'), one_mul, sqrt_div_eq hT hp]
    push_cast; ring
  rw [dLR_eq, Dw_congr_loc hlie hO heq g hg (by show ε / 2 < Gp g; linarith)]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by positivity) (mul_nonneg hC₁0 hC₂0))) (pow_nonneg (gN_pos hg).le _))).2
  intro a
  have e1 : Dw w Ut g a = Dw w (fun g => Ut g a) g := by
    have := dw_clm (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℂ) a) w hUtc
    exact (congrFun this g).symm
  rw [e1]
  have e2 : (fun g => Ut g a) = fun g => (Real.sqrt T : ℂ) • (Phh ε (ψ g) * om g a) := by
    funext g; simp [hUt, smul_eq_mul]
  rw [e2, Dw_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have hL := leibB g (C₁ * C₂ * gN g ^ ((r + 1) * (2 * i + 1))) w (fun g => Phh ε (ψ g)) (fun g => om g a)
    ((Phh_cd hε).comp hψc) (hoc a) (by
      intro w₁ w₂ hs
      have hlen := spl_len hs
      obtain ⟨h₁, h₂, _⟩ := hs
      have b1 := hC₁ w₁ (Adm_sub h₁ hwA) (by have := h₁.length_le; omega) g ⟨hg, hεg⟩
      have b2 := (hCo a w₂ (Adm_sub h₂ hwA) g hg).trans
        (mul_le_mul_of_nonneg_right (hCoa a) (pow_nonneg (gN_pos hg).le _))
      have hexp : (2 * r + 2 + 0) * w₁.length + (r + 1) ≤ (r + 1) * (2 * i + 1) := by
        have := h₁.length_le; rw [hwl] at this; nlinarith
      calc ‖Dw w₁ (fun g => Phh ε (ψ g)) g‖ * ‖Dw w₂ (fun g => om g a) g‖
          ≤ (C₁ * gN g ^ ((2 * r + 2 + 0) * w₁.length)) * (C₂ * gN g ^ (r + 1)) :=
            mul_le_mul b1 b2 (norm_nonneg _) (mul_nonneg hC₁0 (pow_nonneg (gN_pos hg).le _))
        _ = C₁ * C₂ * gN g ^ ((2 * r + 2 + 0) * w₁.length + (r + 1)) := by rw [pow_add]; ring
        _ ≤ C₁ * C₂ * gN g ^ ((r + 1) * (2 * i + 1)) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (gN_ge_one hg) hexp) (mul_nonneg hC₁0 hC₂0))
  rw [hwl] at hL
  calc ‖Dw w (fun g => Phh ε (ψ g) * om g a) g‖ ≤ 2 ^ i * (C₁ * C₂ * gN g ^ ((r + 1) * (2 * i + 1))) := hL
    _ = 2 ^ i * (C₁ * C₂) * gN g ^ ((r + 1) * (2 * i + 1)) := by ring

end Formalism.FourierDecayAlt.P
