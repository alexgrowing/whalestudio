import Mathlib
import Formalism.HermitianLattices.StatementMass
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LandherrAndLandherrSt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCMFieldOfStar

noncomputable section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G

namespace GlobalTheory.BinaryRep

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem gram_diag_pos {r : ℕ} (τ : E →+* ℂ) (d : Fin r → E)
    (hd : ∀ i, (τ (d i)).im = 0 ∧ 0 < (τ (d i)).re) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      FD.gram τ (Matrix.diagonal d) Q = Matrix.diagonal fun a : Fin r => ((FD.sgn r (a : ℕ) : ℝ) : ℂ) := by
  classical
  set q : Fin r → ℝ := fun i => (Real.sqrt (τ (d i)).re)⁻¹ with hq
  have hq2 : ∀ i, (q i : ℂ) * τ (d i) * (q i : ℂ) = 1 := by
    intro i
    have h1 : τ (d i) = ((τ (d i)).re : ℂ) := Complex.ext rfl (by simp [(hd i).1])
    have h2 : q i * q i * (τ (d i)).re = 1 := by
      rw [hq]
      simp only
      rw [← mul_inv, Real.mul_self_sqrt (hd i).2.le, inv_mul_cancel₀ (hd i).2.ne']
    rw [h1]
    exact_mod_cast (by linarith [h2] : q i * (τ (d i)).re * q i = 1)
  refine ⟨Matrix.diagonal fun i => (q i : ℂ), ?_, ?_⟩
  · rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    have : (q i : ℂ) ≠ 0 := fun h => by simpa [h] using hq2 i
    exact this
  · ext a b
    simp only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      have hs : FD.sgn r (a : ℕ) = 1 := by simp [FD.sgn, a.isLt]
      simp [hs, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', Complex.conj_ofReal]
      rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp only [if_true, Complex.conj_ofReal]
      linear_combination hq2 a
    · simp [hab, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hx : a = x
      · subst hx
        simp [hab]
      · simp [hx]

end GlobalTheory.BinaryRep

namespace GlobalTheory.BinaryRep

theorem represents_totallyPositive : ∀ (K : Type) [Field K] [NumberField K] [StarRing K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ a b n : K, star a = a → star b = b → star n = n →
    (∀ φ : K →+* ℂ, 0 < (φ a).re) → (∀ φ : K →+* ℂ, 0 < (φ b).re) → (∀ φ : K →+* ℂ, 0 < (φ n).re) →
    ∃ s t : K, a * (s * star s) + b * (t * star t) = n := by
  intro K _ _ _ hc a b n ha hb hn hpa hpb hpn
  haveI : IsCMField K := GlobalTheory.OrthoLattice.isCMField_of_star K hc.1 hc.2.1
  let φ0 : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  have hst : ∀ x : K, star x = FD.cc x := fun x =>
    φ0.injective (by rw [FD.cc, IsCMField.complexEmbedding_complexConj]; exact hc.2.1 φ0 x)
  have hreal : ∀ x : K, star x = x → ∀ τ : K →+* ℂ, (τ x).im = 0 := by
    intro x hx τ
    have h := hc.2.1 τ x
    rw [hx] at h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hne : ∀ x : K, (∀ φ : K →+* ℂ, 0 < (φ x).re) → x ≠ 0 := by
    intro x hx h0
    have := hx φ0
    simp [h0] at this
  have ha0 := hne a hpa
  have hb0 := hne b hpb
  have hn0 := hne n hpn
  have hca : FD.cc a = a := by rw [← hst, ha]
  have hcb : FD.cc b = b := by rw [← hst, hb]
  have hcn : FD.cc n = n := by rw [← hst, hn]
  have hcab : FD.cc (a * b * n) = a * b * n := by
    rw [← hst, star_mul, star_mul, ha, hb, hn]; ring
  set G : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![a, b] with hG
  set G' : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![n, a * b * n] with hG'
  have herm_diag : ∀ d : Fin 2 → K, (∀ i, FD.cc (d i) = d i) →
      ∀ i j, FD.cc (Matrix.diagonal d i j) = Matrix.diagonal d j i := by
    intro d hd i j
    by_cases h : i = j
    · subst h; simp [hd]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h), FD.cc]
  have hGh : ∀ i j, FD.cc (G i j) = G j i :=
    herm_diag _ (fun i => by fin_cases i <;> simp [hca, hcb])
  have hG'h : ∀ i j, FD.cc (G' i j) = G' j i :=
    herm_diag _ (fun i => by fin_cases i <;> simp [hcn, hcab])
  have hdG : G.det = a * b := by simp [hG, Matrix.det_diagonal, Fin.prod_univ_two]
  have hdG' : G'.det = n * (a * b * n) := by simp [hG', Matrix.det_diagonal, Fin.prod_univ_two]
  have hpos : ∀ d : Fin 2 → K, (∀ i, star (d i) = d i ∧ ∀ φ : K →+* ℂ, 0 < (φ (d i)).re) →
      ∀ τ : K →+* ℂ, ∀ i, (τ (d i)).im = 0 ∧ 0 < (τ (d i)).re :=
    fun d hd τ i => ⟨hreal _ (hd i).1 τ, (hd i).2 τ⟩
  have habn : star (a * b * n) = a * b * n := by rw [star_mul, star_mul, ha, hb, hn]; ring
  have hpabn : ∀ φ : K →+* ℂ, 0 < (φ (a * b * n)).re := by
    intro φ
    have e : ∀ x : K, star x = x → (φ x : ℂ) = ((φ x).re : ℂ) := fun x hx =>
      Complex.ext rfl (by simp [hreal x hx φ])
    rw [map_mul, map_mul, e a ha, e b hb, e n hn]
    simp only [← Complex.ofReal_mul, Complex.ofReal_re]
    exact mul_pos (mul_pos (hpa φ) (hpb φ)) (hpn φ)
  obtain ⟨γ, hγ⟩ := (GlobalTheory.QNorm.landherr_and_landherrSt.2) K 2 G G' hGh hG'h
    (by rw [hdG]; exact mul_ne_zero ha0 hb0)
    (by rw [hdG']; exact mul_ne_zero hn0 (mul_ne_zero (mul_ne_zero ha0 hb0) hn0))
    (fun τ => ⟨2,
      gram_diag_pos τ ![a, b] (hpos _ (fun i => by fin_cases i <;> simp [ha, hb, hpa, hpb]) τ),
      gram_diag_pos τ ![n, a * b * n]
        (hpos _ (fun i => by fin_cases i; exacts [⟨hn, hpn⟩, ⟨habn, hpabn⟩]) τ)⟩)
    ⟨n, by rw [hdG', hdG, hcn]; ring⟩
  have h := hγ (Pi.single 0 1) (Pi.single 0 1)
  set v := (γ : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single 0 1 with hv
  refine ⟨v 0, v 1, ?_⟩
  simp only [FD.herm, Fin.sum_univ_two, hG, hG', Matrix.diagonal_apply_eq,
    Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
    Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0)] at h
  simp [FD.cc] at h
  rw [hst, hst]
  simp only [FD.cc]
  linear_combination h

end GlobalTheory.BinaryRep
