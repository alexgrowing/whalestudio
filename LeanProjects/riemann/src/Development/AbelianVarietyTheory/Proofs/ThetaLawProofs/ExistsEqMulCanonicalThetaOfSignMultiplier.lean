import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier

noncomputable section

namespace GlobalTheory

section SlopeTestRemainingChoices

open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CanTh
open scoped Real

variable {g : ℕ}

theorem eC_half_char_emod_two (p q n n' : Fin g → ℤ) :
    eC (ofRealVec (fun i => (p i : ℝ) / 2) ⬝ᵥ ofIntVec n' -
      ofRealVec (fun i => (q i : ℝ) / 2) ⬝ᵥ ofIntVec n) =
    eC (ofRealVec (fun i => ((p i % 2 : ℤ) : ℝ) / 2) ⬝ᵥ ofIntVec n' -
      ofRealVec (fun i => ((q i % 2 : ℤ) : ℝ) / 2) ⬝ᵥ ofIntVec n) := by
  have split : ∀ r : Fin g → ℤ, ofRealVec (fun i => (r i : ℝ) / 2) =
      ofIntVec (fun i => r i / 2) + ofRealVec (fun i => ((r i % 2 : ℤ) : ℝ) / 2) := by
    intro r
    funext i
    simp only [ofRealVec, ofIntVec, Pi.add_apply]
    have hr : r i = 2 * (r i / 2) + r i % 2 := by omega
    conv_lhs => rw [hr]
    push_cast
    ring
  have intdot : ∀ r s : Fin g → ℤ, ofIntVec r ⬝ᵥ ofIntVec s = ((r ⬝ᵥ s : ℤ) : ℂ) := by
    intro r s
    simp [ofIntVec, dotProduct]
  have shift : ∀ (k : ℤ) (y : ℂ), eC (k + y) = eC y := by
    intro k y
    unfold eC
    rw [mul_add, Complex.exp_add]
    have hk : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * k) = 1 := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * k = k * (2 * Real.pi * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [hk, one_mul]
  have hsub : ∀ (u v : ℤ) (A B : ℂ), eC ((u : ℂ) + A - ((v : ℂ) + B)) = eC (A - B) := by
    intro u v A B
    rw [show (u : ℂ) + A - ((v : ℂ) + B) = ((u - v : ℤ) : ℂ) + (A - B) by push_cast; ring]
    exact shift _ _
  rw [split p, split q, add_dotProduct, add_dotProduct, intdot, intdot]
  exact hsub _ _ _ _

theorem classical_law_of_canonical {τ : Matrix (Fin g) (Fin g) ℂ} (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) {c : ℂ} {f : (Fin g → ℂ) → ℂ} (m n : Fin g → ℤ)
    (z : Fin g → ℂ) {l : Fin g → ℂ} (hl : l = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)))
    (h : f (z + l) = c * cexp (π * hermForm (imInv τ) z l + π / 2 * hermForm (imInv τ) l l) * f z) :
    cexp (-(π / 2 * ((z + l) ⬝ᵥ imInv τ *ᵥ (z + l)))) * f (z + l) =
      c * cexp (-(π * I * ((m ⬝ᵥ n : ℤ) : ℂ))) *
        eC (-((1 : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) *
        (cexp (-(π / 2 * (z ⬝ᵥ imInv τ *ᵥ z))) * f z) := by
  set M := imInv τ with hMdef
  set nC : Fin g → ℂ := fun i => (n i : ℂ) with hnC
  set mC : Fin g → ℂ := fun i => (m i : ℂ) with hmC
  have hMsymm : Mᵀ = M := isSymm_imInv hs
  have hswap : ∀ u v : Fin g → ℂ, u ⬝ᵥ M *ᵥ v = v ⬝ᵥ M *ᵥ u := by
    intro u v
    rw [dotProduct_mulVec, ← mulVec_transpose, hMsymm, dotProduct_comm]
  have hY : M *ᵥ (((τ.map Complex.im).map fun x : ℝ => (x : ℂ)) *ᵥ nC) = nC := by
    rw [mulVec_mulVec, imInv_mul hp, one_mulVec]
  have hstar : star l = l - (2 * I) • (((τ.map Complex.im).map fun x : ℝ => (x : ℂ)) *ᵥ nC) := by
    subst hl
    funext i
    simp only [Pi.star_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
      dotProduct, Matrix.map_apply, star_add, star_sum, Finset.mul_sum]
    rw [add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    · simp [hmC]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hnC]
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have hMstar : M *ᵥ star l = M *ᵥ l - (2 * I) • nC := by
    rw [hstar, mulVec_sub, mulVec_smul, hY]
  have hH1 : hermForm M z l = z ⬝ᵥ M *ᵥ l - 2 * I * (z ⬝ᵥ nC) := by
    unfold hermForm
    rw [hMstar, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have hH2 : hermForm M l l = l ⬝ᵥ M *ᵥ l - 2 * I * (l ⬝ᵥ nC) := by
    unfold hermForm
    rw [hMstar, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have hquad : (z + l) ⬝ᵥ M *ᵥ (z + l) = z ⬝ᵥ M *ᵥ z + 2 * (z ⬝ᵥ M *ᵥ l) + l ⬝ᵥ M *ᵥ l := by
    rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hswap l z]
    ring
  have hln : l ⬝ᵥ nC = ((m ⬝ᵥ n : ℤ) : ℂ) + ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) := by
    rw [hl, add_dotProduct]
    congr 1
    · simp [hmC, hnC, dotProduct]
    · rw [dotProduct_comm]
      rfl
  have hzn : z ⬝ᵥ nC = ofIntVec n ⬝ᵥ z := by
    rw [dotProduct_comm]
    rfl
  have E : -(π / 2 * ((z + l) ⬝ᵥ M *ᵥ (z + l))) +
      (π * hermForm M z l + π / 2 * hermForm M l l) =
      -(π * I * ((m ⬝ᵥ n : ℤ) : ℂ)) +
        2 * π * I * (-((1 : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) +
        -(π / 2 * (z ⬝ᵥ M *ᵥ z)) := by
    rw [hquad, hH1, hH2, hln, hzn]
    push_cast
    ring
  rw [h]
  calc cexp (-(π / 2 * ((z + l) ⬝ᵥ M *ᵥ (z + l)))) *
        (c * cexp (π * hermForm M z l + π / 2 * hermForm M l l) * f z)
      = c * f z * cexp (-(π / 2 * ((z + l) ⬝ᵥ M *ᵥ (z + l))) +
          (π * hermForm M z l + π / 2 * hermForm M l l)) := by
        simp only [Complex.exp_add]
        ring
    _ = c * f z * cexp (-(π * I * ((m ⬝ᵥ n : ℤ) : ℂ)) +
        2 * π * I * (-((1 : ℕ) : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) +
        -(π / 2 * (z ⬝ᵥ M *ᵥ z))) := by rw [E]
    _ = _ := by
        unfold eC
        rw [Complex.exp_add, Complex.exp_add]
        ring

end SlopeTestRemainingChoices

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_eq_mul_canonical_theta_of_sign_multiplier :
    ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (α : (Fin g → ℤ) → (Fin g → ℤ) → ℂ) (f : (Fin g → ℂ) → ℂ),
    τ.IsSymm → (τ.map Complex.im).PosDef → (∀ m n, α m n ^ 2 = 1) → Differentiable ℂ f → f ≠ 0 →
    (∀ (m n : Fin g → ℤ) (l z : Fin g → ℂ), l = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)) →
      f (z + l) = α m n * Complex.exp (Real.pi * hermForm ((τ.map Complex.im)⁻¹.map fun x : ℝ => (x : ℂ)) z l +
        Real.pi / 2 * hermForm ((τ.map Complex.im)⁻¹.map fun x : ℝ => (x : ℂ)) l l) * f z) →
    ∃ (a b : Fin g → ℝ) (c : ℂ), (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, b i = 0 ∨ b i = 1 / 2) ∧ c ≠ 0 ∧
      ∀ z, f z = c * (Complex.exp (Real.pi / 2 * (z ⬝ᵥ ((τ.map Complex.im)⁻¹.map fun x : ℝ => (x : ℂ)).mulVec z)) *
        thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) z) := by
  intro g τ α f hs hp hα2 hf hf0 hlaw
  classical
  let M : Matrix (Fin g) (Fin g) ℂ := CanTh.imInv τ
  let F : (Fin g → ℂ) → ℂ := fun z => Complex.exp (-(Real.pi / 2 * (z ⬝ᵥ M.mulVec z))) * f z
  let χ : (Fin g → ℤ) → (Fin g → ℤ) → ℂ := fun n n' =>
    α n' n * Complex.exp (-(Real.pi * Complex.I * ((n' ⬝ᵥ n : ℤ) : ℂ)))
  have hlawF : ∀ (n n' : Fin g → ℤ) (z : Fin g → ℂ),
      F (z + τ.mulVec (ReciprocityTheory.PTheta.ofIntVec n) + ReciprocityTheory.PTheta.ofIntVec n') = χ n n' *
        ReciprocityTheory.PTheta.eC (-((1 : ℕ) : ℂ) * (ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ
          (τ.mulVec (ReciprocityTheory.PTheta.ofIntVec n)) / 2 + ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ z)) * F z := by
    intro n n' z
    have hw : z + τ.mulVec (ReciprocityTheory.PTheta.ofIntVec n) + ReciprocityTheory.PTheta.ofIntVec n' =
        z + ((fun i => (n' i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) := by
      rw [add_assoc, add_comm (τ.mulVec _)]
      rfl
    have key := classical_law_of_canonical hs hp n' n z rfl (hlaw n' n _ z rfl)
    simp only [F, χ]
    rw [hw, key]
  have hF0 : F ≠ 0 := by
    intro h0
    apply hf0
    funext z
    have hz := congrFun h0 z
    simp only [F, Pi.zero_apply] at hz
    exact (mul_eq_zero.mp hz).resolve_left (Complex.exp_ne_zero _)
  have hquad : Differentiable ℂ (fun z : Fin g → ℂ => z ⬝ᵥ M.mulVec z) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  have hFd : Differentiable ℂ F := ((hquad.const_mul _).neg.cexp).mul hf
  have hone : ∀ x : ℂ, x ^ 2 = 1 → x = 1 ∨ x = -1 := by
    intro x hx
    have h' : (x - 1) * (x + 1) = 0 := by linear_combination hx
    rcases mul_eq_zero.mp h' with h1 | h1
    · left; linear_combination h1
    · right; linear_combination h1
  have hsign : ∀ n n', χ n n' = 1 ∨ χ n n' = -1 := by
    intro n n'
    apply hone
    simp only [χ]
    rw [mul_pow, hα2, _root_.one_mul, sq, ← Complex.exp_add]
    rw [show -(Real.pi * Complex.I * ((n' ⬝ᵥ n : ℤ) : ℂ)) + -(Real.pi * Complex.I * ((n' ⬝ᵥ n : ℤ) : ℂ)) =
      ((-(n' ⬝ᵥ n) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  have hchar := multiplier_add_of_ne_zero (N := 1) hs hF0 hlawF
  obtain ⟨p, q, hpq⟩ := exists_half_char_of_sign hchar hsign
  have hmem : F ∈ thetaLevelChar (fun i => ((p i % 2 : ℤ) : ℝ) / 2)
      (fun i => ((q i % 2 : ℤ) : ℝ) / 2) 1 τ := by
    rw [mem_thetaLevelChar]
    refine ⟨hFd, fun n n' z => ?_⟩
    rw [hlawF, hpq, eC_half_char_emod_two p q n n', Nat.cast_one, _root_.one_mul]
  rw [thetaLevelChar_one ⟨hs, hp⟩, Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hF0
    rw [← hc, zero_smul]
  have hhalf : ∀ r : ℤ, ((r % 2 : ℤ) : ℝ) / 2 = 0 ∨ ((r % 2 : ℤ) : ℝ) / 2 = 1 / 2 := by
    intro r
    rcases Int.emod_two_eq_zero_or_one r with h | h <;> simp [h]
  refine ⟨fun i => ((p i % 2 : ℤ) : ℝ) / 2, fun i => ((q i % 2 : ℤ) : ℝ) / 2, c,
    fun i => hhalf (p i), fun i => hhalf (q i), hc0, fun z => ?_⟩
  show f z = c * (Complex.exp (Real.pi / 2 * (z ⬝ᵥ M.mulVec z)) * _)
  rw [CanTh.thetaChar_eq_theta]
  have hz := congrFun hc z
  simp only [Pi.smul_apply, smul_eq_mul, F] at hz
  rw [mul_left_comm, hz, ← _root_.mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero,
    _root_.one_mul]

end GlobalTheory
