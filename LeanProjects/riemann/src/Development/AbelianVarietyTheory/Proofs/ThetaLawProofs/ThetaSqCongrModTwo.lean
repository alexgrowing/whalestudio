import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OfRealVecHalfVec

noncomputable section

open Complex Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.KeyPow

theorem theta_sq_congr_mod_two {g : ℕ} {k k' m m' : Fin g → ℤ} (h : ∀ i, k i % 2 = m i % 2)
    (h' : ∀ i, k' i % 2 = m' i % 2) (z : Fin g → ℂ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    theta (halfVec k) (halfVec k') z τ ^ 2 = theta (halfVec m) (halfVec m') z τ ^ 2 := by
  rw [theta_sq_red k k', theta_sq_red m m', funext h, funext h']

theorem ThetaLaw.congr_target {g : ℕ} {sp : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    {n n' k k' m m' : Fin g → ℤ} (hl : ThetaLaw g sp n n' k k') (h : ∀ i, m i % 2 = k i % 2)
    (h' : ∀ i, m' i % 2 = k' i % 2) : ThetaLaw g sp n n' m m' := by
  obtain ⟨c, hc, hlaw⟩ := hl
  exact ⟨c, hc, fun τ hτ z => by rw [theta_sq_congr_mod_two h h']; exact hlaw τ hτ z⟩

theorem thetaLaw_spTransl {g : ℕ} (S : Matrix (Fin g) (Fin g) ℤ) (hS : S.IsSymm) (n n' : Fin g → ℤ) :
    ThetaLaw g (spTransl S) n n' n (n' - S *ᵥ n - fun i => S i i) := by
  set X : ℂ := -(ofRealVec (halfVec n) ⬝ᵥ (S.map (fun x : ℤ => (x : ℂ)) *ᵥ ofRealVec (halfVec n))) / 2 -
      ofRealVec (halfVec n) ⬝ᵥ (fun i => ((S i i : ℤ) : ℂ) / 2) with hX
  refine ⟨eC X ^ 2, ?_, fun τ _ z => ?_⟩
  · rw [← pow_mul, eC_pow]
    have h8 : ((2 * 4 : ℕ) : ℂ) * X = ((-(n ⬝ᵥ (S *ᵥ n)) - 2 * (n ⬝ᵥ fun i => S i i) : ℤ) : ℂ) := by
      have hd : ofIntVec n ⬝ᵥ (fun i => ((S i i : ℤ) : ℂ)) = ((n ⬝ᵥ fun i => S i i : ℤ) : ℂ) := by
        simp [dotProduct, ofIntVec]
      have hd2 : (fun i => ((S i i : ℤ) : ℂ) / 2) = (1 / 2 : ℂ) • fun i => ((S i i : ℤ) : ℂ) := by
        ext i; simp; ring
      rw [hX, ofRealVec_halfVec, Matrix.mulVec_smul, ← ofIntVec_mulVec, smul_dotProduct,
        dotProduct_smul, ofIntVec_dot, hd2, smul_dotProduct, dotProduct_smul, hd]
      simp only [smul_eq_mul]
      push_cast; ring
    rw [h8, eC_int]
  · have hb : halfVec (n' - S *ᵥ n - fun i => S i i) + S.map (fun x : ℤ => (x : ℝ)) *ᵥ halfVec n +
        (fun i => ((S i i : ℤ) : ℝ) / 2) = halfVec n' := by
      rw [mulVec_halfVec]
      ext i; simp only [halfVec, Pi.add_apply, Pi.sub_apply]; push_cast; ring
    have hz : zAct (spTransl S) τ z = z := by simp [zAct, jAut_spTransl]
    have he : expArg (spTransl S) τ z = 0 := by simp [expArg, jAut_spTransl, cMat_spTransl]
    rw [hz, he, spAct_spTransl, jAut_spTransl, thetaTranslTau_holds (Fin g) _ _ _ _ S hS, hb,
      mul_pow, det_one, eC_zero]
    ring

theorem thetaLaw_J {g : ℕ} (hInv : InversionStatement) (n n' : Fin g → ℤ) :
    ThetaLaw g (Matrix.J (Fin g) ℤ) n n' (-n') n := by
  set F : ℂ := 2 * (ofRealVec (halfVec (-n')) ⬝ᵥ ofRealVec (halfVec n))
  refine ⟨(-I) ^ g * eC F, ?_, fun τ hτ z => ?_⟩
  · rw [mul_pow, ← pow_mul, mul_comm g 4, pow_mul, eC_pow]
    have hI : (-I : ℂ) ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]; simp
    have hF : ((4 : ℕ) : ℂ) * F = ((-(2 * (n' ⬝ᵥ n)) : ℤ) : ℂ) := by
      simp only [F, ofRealVec_halfVec, smul_dotProduct, dotProduct_smul, ofIntVec_dot, smul_eq_mul]
      simp [dotProduct]; ring
    rw [hI, one_pow, one_mul, hF, eC_int]
  · have hsym : τ.IsSymm := hτ.1
    have hs : spAct (Matrix.J (Fin g) ℤ) τ = -τ⁻¹ := by
      rw [spAct_eq, jAut_J, nAut_eq, cMat_J]; simp [Matrix.J]
    have htinv : (τ⁻¹)ᵀ = τ⁻¹ := by rw [Matrix.transpose_nonsing_inv, hsym.eq]
    have hz : zAct (Matrix.J (Fin g) ℤ) τ z = τ⁻¹ *ᵥ z := by rw [zAct, jAut_J, htinv]
    have he : expArg (Matrix.J (Fin g) ℤ) τ z = z ⬝ᵥ (τ⁻¹ *ᵥ z) := by
      rw [expArg, jAut_J, cMat_J]; simp [Matrix.J]
    have hneg : -halfVec (-n') = halfVec n' := by ext i; simp [halfVec]; ring
    rw [hs, hz, he, jAut_J, hInv g _ _ τ hτ z, hneg]
    ring

theorem thetaLaw_generators (hInv : InversionStatement) (g : ℕ) (k k' : Fin g → ℤ) :
    (∀ (S : Matrix (Fin g) (Fin g) ℤ) (n' : Fin g → ℤ), S.IsSymm →
      (∀ i, (2 : ℤ) ∣ (S.mulVec k) i + S i i + k' i - n' i) → ThetaLaw g (spTransl S) k n' k k') ∧
    ThetaLaw g (Matrix.J (Fin g) ℤ) k' k k k' := by
  refine ⟨fun S n' hS hd => (thetaLaw_spTransl S hS k n').congr_target (fun _ => rfl) fun i => ?_,
    (thetaLaw_J hInv k' k).congr_target (fun i => ?_) fun _ => rfl⟩
  · have := hd i
    simp only [Pi.sub_apply]
    omega
  · simp only [Pi.neg_apply]
    omega

end GlobalTheory.KeyPow
end
