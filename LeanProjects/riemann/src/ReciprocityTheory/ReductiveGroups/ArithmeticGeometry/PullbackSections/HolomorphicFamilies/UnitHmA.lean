import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.UH

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {g : ℕ}

theorem hermForm_add_left (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp [hermForm, add_dotProduct]

theorem hermForm_smul_left (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (c • z) w = c * hermForm Hm z w := by
  simp [hermForm, smul_dotProduct]

theorem hermForm_add_right (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  simp [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_rsmul_right (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℝ) (z w : Fin g → ℂ) :
    hermForm Hm z (c • w) = c * hermForm Hm z w := by
  simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.real_smul]

theorem hermForm_sub_mat (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm (H₁ - H₂) z w = hermForm H₁ z w - hermForm H₂ z w := by
  simp [hermForm, Matrix.sub_mulVec, dotProduct_sub]

def imForm (Hm : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (hermForm Hm z w).im)
    (fun z z' w => by rw [hermForm_add_left, Complex.add_im])
    (fun c z w => by
      rw [show (c • z : Fin g → ℂ) = (c : ℂ) • z from by funext i; simp [Complex.real_smul],
        hermForm_smul_left, smul_eq_mul, Complex.im_ofReal_mul])
    (fun z w w' => by rw [hermForm_add_right, Complex.add_im])
    (fun c z w => by rw [hermForm_rsmul_right, smul_eq_mul]; simp)

theorem herm_eq_of_im {L : Type} [AddCommGroup L] (P : L →+ (Fin g → ℂ))
    (hP : Submodule.span ℝ (Set.range P) = ⊤) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ x y, (hermForm H₁ (P x) (P y)).im = (hermForm H₂ (P x) (P y)).im) : H₁ = H₂ := by
  have hD : ∀ x y, (hermForm (H₁ - H₂) (P x) (P y)).im = 0 := fun x y => by
    rw [hermForm_sub_mat, Complex.sub_im, h, sub_self]
  have h0 : imForm (H₁ - H₂) = 0 := by
    apply LinearMap.ext_on_range hP
    intro x
    apply LinearMap.ext_on_range hP
    intro y
    simpa [imForm] using hD x y
  have hall : ∀ z w, hermForm (H₁ - H₂) z w = 0 := by
    intro z w
    have him : ∀ z' : Fin g → ℂ, (hermForm (H₁ - H₂) z' w).im = 0 := fun z' => by
      simpa [imForm] using LinearMap.congr_fun₂ h0 z' w
    have hre := him (Complex.I • z)
    rw [hermForm_smul_left] at hre
    apply Complex.ext
    · simpa using hre
    · simpa using him z
  have hs : ∀ j : Fin g, star (Pi.single j 1 : Fin g → ℂ) = (Pi.single j 1 : Fin g → ℂ) := fun j => by
    ext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  refine sub_eq_zero.1 ?_
  ext i j
  have := hall (Pi.single i 1) (Pi.single j 1)
  simpa [hermForm, hs, Matrix.mulVec_single, single_dotProduct] using this

end ReciprocityTheory.ChartRestriction.G.PullbackSections.UH
