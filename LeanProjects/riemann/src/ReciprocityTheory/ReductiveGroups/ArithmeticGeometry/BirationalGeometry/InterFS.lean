import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem maDensity_congr_of_eventuallyEq {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : ∀ j, φ j =ᶠ[𝓝 y] ψ j) : maDensity φ y = maDensity ψ y := by
  have h2 : ∀ j, fderiv ℝ (fderiv ℝ (φ j)) y = fderiv ℝ (fderiv ℝ (ψ j)) y := fun j =>
    Filter.EventuallyEq.fderiv_eq (show fderiv ℝ (φ j) =ᶠ[𝓝 y] fderiv ℝ (ψ j) from
      (h j).eventuallyEq_nhds.mono fun _ h' => h'.fderiv_eq)
  have hH : ∀ k, cxHessian (φ k) y = cxHessian (ψ k) y := by
    intro k
    unfold cxHessian
    rw [h2 k]
  simp only [maDensity, hH]

local instance instRealIPS : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E

def affL (b : E) : (Fin 1 → ℂ) →L[ℝ] E :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0).smulRight b

theorem mixedDisc_one (A : Fin 1 → Matrix (Fin 1) (Fin 1) ℂ) : mixedDisc A = A 0 0 0 := by
  unfold mixedDisc
  rw [← Finset.powerset_univ, Finset.univ_unique, ← Finset.insert_empty,
    Finset.sum_powerset_insert (by simp)]
  simp [Matrix.det_unique]

theorem maDensity_one (f : (Fin 1 → ℂ) → ℝ) (y : Fin 1 → ℂ) :
    maDensity (fun _ => f) y = (fderiv ℝ (fderiv ℝ f) y (Pi.single 0 1) (Pi.single 0 1) +
      fderiv ℝ (fderiv ℝ f) y (Complex.I • Pi.single 0 1) (Complex.I • Pi.single 0 1)) /
        (2 * Real.pi) := by
  have hre : ∀ u v : ℝ, ((((u : ℂ) + Complex.I * (v : ℂ)) / 4).re) = u / 4 := by
    intro u v
    simp [Complex.div_ofNat_re]
  rw [maDensity, mixedDisc_one]
  simp only [cxHessian, hre]
  have := Real.pi_pos
  simp
  field_simp
  ring

end ReciprocityTheory.ChartRestriction.G.Geo
