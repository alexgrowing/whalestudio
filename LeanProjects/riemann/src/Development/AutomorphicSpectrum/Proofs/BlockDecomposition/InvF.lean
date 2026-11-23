import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine

noncomputable section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD

namespace GlobalTheory.CompanionTheory.TrPassage

variable {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]

def invF (r : Matrix.unitaryGroup (Fin n) ℂ →* (F →L[ℂ] F)) (E : KMod n) :
    Submodule ℂ ((E.V →L[ℂ] ℂ) →L[ℂ] F) where
  carrier := {t | ∀ k ξ, t (ξ ∘L E.ρ k⁻¹) = r k (t ξ)}
  add_mem' {a b} ha hb k ξ := by
    simp only [ContinuousLinearMap.add_apply, map_add]
    rw [ha k ξ, hb k ξ]
  zero_mem' k ξ := by simp
  smul_mem' c a ha k ξ := by
    simp only [ContinuousLinearMap.smul_apply, map_smul]
    rw [ha k ξ]

def chiT (E : KMod n) (T : E.V →L[ℂ] E.V) (k : Matrix.unitaryGroup (Fin n) ℂ) : ℂ :=
  LinearMap.trace ℂ E.V ((E.ρ k * T : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V)

end GlobalTheory.CompanionTheory.TrPassage
