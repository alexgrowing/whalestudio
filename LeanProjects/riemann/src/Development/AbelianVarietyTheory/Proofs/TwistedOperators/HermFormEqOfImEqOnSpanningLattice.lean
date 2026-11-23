import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable def hermFormImPullback {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y w => (hermForm Hm (h y) (h w)).im)
    (fun a b w => by simp [hermForm, add_dotProduct])
    (fun c a w => by
      rw [show h (c • a) = (c : ℂ) • h a by rw [← map_smul]; rfl]
      simp [hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      rw [show h (c • a) = (c : ℂ) • h a by rw [← map_smul]; rfl]
      simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul])

theorem hermForm_eq_of_im_eq_on_spanning_lattice :
    ∀ {g : ℕ} {L : Type} [AddCommGroup L] (P : L →+ (Fin g → ℂ)), Submodule.span ℝ (Set.range P) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (h h' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ a b, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h (P a)) (h (P b))).im = (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' (P a)) (h' (P b))).im) → ∀ x y, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h x) (h y) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' x) (h' y) := by
  intro g L _ P hsp Hm h h' hab
  have hB : hermFormImPullback Hm h = hermFormImPullback Hm h' := by
    refine LinearMap.ext_on hsp ?_
    rintro _ ⟨a, rfl⟩
    refine LinearMap.ext_on hsp ?_
    rintro _ ⟨b, rfl⟩
    exact hab a b
  have him : ∀ x y, (hermForm Hm (h x) (h y)).im = (hermForm Hm (h' x) (h' y)).im := by
    intro x y
    exact LinearMap.congr_fun₂ hB x y
  intro x y
  have hI : ∀ (k : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (hermForm Hm (k (Complex.I • x)) (k y)).im = (hermForm Hm (k x) (k y)).re := by
    intro k
    simp [hermForm, map_smul, smul_dotProduct]
  apply Complex.ext
  · rw [← hI h, ← hI h']
    exact him _ _
  · exact him x y

end GlobalTheory
