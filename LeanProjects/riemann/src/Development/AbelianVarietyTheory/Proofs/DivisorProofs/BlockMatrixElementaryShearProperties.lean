import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem shear_self {ι : Type} {m : ι → ℕ} (τ : ι) (a b : Fin (m τ)) {R : Type} [CommRing R] (t : R) :
    shear τ a b t τ = Matrix.transvection a b t := by
  ext i j
  simp only [shear, Matrix.transvection, Matrix.add_apply, Matrix.of_apply, Sigma.mk.inj_iff, heq_eq_eq, true_and]
  rw [Matrix.single_apply]
  simp only [@eq_comm _ a i, @eq_comm _ b j]

theorem shear_ne {ι : Type} {m : ι → ℕ} (τ : ι) (a b : Fin (m τ)) {R : Type} [CommRing R] (t : R) (σ : ι)
    (h : σ ≠ τ) : shear τ a b t σ = 1 := by
  ext i j
  simp [shear, Sigma.mk.inj_iff, h]

theorem shear_props : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), a < b → ∀ (R : Type) [CommRing R] (t : R), (∀ σ, (shear τ a b t σ).det = 1) ∧ shear τ a b t * shear τ a b (-t) = 1 ∧ shear τ a b (0 : R) = 1 ∧ ∀ (S : Type) [CommRing S] (g : R →+* S), (shear τ a b t).map g = shear τ a b (g t) := by
  intro ι m τ a b hab R _ t
  have hne : a ≠ b := hab.ne
  refine ⟨fun σ => ?_, ?_, ?_, fun S _ g => ?_⟩
  · by_cases h : σ = τ
    · subst h; rw [shear_self]; exact Matrix.det_transvection_of_ne a b hne t
    · rw [shear_ne τ a b t σ h, Matrix.det_one]
  · funext σ
    rw [Pi.mul_apply, Pi.one_apply]
    by_cases h : σ = τ
    · subst h; rw [shear_self, shear_self, Matrix.transvection_mul_transvection_same (h := hne), add_neg_cancel,
        Matrix.transvection_zero]
    · rw [shear_ne τ a b _ σ h, shear_ne τ a b _ σ h, mul_one]
  · funext σ
    rw [Pi.one_apply]
    by_cases h : σ = τ
    · subst h; rw [shear_self, Matrix.transvection_zero]
    · rw [shear_ne τ a b _ σ h]
  · funext σ i j
    simp only [Mat.map, shear, Matrix.map_apply, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply]
    split_ifs <;> simp

end GlobalTheory.FlagPush
