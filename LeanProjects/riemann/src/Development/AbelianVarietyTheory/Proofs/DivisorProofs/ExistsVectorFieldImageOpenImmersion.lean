import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameBaseHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LogKS.FieldImage

variable {Z Z' : Scheme.{0}} (φ : Z' ⟶ Z) [IsOpenImmersion φ]

def appEquiv (O : Z.Opens) (h : O ≤ φ.opensRange) : Γ(Z, O) ≃+* Γ(Z', φ ⁻¹ᵁ O) :=
  haveI := Scheme.Hom.isIso_app φ O h
  (asIso (φ.app O)).commRingCatIsoToRingEquiv

theorem appEquiv_apply (O : Z.Opens) (h : O ≤ φ.opensRange) (f : Γ(Z, O)) :
    appEquiv φ O h f = (φ.app O).hom f := rfl

theorem app_res {W W' : Z.Opens} (h : W' ≤ W) (f : Γ(Z, W)) :
    (φ.app W').hom (resG Z h f) = resG Z' (Scheme.Hom.preimage_mono φ h) ((φ.app W).hom f) := by
  have := congrArg (fun g => g.hom f) (Scheme.Hom.naturality φ (homOfLE h).op)
  simpa [resG] using this

open Classical in

def push (d : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O)) (O : Z.Opens) (f : Γ(Z, O)) : Γ(Z, O) :=
  if h : O ≤ φ.opensRange then (appEquiv φ O h).symm (d (φ ⁻¹ᵁ O) ((φ.app O).hom f)) else 0

theorem app_push (d : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O)) (O : Z.Opens) (h : O ≤ φ.opensRange)
    (f : Γ(Z, O)) : (φ.app O).hom (push φ d O f) = d (φ ⁻¹ᵁ O) ((φ.app O).hom f) := by
  rw [push, dif_pos h, ← appEquiv_apply φ O h, RingEquiv.apply_symm_apply]

theorem le_range {W₀ : Z'.Opens} {O : Z.Opens} (hO : O ≤ φ ''ᵁ W₀) : O ≤ φ.opensRange :=
  hO.trans (Scheme.Hom.image_le_opensRange φ W₀)

theorem preimage_le {W₀ : Z'.Opens} {O : Z.Opens} (hO : O ≤ φ ''ᵁ W₀) : φ ⁻¹ᵁ O ≤ W₀ := by
  have := Scheme.Hom.preimage_mono φ hO
  rwa [Scheme.Hom.preimage_image_eq] at this

theorem inj_app {O : Z.Opens} (h : O ≤ φ.opensRange) : Function.Injective (φ.app O).hom :=
  (appEquiv φ O h).injective

theorem isField_push (W₀ : Z'.Opens) (d : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O)) (hd : IsField W₀ d) :
    IsField (φ ''ᵁ W₀) (push φ d) := by
  obtain ⟨hadd, hmul, hres⟩ := hd
  refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW f => ?_⟩
  · apply inj_app φ (le_range φ hW)
    rw [map_add, app_push φ d W (le_range φ hW), app_push φ d W (le_range φ hW),
      app_push φ d W (le_range φ hW), map_add, hadd _ (preimage_le φ hW)]
  · apply inj_app φ (le_range φ hW)
    rw [map_add, map_mul, map_mul, app_push φ d W (le_range φ hW), app_push φ d W (le_range φ hW),
      app_push φ d W (le_range φ hW), map_mul, hmul _ (preimage_le φ hW)]
  · have hW' : W' ≤ φ ''ᵁ W₀ := h.trans hW
    apply inj_app φ (le_range φ hW')
    rw [app_push φ d W' (le_range φ hW'), app_res, app_res, app_push φ d W (le_range φ hW),
      hres _ _ _ (preimage_le φ hW)]

end GlobalTheory.LogKS.FieldImage

theorem GlobalTheory.LogKS.isField_image : ∀ (Z Z' : Scheme.{0}) (φ : Z' ⟶ Z) [IsOpenImmersion φ] (W₀ : Z'.Opens) (d : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O)), IsField W₀ d → ∃ d₂ : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField (φ ''ᵁ W₀) d₂ ∧ ∀ (O : Z.Opens), O ≤ φ ''ᵁ W₀ → ∀ f : Γ(Z, O), (φ.app O).hom (d₂ O f) = d (φ ⁻¹ᵁ O) ((φ.app O).hom f) := by
  intro Z Z' φ _ W₀ d hd
  exact ⟨FieldImage.push φ d, FieldImage.isField_push φ W₀ d hd,
    fun O hO f => FieldImage.app_push φ d O (FieldImage.le_range φ hO) f⟩
