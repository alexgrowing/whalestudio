import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormExistsForCmObject
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbDual

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMultAdjoint

theorem polForm_adjoint_rm : GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R)) (c : 𝔠.elt) (ψ : LinearMap.BilinForm R (HdR X.A)),
    IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ → ∀ (b : 𝓞 F) (x y : HdR X.A),
      ψ (act (dp0 R) (𝟙 _) X.rm b x) y = ψ x (act (dp0 R) (𝟙 _) X.rm b y) := by
  intro HR HD F _ _ 𝔠 R _ X c ψ hψ b x y
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor X.A X.A X.ab X.ab
  have gAB := smooth_prod X.dim X.dim
  have C := cupSquare_of_free HR.1 hAB gAB
  have := X.rm.hom
  obtain ⟨φ, hφ, h2φ⟩ := GlobalTheory.PolPairing.exists_isCorrForm_diag HR F 𝔠 R X c
  obtain ⟨φ', hφ', h2φ'⟩ := GlobalTheory.PolPairing.exists_isCorrForm_diag HR F 𝔠 R X (b • c)
  have eψ : ψ = (2 : R) • φ := IsPolForm.unique HR.1 X.ab X.dim (pull_isLB (X.isLB c) _) hψ h2φ
  obtain ⟨χ, hχ, k⟩ := hφ.pull (X.isLB c) (homMor (dp0 R) (𝟙 _) (𝟙 X.A))
    (homMor (dp0 R) (𝟙 _) (X.rm.act b)) (h := (lift (fst X.A X.A) (snd X.A X.A ≫ X.rm.act b)).left)
    (by simp only [← Over.comp_left, lift_fst, lift_snd, Category.comp_id])
    (by simp only [← Over.comp_left, lift_fst, lift_snd, Category.comp_id])
    (X.isLB (b • c)) (LBIso.symm (X.smul b c))
  obtain rfl := hχ.unique C (X.isLB (b • c)) hφ'
  have key : ∀ u v, χ u v = φ u (push (dp0 R) (𝟙 _) (X.rm.act b) v) := fun u v ↦ by
    have e := k (push (dp0 R) (𝟙 _) (𝟙 X.A) u) u (push (dp0 R) (𝟙 _) (X.rm.act b) v) v (fun _ ↦ rfl) fun _ ↦ rfl
    rwa [push_id, LinearMap.id_apply, RingHom.id_apply] at e
  change ψ (push (dp0 R) (𝟙 _) (X.rm.act b) x) y = ψ x (push (dp0 R) (𝟙 _) (X.rm.act b) y)
  have e₁ := (LinearMap.IsAlt.neg hψ.isAlt y (push (dp0 R) (𝟙 _) (X.rm.act b) x)).symm
  have e₂ := LinearMap.IsAlt.neg h2φ'.isAlt y x
  rw [e₁, eψ]
  simp only [LinearMap.smul_apply, ← key] at e₂ ⊢
  exact e₂

end GlobalTheory.RealMultAdjoint
