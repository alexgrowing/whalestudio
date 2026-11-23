import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.PerfVB

namespace GlobalTheory.CompanionTheory.PerfVB

theorem exists_bc_comp (R S S' C : Type) [CommRing R] [CommRing S] [CommRing S'] [Algebra R S]
    [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} S) (F'' : C ⥤ CommAlgCat.{0} S')
    (m : BC F F') (n : BC F' F'') :
    ∃ l : BC F F'', ∀ T b, l.α T b = n.α T (m.α T b) := by
  obtain ⟨α, hα₁, hα₂, hα₃⟩ := m
  obtain ⟨β, hβ₁, hβ₂, hβ₃⟩ := n
  refine ⟨⟨fun T => (β T).comp (α T), ?_, ?_, ?_⟩, fun T b => rfl⟩
  · intro T T' φ b
    simp only [RingHom.comp_apply, hα₁, hβ₁]
  · intro T r b
    simp only [RingHom.comp_apply, hα₂, hβ₂, ← IsScalarTower.algebraMap_apply]
  · intro T
    obtain ⟨e₁, he₁⟩ := hα₃ T
    obtain ⟨e₂, he₂⟩ := hβ₃ T
    refine ⟨(TensorProduct.AlgebraTensorModule.cancelBaseChange R S S' S' (F.obj T)).symm.trans
      ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S' S') e₁).trans e₂), fun b => ?_⟩
    simp only [LinearEquiv.trans_apply, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, he₁, he₂,
      RingHom.comp_apply]

end GlobalTheory.CompanionTheory.PerfVB
