import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationOfData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitMpOmjExtIff

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis

def CovBy {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (Φ : C → Prop) (S : C) : Prop :=
  ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧
    ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → Φ S'

theorem CovBy.mono {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}
    {Φ Ψ : C → Prop} (h : ∀ S, Φ S → Ψ S) {S : C} (hS : CovBy F Φ S) : CovBy F Ψ S := by
  obtain ⟨n, b, hb, hc⟩ := hS
  exact ⟨n, b, hb, fun i S' u hu ↦ h _ (hc i S' u hu)⟩

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
