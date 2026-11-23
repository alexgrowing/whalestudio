import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDataOfCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafGlueOfOpenImmersions

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace GlobalTheory.IdealGlue

theorem exists_comap_eq : ∀ {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0}) (f : ∀ i, V i ⟶ X),
    (∀ i, IsOpenImmersion (f i)) → (∀ x : X, ∃ i y, f i y = x) →
    ∀ (J : ∀ i, (V i).IdealSheafData),
    (∀ i j (Y : Scheme.{0}) (a : Y ⟶ V i) (a' : Y ⟶ V j), a ≫ f i = a' ≫ f j →
      (J i).comap a = (J j).comap a') →
    ∃ I : X.IdealSheafData, ∀ i, I.comap (f i) = J i := by
  intro X ι V f hf hcov J hJ
  exact idealSheaf_glue_of_openImmersions (fun 𝒜 h1 h2 k h3 => GlobalTheory.T.exists_idealSheafData_of_compatible_ideals 𝒜 h1 h2 k h3)
    V f hf (fun x => by obtain ⟨i, y, hy⟩ := hcov x; exact ⟨i, y, hy⟩) J hJ

end GlobalTheory.IdealGlue
