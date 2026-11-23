import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafGlueOfOpenImmersions
import Mathlib
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idealSheafData_glue_of_openImmersions : (∀ {X : Scheme.{0}} (𝒜 : Set X.affineOpens), (∀ W ∈ 𝒜, ∀ W' : X.affineOpens, W' ≤ W → W' ∈ 𝒜) → (∀ x : X, ∃ W ∈ 𝒜, x ∈ W.1) → ∀ (k : ∀ W : X.affineOpens, Ideal Γ(X, W)), (∀ W ∈ 𝒜, ∀ (W' : X.affineOpens) (h : W' ≤ W), (k W).map (X.presheaf.map (homOfLE h).op).hom = k W') → ∃ I : X.IdealSheafData, ∀ W ∈ 𝒜, I.ideal W = k W) → ∀ {X : Scheme.{0}} {ι : Type*} (P : ι → Scheme.{0}) (e : ∀ i, P i ⟶ X), (∀ i, IsOpenImmersion (e i)) → (∀ x : X, ∃ i, x ∈ Set.range (e i)) → ∀ (K : ∀ i, (P i).IdealSheafData), (∀ i j (Q : Scheme.{0}) (a : Q ⟶ P i) (b : Q ⟶ P j), a ≫ e i = b ≫ e j → (K i).comap a = (K j).comap b) → ∃ I : X.IdealSheafData, ∀ i, I.comap (e i) = K i := by
  first | (exact @GlobalTheory.IdealGlue.idealSheaf_glue_of_openImmersions) | (exact GlobalTheory.IdealGlue.idealSheaf_glue_of_openImmersions) | (intros; apply GlobalTheory.IdealGlue.idealSheaf_glue_of_openImmersions  <;> assumption)
