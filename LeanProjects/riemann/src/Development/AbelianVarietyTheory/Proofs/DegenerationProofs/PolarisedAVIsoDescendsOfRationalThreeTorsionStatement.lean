import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedAVIsoDescendsOfRationalThreeTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedAVIso_descends_of_rational_threeTorsion : Laws → Laws2 → GlobalTheory.LN.HomExtSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (C : Type) [Field C] [IsAlgClosed C] [Algebra (FractionRing R) C] (B B' : PolAV (Sp R)), RatTors B C 3 → RatTors B' C 3 → ∀ (φ : TF (R := R) C ⊗ B.A ≅ TF (R := R) C ⊗ B'.A) (g : (TF (R := R) C ⟶ B.A) ≃* (TF (R := R) C ⟶ B'.A)), φ.hom ≫ fst _ _ = fst _ _ → (∀ x, lift (𝟙 _) x ≫ φ.hom = lift (𝟙 _) (g x)) → LBIso (B.L.pull (snd (TF (R := R) C) B.A).left) (B'.L.pull (φ.hom ≫ snd (TF (R := R) C) B'.A).left) → ∃ Ψ : B'.A ≅ B.A, IsMonHom Ψ.hom ∧ LBIso B'.L (B.L.pull Ψ.hom.left) ∧ ∀ x, g x ≫ Ψ.hom = x := by
  first | exact @GlobalTheory.polAV_iso_descends_of_ratTors | exact GlobalTheory.polAV_iso_descends_of_ratTors | (intros; apply GlobalTheory.polAV_iso_descends_of_ratTors <;> assumption)
