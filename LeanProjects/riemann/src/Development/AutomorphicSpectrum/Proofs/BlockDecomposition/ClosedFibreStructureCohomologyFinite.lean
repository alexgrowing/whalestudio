import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.FlatFibre

theorem closed_fibre_first_cohomology_finite : FlatBCSt → ∀ (k : Type) [Field k] (A : Over (Sp k)) [IsSeparated A.hom] [QuasiCompact A.hom],
    Module.Finite k (HO1 A.hom) → ∀ (R : Type) [CommRing R] [IsLocalRing R] (t : Sp R ⟶ Sp k)
    (X' : Scheme.{0}) (s' : X' ⟶ Sp (IsLocalRing.ResidueField R)) (φ : X' ⟶ (A ⊗ Over.mk t).left),
    IsPullback φ s' (snd A (Over.mk t)).left (spMap (algebraMap R (IsLocalRing.ResidueField R))) →
    Module.Finite (IsLocalRing.ResidueField R) (HO1 s') ∧
      Module.finrank (IsLocalRing.ResidueField R) (HO1 s') ≤ Module.finrank k (HO1 A.hom) := by
  intro hBC k _ A _ _ hfin R _ _ t X' s' φ h
  let u : Sp (IsLocalRing.ResidueField R) ⟶ Sp k :=
    spMap (algebraMap R (IsLocalRing.ResidueField R)) ≫ t
  let σ : k →+* IsLocalRing.ResidueField R := (Spec.preimage u).hom
  have hσ : spMap σ = u := Spec.map_preimage u
  let _ : Algebra k (IsLocalRing.ResidueField R) := σ.toAlgebra
  have hsq : IsPullback (fst A (Over.mk t)).left (snd A (Over.mk t)).left A.hom t := by
    simpa using IsPullback.of_hasPullback A.hom t
  have hp : IsPullback (φ ≫ (fst A (Over.mk t)).left) s' A.hom
      (spMap (algebraMap k (IsLocalRing.ResidueField R))) := by
    have h2 := IsPullback.paste_horiz h hsq
    have h3 : spMap (algebraMap k (IsLocalRing.ResidueField R)) = u := hσ
    rw [h3]
    exact h2
  obtain ⟨e, -⟩ := hBC k (IsLocalRing.ResidueField R) A.left X' A.hom s' _ hp inferInstance inferInstance
  refine ⟨Module.Finite.equiv e, ?_⟩
  rw [← e.finrank_eq, Module.finrank_baseChange]

end GlobalTheory.CompanionTheory.FlatFibre
