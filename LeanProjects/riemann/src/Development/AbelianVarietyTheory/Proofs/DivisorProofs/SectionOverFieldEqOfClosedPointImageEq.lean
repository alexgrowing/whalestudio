import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory

theorem section_eq_of_point_eq : ∀ (K : Type) [Field K] (X : Scheme.{0}) (q : X ⟶ Sp K) (z z' : Sp K ⟶ X), z ≫ q = 𝟙 _ → z' ≫ q = 𝟙 _ → z (IsLocalRing.closedPoint K) = z' (IsLocalRing.closedPoint K) → z = z' := by
  intro K _ X q z z' hz hz' hpt
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective z
  obtain ⟨⟨p', ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective z'
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hz hz' hpt ⊢
  have e : p = p' := by
    have h1 := (Scheme.Hom.comp_apply _ _ _).symm.trans (hpt.trans (Scheme.Hom.comp_apply _ _ _))
    rwa [Scheme.fromSpecResidueField_apply, Scheme.fromSpecResidueField_apply] at h1
  subst e
  obtain ⟨χ, hχ⟩ := Spec.map_surjective (X.fromSpecResidueField p ≫ q)
  rw [Category.assoc, ← hχ, ← Spec.map_comp, ← Spec.map_id, Spec.map_inj] at hz hz'
  have hφ : ∀ c, φ.hom (χ.hom c) = c := fun c => congrArg (fun g => g.hom c) hz
  have hψ : ∀ c, ψ.hom (χ.hom c) = c := fun c => congrArg (fun g => g.hom c) hz'
  have hsurj : Function.Surjective χ.hom := by
    intro y
    refine ⟨φ.hom y, φ.hom.injective ?_⟩
    rw [hφ]
  have : φ = ψ := by
    ext y
    obtain ⟨c, rfl⟩ := hsurj y
    rw [hφ, hψ]
  rw [this]

end GlobalTheory
