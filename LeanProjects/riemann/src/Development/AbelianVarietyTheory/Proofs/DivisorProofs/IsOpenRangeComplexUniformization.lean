import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormSecOfNot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyConnectedComponentGenericFibre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentUniquePointEachFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagComponentPointOverGeometricBasePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalChartSectionBound
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfIsReducedOfRangeSubset
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompClopen

theorem isOpen_range_π {D : D7} (O : Setup D) (c : O.s.Comp) : IsOpen (Set.range (O.Φ.C c).π) := by
  have hsm := O.s.T.smooth
  obtain ⟨X, j, hoi, hj, hr⟩ := GlobalTheory.CompOfVar.exists_var_comp _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e hsm (O.Φ.C c).Y
    (O.Φ.C c).π (O.Φ.C c).π_str
  let f : (O.Φ.C c).Y.X ⟶ X.X := IsOpenImmersion.lift j (O.Φ.C c).π hr
  have hf : f ≫ j = (O.Φ.C c).π := IsOpenImmersion.lift_fac _ _ _
  have hrange : Set.range j = Set.range (O.Φ.C c).π := by
    refine Set.Subset.antisymm ?_ hr
    rintro _ ⟨z, rfl⟩
    obtain ⟨K, _, _, x, t, rfl⟩ := GlobalTheory.FlagCptBase.exists_geomPt _ z
    let χ : O.κ.c.F →+* K := (Spec.preimage (x ≫ j ≫ genStr O.s.T.Z)).hom
    have hχ : x ≫ j ≫ genStr O.s.T.Z = spMap χ := (Spec.map_preimage _).symm
    obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame _ _ _ _ _ _ _ _ O.s.T.Z K χ (x ≫ j) (by rw [Category.assoc, hχ])
    rw [Category.assoc] at g
    obtain ⟨p, ⟨hp, -⟩, -⟩ := GlobalTheory.CarryAll.carries_everywhere _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e _ _ _ O.Φ c X j hoi hj f hf
      K χ x hχ g
    refine ⟨p t, ?_⟩
    rw [← hf, ← hp]
    simp only [Scheme.Hom.comp_apply]
  rw [← hrange]
  exact j.isOpenEmbedding.isOpen_range

theorem isPreimmersion_gen {D : D7} (O : Setup D) : IsPreimmersion (genι O.s.T.Z) := by
  have : FiniteDimensional ℚ O.κ.c.F := O.κ.c.fin
  have : NumberField O.κ.c.F := {}
  have : IsPreimmersion (spMap (algebraMap (𝓞 O.κ.c.F) O.κ.c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 O.κ.c.F)) (S := O.κ.c.F)
  exact inferInstanceAs (IsPreimmersion (Limits.pullback.fst O.s.T.Z.s (spMap (algebraMap (𝓞 O.κ.c.F) O.κ.c.F))))

theorem preimage_range_eq {D : D7} {O : Setup D} {c : O.s.Comp} (M : DRBase O c) :
    genι O.s.T.Z ⁻¹' Set.range M.b = Set.range (O.Φ.C c).π := by
  have := isPreimmersion_gen O
  have hw : closure {(O.Φ.C c).π (genericPoint (O.Φ.C c).Y.X)} = Set.range (O.Φ.C c).π := by
    have h := (genericPoint_spec (O.Φ.C c).Y.X).image (O.Φ.C c).π.continuous
    rwa [Set.image_univ, (GlobalTheory.FlagCptBase.isClosed_range_π (O.Φ.C c)).closure_eq] at h
  have hb : closure {M.b (genericPoint M.B)} = Set.range M.b := by
    have h := (genericPoint_spec M.B).image M.b.continuous
    rwa [Set.image_univ, M.b.isClosedEmbedding.isClosed_range.closure_eq] at h
  rw [← hw, ← hb, (genι O.s.T.Z).isEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_singleton, M.gen]

theorem isOpen_range_up : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (M : DRBase O c) (σ : O.κ.c.F →+* ℂ), IsOpen (Set.range (up M.b rfl σ)) := by
  intro D O c M σ
  have := isPreimmersion_gen O
  have e : Set.range (up M.b rfl σ) = ptsIn (genStr O.s.T.Z) σ ⟨_, isOpen_range_π O c⟩ := by
    ext z
    rw [CxPts.mem_ptsIn]
    change _ ↔ z.1 (IsLocalRing.closedPoint ℂ) ∈ Set.range (O.Φ.C c).π
    rw [← preimage_range_eq M]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1 (IsLocalRing.closedPoint ℂ),
        (congrArg (fun g : Sp ℂ ⟶ O.s.T.Z.X => g (IsLocalRing.closedPoint ℂ)) (up_ι M.b rfl σ y)).symm⟩
    · intro hz
      have hr : Set.range (z.1 ≫ genι O.s.T.Z) ⊆ Set.range M.b := by
        rintro _ ⟨t, rfl⟩
        rw [Subsingleton.elim t (IsLocalRing.closedPoint ℂ)]
        exact hz
      obtain ⟨y, hy⟩ : ∃ y : Sp ℂ ⟶ M.B, y ≫ M.b = z.1 ≫ genι O.s.T.Z :=
        exists_lift_of_isReduced_of_range_subset M.b _ hr
      refine ⟨⟨y, ?_⟩, Subtype.ext ?_⟩
      · have h₁ : genι O.s.T.Z ≫ O.s.T.Z.s = genStr O.s.T.Z ≫ spMap _ := Limits.pullback.condition
        change y ≫ M.b ≫ O.s.T.Z.s = _
        rw [reassoc_of% hy, h₁, ← Category.assoc, z.2, ← Spec.map_comp]
        rfl
      · rw [← cancel_mono (genι O.s.T.Z), up_ι, hy]
  rw [e]
  exact CxPts.isOpen_ptsIn _

end GlobalTheory.CompClopen

end
