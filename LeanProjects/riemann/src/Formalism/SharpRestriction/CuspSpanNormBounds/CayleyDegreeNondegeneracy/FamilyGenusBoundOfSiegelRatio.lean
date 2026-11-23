import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.TraceInnerPosOfOrthonormalPair
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ExistsSmallMemFractionalIdeal
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ProdNormEmbeddingsEqAbsNorm
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.PlaneMassBoundOfFacts
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeIndexAndWeightTheory

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.HermitianLatticesTheory

theorem second_orthogonal_vector_holds (K : Type) [Field K] [NumberField K] [StarRing K] (hK : IsCMUnram K) : SecondOrthogonalVector K :=
  fun V _ _ _ _ h L _ hL M hlat hint huni x hx hx0 => exists_orthogonal_second_vector K hK V h L hL M hlat hint huni x hx hx0

theorem plane_class_count_holds (K : Type) [Field K] [NumberField K] [StarRing K] (hK : IsCMUnram K) : PlaneClassCount K :=
  fun V _ _ _ _ h L hs hL s hreps B₁ B₂ hint hshort => class_count_plane_bound K hK V h L hs hL s hreps B₁ B₂ hint hshort

end Formalism.MainNotions.BridgeLemma₂

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem plane_mass_le_height_pow (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C : ℝ)
    (hC : 55 * max 1 (1 / Cl) ≤ C ^ 2) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) : UnitaryVolumeMass.Mass2At D large₂ C := by
  have hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := D.sp.cm.cmUnram
  have hfin := Formalism.MainNotions.StandardLattice.finrank_host D
  have hrd : rootDiscriminant D.host.E = D.host.rdE := rfl
  have h19 : 1 ≤ D.host.v := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h19, -⟩ := hH
    exact h19
  have hrd0 : 0 ≤ D.host.rdE := by
    have e : 2 * D.host.v = D.host.rdE := by unfold Host.v; ring
    rw [← e]; linarith
  refine plane_mass_bound_of_facts D large₂ C' Cl Cg cb Cu cT CT C _ (short_vector_every_place D.host.E hK)
    (second_orthogonal_vector_holds D.host.E hK) (plane_class_count_holds D.host.E hK) ?_ ?_ hC hH
  · rw [hrd]; positivity
  · rw [hrd, hfin]; push_cast; apply le_of_eq; ring

theorem plane_mass_bound_parameters (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ)
    (hC : 55 * max 1 (1 / Cl) ≤ C ^ 2) : UnitaryVolumeMass.stMass2 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C :=
  fun hH => plane_mass_le_height_pow D large₂ C' Cl Cg cb Cu cT CT C hC hH.1.1

theorem plane_mass_bound_K2 (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 C : ℝ)
    (hC : 55 * max 1 (1 / Cl) ≤ C ^ 2) : UnitaryVolumeMass.stMass2K D large₂ C' Cl Cg cb Cu cT CT C0 C :=
  fun hH => plane_mass_le_height_pow D large₂ C' Cl Cg cb Cu cT CT C hC hH.1.1

theorem plane_mass_constant_le_sq (Cl : ℝ) : 55 * max 1 (1 / Cl) ≤ (55 * max 1 (1 / Cl)) ^ 2 := by
  have h : (1 : ℝ) ≤ max 1 (1 / Cl) := le_max_left _ _
  nlinarith

section Family

variable {eps : ℝ} (Fm : FamP eps)

theorem family_plane_mass_admissible (Cg cb Cu cT CT C0 A : ℝ) : AuxiliaryNormPrimes.FamilyRankTwoMassBound Fm Cg cb Cu cT CT C0 A :=
  ⟨55 * max 1 (1 / sCl Fm), 0, fun _ _ _ u u' => plane_mass_bound_parameters _ _ u u' _ _ _ _ _ _ _ _ _ _ (plane_mass_constant_le_sq _)⟩

theorem family_plane_mass_admissible_alt (Cg cb Cu cT CT C0 A : ℝ) : VanishingOnXAndXPlus.FamilyRankTwoMassEstimate Fm Cg cb Cu cT CT C0 A :=
  ⟨55 * max 1 (1 / sCl Fm), 0, fun _ _ _ u u' => plane_mass_bound_parameters _ _ u u' _ _ _ _ _ _ _ _ _ _ (plane_mass_constant_le_sq _)⟩

theorem family_plane_mass_admissible_k2 : LatticeIndexAndWeightTheory.FamilyRankTwoMassHyp Fm := fun _ _ _ _ _ _ =>
  ⟨55 * max 1 (1 / sCl Fm), 0, fun _ _ _ => plane_mass_bound_K2 _ _ _ _ _ _ _ _ _ _ _ (plane_mass_constant_le_sq _)⟩

theorem family_genus_bound_of_mass_ratio (Cg cb Cu cT CT C0 A : ℝ) (h1 : VanishingOnXAndXPlusMass.familyUnitInput Fm) (hCl : 1 ≤ sCl Fm) :
    VanishingOnXAndXPlusMass.Conclusion1Family Fm Cg cb Cu cT CT C0 A :=
  BridgeLemma.family_first_bound_of_mass_ratio Fm Cg cb Cu cT CT C0 A h1 (family_plane_mass_admissible Fm Cg cb Cu cT CT C0 A) hCl

theorem family_genus_bound_of_siegel_ratio (Cg cb Cu cT CT C0 A : ℝ) (hS : Formalism.HermitianLatticesTheory.SiegelMassRatio) (hCl : 1 ≤ sCl Fm) :
    VanishingOnXAndXPlusMass.Conclusion1Family Fm Cg cb Cu cT CT C0 A :=
  family_genus_bound_of_mass_ratio Fm Cg cb Cu cT CT C0 A (BridgeLemma.family_lattice_count_first_of_siegel Fm hS) hCl

end Family

end Formalism.MainNotions.BridgeLemma₂

end
