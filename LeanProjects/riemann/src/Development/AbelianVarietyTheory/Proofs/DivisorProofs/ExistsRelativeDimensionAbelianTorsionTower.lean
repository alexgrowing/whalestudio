import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeBaseChangeRigid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearCanonicalMapPrimitiveDeRhamRigExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfForallField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRigidExtensionsEqHeightAndDimAddDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToRigidifiedExtensionBijectivePNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneRanksFieldCharP
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TowerDim

theorem exists_smoothOfRelativeDimension_of_hodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]
    (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ G : PDivGroup p R, G.TorsionTower A → ∃ g, SmoothOfRelativeDimension g A.hom := by
  intro hH p _ R _ hp A _ hA G t
  have hF : GlobalTheory.Published.AbelianDeRham.Free := (GlobalTheory.abelianDeRham_free_baseChange_rigid hH).1
  have hs := hA.smooth
  refine ⟨G.height / 2, GlobalTheory.FibreDim.smoothOfRelativeDimension_of_forall_field R A _ hs fun k _ _ ↦ ?_⟩
  have hk : IsNilpotent (p : k) := by simpa using hp.map (algebraMap R k)
  have hk0 : (p : k) = 0 := hk.eq_zero
  letI : GrpObj ((Over.pullback (spMap (algebraMap R k))).obj A) := Functor.grpObjObj
  have h := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A (spMap (algebraMap R k))
  have hAk : IsAbelianScheme ((Over.pullback (spMap (algebraMap R k))).obj A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ A hA
  obtain ⟨gk, hgk⟩ := GlobalTheory.AbelianDim.exists_relDim k ((Over.pullback (spMap (algebraMap R k))).obj A) hAk
  let tk := t.baseChange h
  obtain ⟨L, hL⟩ := GlobalTheory.PtExt.exists_canMap k ((Over.pullback (spMap (algebraMap R k))).obj A) p
    (G.baseChange k) tk hAk
  have hbij : Function.Bijective L :=
    GlobalTheory.T.deRham_to_rigidified_extension_bijective_p_nilpotent hH p k hk _ gk hAk hgk (G.baseChange k) tk L fun c ↦ (hL c (L c)).2 rfl
  obtain ⟨hfin, hprj, hrk⟩ := hF.prim hAk hgk
  have h1 : Module.finrank k (primDR ((Over.pullback (spMap (algebraMap R k))).obj A)) = 2 * gk := by
    have := hrk ⊥
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have h2 : Module.finrank k (G.baseChange k).RigExt = G.height :=
    (GlobalTheory.PDivGroup.finrank_rigExt_omega p k hk0 (G.baseChange k)).2.2.1
  have h3 : 2 * gk = G.height := by
    rw [← h1, ← h2]; exact (LinearEquiv.ofBijective L hbij).finrank_eq
  have h4 : G.height / 2 = gk := by omega
  rw [h4]
  exact hgk

end GlobalTheory.TowerDim
