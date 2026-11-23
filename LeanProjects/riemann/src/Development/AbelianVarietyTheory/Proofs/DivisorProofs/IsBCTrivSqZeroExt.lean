import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructureStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniqueIsConnOfLift
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SmoothOfRelativeDimensionTensor

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroCrys

theorem isBC_trivSqZeroExt : ∀ (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V]
    [IsCentralScalar k V] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ →
    ∀ (h2 : RingHom.ker (TrivSqZeroExt.fstHom k k V).toRingHom ^ 2 = 0)
      (m : GrpMor (dp0 k) (𝟙 _) A₀ (divided₂ h2) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀
        (algebraMap k (TrivSqZeroExt k V)) (𝟙 _) (Over.Hom.left (𝟙 A₀))), m.IsBC := by
  intro k _ V _ _ _ _ A₀ _ hA h2 m
  have := hA.smooth
  obtain ⟨g, hg⟩ := GlobalTheory.SerreDim.exists_dim_of_grpObj A₀
  have e : (𝟙 _ : Sp k ⟶ Sp k) = spMap (RingHom.id k) := (Cris.spMap_id k).symm
  have h := (GlobalTheory.CrysConn.isGrpPullback_refl A₀).congr e rfl
  have key : ∀ (t : Sp k ⟶ Sp k), t = spMap (RingHom.id k) →
      ∀ m : GrpMor (dp0 k) t A₀ (divided₂ h2) (spMap (TrivSqZeroExt.fstHom k k V).toRingHom) A₀
        (algebraMap k (TrivSqZeroExt k V)) (𝟙 _) (Over.Hom.left (𝟙 A₀)), m.IsBC := by
    rintro _ rfl m
    exact GlobalTheory.CrysConn.isBC_of_lift GlobalTheory.T.abelianScheme_firstDeRham_structure hA hg (isDPNilpotent_bot k) Function.surjective_id
      ((RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id) h (isDPNilpotent_squareZero _)
      (fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩) rfl m (GlobalTheory.CrysConn.isGrpPullback_refl A₀)
  exact key _ e m

end GlobalTheory.SqZeroCrys
