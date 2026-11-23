import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitLatticesIsoFormsProportionalRamification
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitMemRangeJKOfMemRangeJ
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GoodRed

theorem subsingleton_lattice_of_extends : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F)
    (ξ : Sp T.V ⟶ F.X), jK T.V ≫ ξ = T.y → Subsingleton T.D.toPre.X := by
  intro g n o _ ζ F T ξ hξ

  have hB := GlobalTheory.isAbelianScheme_pullback_obj ξ F.univ.A F.univ.ab
  haveI := T.U.gen_hom

  have h₁ := ((isGrpPullback_of_iso T.U.gen).comp T.cart).congr ((Category.id_comp _).trans hξ.symm) rfl
  have h₂ := (isGrpPullback_pullback ((Over.pullback ξ).obj F.univ.A) (jK T.V)).comp (isGrpPullback_pullback F.univ.A ξ)
  obtain ⟨e, he, -⟩ := grpPullback_iso h₁ h₂

  obtain ⟨E, -, -⟩ := TraitUniq.extIso T.semi (GlobalTheory.isSemiAbelian_of_isAbelianScheme _ hB) e he
  have hp : IsProper T.G.hom := by
    have := hB.proper
    have : IsIso E.hom.left := inferInstanceAs (IsIso ((Over.forget _).map E.hom))
    rw [← Over.w E.hom]
    infer_instance

  have hmax : (maximalIdeal T.V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (T.V ⧸ maximalIdeal T.V ^ (0 + 1)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  letI := hF.toField
  let k := T.U.gt 0
  have m : Mono k.i := ⟨fun a b h => k.isKernel.hom_ext h (CartesianMonoidalCategory.toUnit_unique _ _)⟩
  exact ArcNotAbelian.subsingleton_of_mem_abLocus T.G T.semi _ hF _ (closedPoint _)
    (fun _ _ _ _ _ => inferInstance) T.D.toPre.X k.i k.i_hom

end GlobalTheory.Poinc.GoodRed
