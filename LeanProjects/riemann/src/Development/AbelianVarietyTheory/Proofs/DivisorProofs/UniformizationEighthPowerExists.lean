import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8LB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Laws3
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTotalClosed
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalStructureE8PowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8PowerBundleHypothesisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitExtensionModuloIdealEighthPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedSemiAbelianSplitModMaximalIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8MumfordBundlePowerSectionNonvanishingClosedFibStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericEighthPowerUniformisedIsPolarisedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8

theorem isAdmissibleBase_of_completeNormalLocalCharZero (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (h : IsCN V₁) :
    GlobalTheory.LN.admitted V₁ (maximalIdeal V₁) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  letI : Field (V₁ ⧸ maximalIdeal V₁) := Ideal.Quotient.field _
  exact ⟨⟨h1, inferInstance, h2, h3⟩, h3, h4, inferInstance, inferInstance⟩

theorem exists_unif_pow8 : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ P : PolAV (Sp (FractionRing V₁)), SharpOver F W P y → ∃ D : DegData V₁ (maximalIdeal V₁), Nonempty (Unif (maximalIdeal V₁) D P (powObj G₀ 8)) := by
  intro g n o _ ζ F W hW V₁ _ _ _ hCN D₀ G₀ _ _ A₀ U₀ y α α₂ hS hpb hsq hlb P hP
  have hL := GlobalTheory.abelianSchemeLaws_all
  let P₀ := GlobalTheory.ValueForm.modelCP U₀.toUnifPre hL.1.globalFns
  obtain ⟨Pc, hPc⟩ := GlobalTheory.T.cubical_structure_e8_power _ G₀ P₀ W
  obtain ⟨gen, hgen, hA⟩ := GlobalTheory.T.generic_eighth_power_uniformised_is_polarised g n o ζ F W V₁ D₀ G₀ A₀ U₀ y α α₂ hpb hsq hlb P hP
  have hW8 : GlobalTheory.LN.HypW (powObj G₀ 8) Pc.L.L := hPc ▸ GlobalTheory.T.hypW_e8LB_powObj _ G₀ P₀ W hW
  have hT : GlobalTheory.LN.ThetaNZ (powObj G₀ 8) Pc.L.L :=
    hPc ▸ GlobalTheory.T.thetaNZ_e8LB_powObj hL.1 hL.2 GlobalTheory.LN.ega_holds V₁ hCN D₀ G₀ A₀ U₀ hS W hW
  have hA' : LBIso (P.L.pull gen.hom.left) (Pc.L.L.pull (pullback.fst (powObj G₀ 8).hom (jK V₁))) := hPc ▸ hA
  letI : Field (V₁ ⧸ maximalIdeal V₁) := Ideal.Quotient.field _
  obtain ⟨D, U, -, -⟩ := GlobalTheory.PrimeUnif.exists_unif hL.1 hL.2 GlobalTheory.laws3 GlobalTheory.LN.ega_holds GlobalTheory.uniformisation_total_closed V₁
    (maximalIdeal V₁) (isAdmissibleBase_of_completeNormalLocalCharZero V₁ hCN) inferInstance (powObj G₀ 8) Pc
    (GlobalTheory.PowGrp.isSemiAbelian_pow _ _ _ 8 (powIsPowGrp G₀ 8) hS) hW8
    (GlobalTheory.T.splitOver_powObj_eight V₁ G₀ _ (GlobalTheory.T.uniformised_semiAbelian_split_mod_maximalIdeal V₁ hCN D₀ G₀ A₀ U₀ hS)) hT P gen hgen hA'
  exact ⟨D, ⟨U⟩⟩

end GlobalTheory.PowE8
end
