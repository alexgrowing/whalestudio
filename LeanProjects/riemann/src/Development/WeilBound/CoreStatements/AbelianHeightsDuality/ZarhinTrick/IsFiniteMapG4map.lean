import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibAmpleD
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorMapFiniteOfSplit
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleFormBundlePowerOfPosDef
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.IsFiniteMapTensorHom
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FourfoldProductExt

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar.XB

variable {S : Scheme.{0}}

def fourfoldProductMap {G H : Over S} (h : G ⟶ H) : G4 G ⟶ G4 H := h ⊗ₘ (h ⊗ₘ (h ⊗ₘ h))

theorem isFinite_map_g4map {T : Scheme.{0}} (s : T ⟶ S) {G H : Over S} (h : G ⟶ H)
    (hh : IsFinite ((Over.pullback s).map h).left) : IsFinite ((Over.pullback s).map (fourfoldProductMap h)).left :=
  isFinite_map_tensorHom s _ _ hh (isFinite_map_tensorHom s _ _ hh (isFinite_map_tensorHom s _ _ hh hh))

variable {Ω : Type} [Field Ω]

theorem isIso_inv_left {G : Over (Sp Ω)} [GrpObj G] [IsCommMonObj G] : IsIso ((𝟙 G)⁻¹ : G ⟶ G).left := by
  have e : ((𝟙 G)⁻¹ : G ⟶ G) ≫ (𝟙 G)⁻¹ = 𝟙 G := by
    rw [GrpObj.comp_inv, Category.comp_id, inv_inv]
  haveI : IsIso ((𝟙 G)⁻¹ : G ⟶ G) := ⟨⟨(𝟙 G)⁻¹, e, e⟩⟩
  exact (Over.forget (Sp Ω)).map_isIso ((𝟙 G)⁻¹ : G ⟶ G)

theorem relAmple_sym {G : Over (Sp Ω)} [GrpObj G] [IsCommMonObj G] [IsProper G.hom] {L : LB G.left} (hL : L.IsLB)
    (ha : Out.RelAmple G L) :
    Out.RelAmple G (LB.LinComb L (K := Fin 2) ![𝟙 G.left, ((𝟙 G)⁻¹ : G ⟶ G).left] ![1, 1]) := by
  haveI : IsIso ((𝟙 G)⁻¹ : G ⟶ G).left := isIso_inv_left
  haveI : IsAffineHom ((𝟙 G)⁻¹ : G ⟶ G).left := inferInstance
  have hLi : Out.RelAmple G (L.pull ((𝟙 G)⁻¹ : G ⟶ G).left) :=
    GlobalTheory.PosDefAmple.relAmple_pull_of_isAffineHom _ hL ha
  have hN := LB.isLB_linComb (K := Fin 2) hL ![𝟙 G.left, ((𝟙 G)⁻¹ : G ⟶ G).left] ![1, 1]
  refine GlobalTheory.relAmple_of_isAmpleLB G hN (fun U hU => ?_)
  have hP := LB.isLB_pull hL ((𝟙 G)⁻¹ : G ⟶ G).left
  have h1 := GlobalTheory.isAmpleLB_of_relAmple G hL ha U hU
  have h2 := GlobalTheory.isAmpleLB_of_relAmple G hP hLi U hU
  have a1 := LB.isLB_pull hN (G.hom ⁻¹ᵁ U).ι
  have a2 := LB.isLB_pull hL (G.hom ⁻¹ᵁ U).ι
  have a3 := LB.isLB_pull hP (G.hom ⁻¹ᵁ U).ι
  have a4 := LB.isLB_div a1 a2
  have a5 := LB.isLB_div a4 a3
  refine GlobalTheory.IsAmpleLB.tensor h1 h2 a1 ?_
  rw [← cls_eq_zero_iff a5, cls_div a4 a3 a5, cls_div a1 a2 a4, cls_pull hN _ a1, cls_pull hL _ a2,
    cls_pull hP _ a3, cls_pull hL _ hP, cls_linComb hL _ _ hN]
  simp [Fin.sum_univ_two, pull_id]

end PositivityTheory.PrwZar.XB
