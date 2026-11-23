import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapCompStalkAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentImagesLinearIndependent
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.TopForm

theorem frame_eq_unit_smul_dForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U' : (X₀ TF.Y Z).Opens) (ω : TopForm.FormsOn (s₀ TF.Y Z) Dw.dim U'), TopForm.IsFrame ω → ∀ hx : x ∈ U', letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra; ∃ (g : Fin Dw.dim → (X₀ TF.Y Z).presheaf.stalk x) (bΩ : Module.Basis (Fin Dw.dim) ((X₀ TF.Y Z).presheaf.stalk x) Ω[(X₀ TF.Y Z).presheaf.stalk x⁄c.F]) (u : (X₀ TF.Y Z).presheaf.stalk x), (∀ i, bΩ i = KaehlerDifferential.D c.F ((X₀ TF.Y Z).presheaf.stalk x) (g i)) ∧ IsUnit u ∧ formOf U' (gen_mem hx) ω = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField u • TopForm.dForm (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) (fun i => algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (g i)) := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U' ω hω hx
  letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra
  obtain ⟨U, y, b, hUU', hxU, hU, hb⟩ :=
    GlobalTheory.AdaptedFrame.exists_basis_dFun (s₀ TF.Y Z) Dw.dim hx
  have hy : IsFreeGen Γ(X₀ TF.Y Z, U) (dOn (s₀ TF.Y Z) y) := isFreeGen_dForm y b hb
  have hres : IsFrame (resForm hUU' ω) := hω.res hU hUU'
  obtain ⟨a, ha⟩ := hy.2 (resForm hUU' ω)
  have hau : IsUnit a := by
    have := hres.gen
    rw [← ha] at this
    exact hy.smul_iff.1 this
  have hgU : genericPoint (X₀ TF.Y Z) ∈ U := gen_mem hxU
  have hform : formOf U' (gen_mem hx) ω =
      fnOf U hgU a • dForm (constFn (s₀ TF.Y Z)) (fun i => fnOf U hgU (y i)) := by
    rw [← formOf_resForm hUU' hgU ω, ← ha, map_smulₛₗ]
    congr 1
    exact formMap_dForm _ _ _
  letI iΓ : Algebra c.F Γ(X₀ TF.Y Z, U) := (algX (s₀ TF.Y Z) U).toAlgebra
  letI iΓA : Algebra Γ(X₀ TF.Y Z, U) ((X₀ TF.Y Z).presheaf.stalk x) :=
    ((X₀ TF.Y Z).presheaf.germ U x hxU).hom.toAlgebra
  have hsc : algebraMap c.F ((X₀ TF.Y Z).presheaf.stalk x) =
      (algebraMap Γ(X₀ TF.Y Z, U) ((X₀ TF.Y Z).presheaf.stalk x)).comp
        (algebraMap c.F Γ(X₀ TF.Y Z, U)) := by
    ext t
    change ((X₀ TF.Y Z).presheaf.germ ⊤ x trivial).hom (algX (s₀ TF.Y Z) ⊤ t) =
      ((X₀ TF.Y Z).presheaf.germ U x hxU).hom (algX (s₀ TF.Y Z) U t)
    rw [← resG_comp_algX (s₀ TF.Y Z) (le_top : U ≤ ⊤), RingHom.comp_apply, germ_resG]
  haveI : IsScalarTower c.F Γ(X₀ TF.Y Z, U) ((X₀ TF.Y Z).presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' hsc
  haveI : IsLocalization.AtPrime ((X₀ TF.Y Z).presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  haveI : Algebra.FormallyEtale Γ(X₀ TF.Y Z, U) ((X₀ TF.Y Z).presheaf.stalk x) :=
    .of_isLocalization (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale c.F Γ(X₀ TF.Y Z, U)
    ((X₀ TF.Y Z).presheaf.stalk x)
  refine ⟨fun i => ((X₀ TF.Y Z).presheaf.germ U x hxU).hom (y i), hbc.basis b,
    ((X₀ TF.Y Z).presheaf.germ U x hxU).hom a, fun i => ?_, hau.map _, ?_⟩
  · rw [IsBaseChange.basis_apply, hb]
    exact KaehlerDifferential.map_D c.F c.F _ _ (y i)
  · rw [hform]
    simp only [algebraMap_germ]
end GlobalTheory.LogKSDiv
