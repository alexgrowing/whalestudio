import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrvEqSelf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
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

namespace GlobalTheory.Cartier.DomPull

variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X'] (φ : X' ⟶ X) [IsDominant φ]

theorem unitAt_map {x : X'} {f : X.functionField} (h : UnitAt (φ x) f) :
    UnitAt x (GlobalTheory.functionFieldMap φ f) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨φ.stalkMap x a, ha.map _, (functionFieldMap_algebraMap φ x a).symm⟩

abbrev unitsMap : X.functionFieldˣ →* X'.functionFieldˣ := Units.map (GlobalTheory.functionFieldMap φ).toMonoidHom

theorem germOf_map_eq (D : CartierDiv X) {x : X'} {g g' : X.functionFieldˣ} (hg : D.IsEqn (φ x) g)
    (hg' : D.IsEqn (φ x) g') : germOf x (unitsMap φ g) = germOf x (unitsMap φ g') := by
  rw [germOf_eq_iff]
  have := unitAt_map φ (hg.iff_unitAt.1 hg')
  simpa only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, map_div₀] using this

def pullback (D : CartierDiv X) : CartierDiv X' :=
  show cartierGroup X' from ⟨fun x => germOf x (unitsMap φ (D.exists_isEqn (φ x)).choose), fun x => by
    obtain ⟨U, hU, g, hg⟩ := D.exists_isEqn_nhds (φ x)
    exact ⟨φ ⁻¹ᵁ U, hU, unitsMap φ g, fun y hy =>
      germOf_map_eq φ D (D.exists_isEqn (φ y)).choose_spec (hg _ hy)⟩⟩

theorem isEqn_pullback (D : CartierDiv X) {x : X'} {g : X.functionFieldˣ} (h : D.IsEqn (φ x) g) :
    (pullback φ D).IsEqn x (unitsMap φ g) :=
  germOf_map_eq φ D (D.exists_isEqn (φ x)).choose_spec h

theorem fnOf_app {U : X.Opens} (hU : genericPoint X' ∈ φ ⁻¹ᵁ U) (a : Γ(X, U)) :
    fnOf (φ ⁻¹ᵁ U) hU (φ.app U a) = GlobalTheory.functionFieldMap φ (fnOf U (gen_mem (x := φ (genericPoint X')) hU) a) := by
  rw [← algebraMap_germ (x := φ (genericPoint X')) hU a, functionFieldMap_algebraMap]
  erw [Scheme.Hom.germ_stalkMap_apply]
  exact (algebraMap_germ (X := X') hU _).symm

def pullEqns (D : CartierDiv X) (J : ((toLB D).pull φ).ι) : X'.functionFieldˣ :=
  unitsMap φ (J PUnit.unit).1.2

theorem fnOf_pull_g (D : CartierDiv X) (J J' : ((toLB D).pull φ).ι)
    (hg : genericPoint X' ∈ ((toLB D).pull φ).U J ⊓ ((toLB D).pull φ).U J') :
    fnOf _ hg (((toLB D).pull φ).g J J' : Γ(X', ((toLB D).pull φ).U J ⊓ ((toLB D).pull φ).U J')) =
      GlobalTheory.functionFieldMap φ (((J PUnit.unit).1.2 : X.functionField) / ((J' PUnit.unit).1.2 : X.functionField)) := by
  have h₀ : genericPoint X' ∈ φ ⁻¹ᵁ ((toLB D).U (J PUnit.unit) ⊓ (toLB D).U (J' PUnit.unit)) :=
    ⟨mem_pull.1 hg.1, mem_pull.1 hg.2⟩
  show fnOf _ hg (Units.val (∏ _k : PUnit.{1}, _ ^ (1 : ℤ))) = _
  rw [Fintype.prod_unique]
  erw [zpow_one, LB.val_res, fnOf_resG]
  exact (fnOf_app φ h₀ _).trans (congrArg _ (fnOf_toLB_g _ _ _))

theorem presents_pullback (D : CartierDiv X) :
    Presents (pullback φ D) ((toLB D).pull φ) (pullEqns φ D) := by
  refine ⟨LB.isLB_pull (isLB_toLB D) φ, fun J J' hg => ?_, fun J x hx => ?_⟩
  · rw [fnOf_pull_g φ D J J' hg]
    show GlobalTheory.functionFieldMap φ _ = GlobalTheory.functionFieldMap φ _ * GlobalTheory.functionFieldMap φ _
    rw [← map_mul, div_mul_cancel₀ _ (Units.ne_zero _)]
  · exact isEqn_pullback φ D ((J PUnit.unit).2.2 _ (mem_pull.1 hx))

end GlobalTheory.Cartier.DomPull

namespace GlobalTheory.Cartier

open DomPull in

theorem exists_pullback_cartierDiv : ∀ (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (φ : X' ⟶ X) [IsDominant φ]
    (D : CartierDiv X), ∃ D' : CartierDiv X', cls (toLB D') (isLB_toLB D') =
      cls ((toLB D).pull φ) (LB.isLB_pull (isLB_toLB D) φ) ∧
      ∀ (x : X') (g : X.functionFieldˣ), D.IsEqn (φ x) g →
        D'.IsEqn x (Units.map (GlobalTheory.functionFieldMap φ).toMonoidHom g) := by
  intro X X' _ _ φ _ D
  refine ⟨pullback φ D, ?_, fun x g h => isEqn_pullback φ D h⟩
  rw [← toPic_apply]
  exact (presents_pullback φ D).toPic_eq

end GlobalTheory.Cartier
