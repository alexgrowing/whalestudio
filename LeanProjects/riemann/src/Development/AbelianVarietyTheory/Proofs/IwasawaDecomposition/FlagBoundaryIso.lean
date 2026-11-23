import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam

section PullPresents

variable {X Z : Scheme.{0}} [IsIntegral X] (B : EffCartierData Z) (f : X ⟶ Z)
  (h : f (genericPoint X) ∉ B.idealSheaf.support)

open Classical in

def pullEqns (J : PUnit.{1} → B.ι) : X.functionFieldˣ :=
  if hJ : ∃ y, f y ∈ B.U (J PUnit.unit) then pullEqn B f h _ hJ.choose_spec else 1

theorem pullEqns_eq (J : PUnit.{1} → B.ι) {y : X} (hy : f y ∈ B.U (J PUnit.unit)) :
    pullEqns B f h J = pullEqn B f h _ hy := by
  rw [pullEqns, dif_pos ⟨y, hy⟩]
  rfl

theorem val_pullEqn (i : B.ι) {y : X} (hy : f y ∈ B.U i) (hg : f (genericPoint X) ∈ B.U i) :
    (pullEqn B f h i hy : X.functionField) =
      (f.stalkMap (genericPoint X)).hom ((Z.presheaf.germ _ _ hg).hom (B.f i)) := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  rfl

theorem fnOf_pull_g (J J' : PUnit.{1} → B.ι)
    (hg : genericPoint X ∈ (B.lb.pull f).U J ⊓ (B.lb.pull f).U J') :
    fnOf _ hg ((B.lb.pull f).g J J' : Γ(X, (B.lb.pull f).U J ⊓ (B.lb.pull f).U J')) =
      (f.stalkMap (genericPoint X)).hom ((Z.presheaf.germ _ _
        (⟨mem_pull.1 hg.1, mem_pull.1 hg.2⟩ : f (genericPoint X) ∈ B.U (J PUnit.unit) ⊓ B.U (J' PUnit.unit))).hom
        (B.trans (J PUnit.unit) (J' PUnit.unit) : Γ(Z, B.U (J PUnit.unit) ⊓ B.U (J' PUnit.unit)))) := by
  show fnOf _ hg (Units.val (∏ _k : PUnit.{1}, _ ^ (1 : ℤ))) = _
  rw [Fintype.prod_unique]
  erw [zpow_one, LB.val_res, fnOf_resG]
  exact (Scheme.Hom.germ_stalkMap_apply f (B.U (J PUnit.unit) ⊓ B.U (J' PUnit.unit)) (genericPoint X) _ _).symm

theorem presents_pullDiv : Presents (pullDiv B f h) (B.lb.pull f) (pullEqns B f h) := by
  refine ⟨pull_isLB B.isLB_lb f, fun J J' hg => ?_, fun J x hx => ?_⟩
  · have hi := mem_pull.1 hg.1
    have hj := mem_pull.1 hg.2
    rw [pullEqns_eq B f h J hi, pullEqns_eq B f h J' hj, val_pullEqn B f h _ hi hi, val_pullEqn B f h _ hj hj]
    erw [fnOf_pull_g B f J J' hg]
    rw [← map_mul]
    congr 1
    have e := congrArg (Z.presheaf.germ _ _ (⟨hi, hj⟩ : f (genericPoint X) ∈ B.U (J PUnit.unit) ⊓ B.U (J' PUnit.unit))).hom
      (B.trans_spec (J PUnit.unit) (J' PUnit.unit))
    erw [map_mul, germ_resG, germ_resG] at e
    exact e
  · have hx' := mem_pull.1 hx
    rw [pullEqns_eq B f h J hx']
    exact isEqn_pullDiv B f h _ hx'

end PullPresents

theorem lbIso_bdPull : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag)
    (k : s.Comp), LBIso ((Φ.C k).Y.lb (bdPull Φ k)) (s.T.BD.lb.pull ((Φ.C k).π ≫ genι s.T.Z)) :=
  fun _ _ _ _ _ _ _ Φ k => (presents_toLB (bdPull Φ k)).lbIso (presents_pullDiv _ _ _)

end GlobalTheory.ShFam
