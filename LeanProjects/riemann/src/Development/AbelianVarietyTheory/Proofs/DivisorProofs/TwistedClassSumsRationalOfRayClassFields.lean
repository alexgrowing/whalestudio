import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRationalOfOneMapOverL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoverFieldOfContainsRayField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTieCoordBase
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open GlobalTheory.OntoChain
set_option autoImplicit false
noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistedRatBase

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem exists_base_lift (hU : R.LUnif) (hB : GlobalTheory.BigOn.BaseLinks R F)
    (hRk : Formalism.L2.Indef.Tree.RankRows ((R.toCx F).data F.cr false)) (i : Fin D.R.m) :
    ∃ (x₀ : A.fam.amb.FL i A.μ0) (y : Fin (R.nW i) → D.what₂.LL),
      (R.FW i).j (sg0 D A) y = R.thG i A.μ0 (R.jV i A.μ0 x₀) ∧ (R.FW i).j (sg0 D A) y ≠ 0 := by
  refine Classical.byContradiction fun hn => ?_
  have hd : 0 < Module.finrank D.what₂.LL (R.WL F false i) := hRk.1.trans_eq (hRk.2 i).symm
  obtain ⟨y, hy⟩ : ∃ y, (GlobalTheory.OntoChain.thetaMat R F i A.μ0).mulVec y = fun _ => 1 :=
    ((R.toCx F).liftMat_bij F.cr false (RealDat.kForm hU false) (RealDat.ewNorm false) (RealDat.nP_pos false) hB.1
      hB.2.1 i A.μ0).2 _
  have h1 := GlobalTheory.BigOnBase.j_thetaMat_base hB i A.μ0 y
  refine hn ⟨(A.fam.L i A.μ0).toF (GlobalTheory.OntoChain.liftLvl F) (GlobalTheory.OntoChain.liftSub R F i A.μ0) y,
    GlobalTheory.OntoChain.coordMap R F i ((GlobalTheory.OntoChain.thetaMat R F i A.μ0).mulVec y), h1, fun h0 => ?_⟩
  have h2 : GlobalTheory.OntoChain.coordMap R F i ((GlobalTheory.OntoChain.thetaMat R F i A.μ0).mulVec y) = 0 :=
    (injective_iff_map_eq_zero _).1 (j_injective hU i) _ h0
  have h3 := (injective_iff_map_eq_zero _).1 (GlobalTheory.OntoChain.coordMap_injective (R := R) (F := F) i) _ h2
  exact one_ne_zero (congrFun (hy.symm.trans h3) ⟨0, hd⟩)

theorem baseLiftNeZero (hU : R.LUnif) (hB : GlobalTheory.BigOn.BaseLinks R F)
    (hRk : Formalism.L2.Indef.Tree.RankRows ((R.toCx F).data F.cr false)) :
    ∀ i, ∃ x₀ : A.fam.amb.FL i A.μ0, R.thG i A.μ0 (R.jV i A.μ0 x₀) ≠ 0 := fun i =>
  (exists_base_lift hU hB hRk i).imp fun _ h => h.elim fun _ h => h.1.symm.trans_ne h.2

theorem twistedRational_of_rayField : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (O : ∀ i, OMDat J.toCore R i Unit (fun _ => A.μ0)), R.Char F → IoExt R → R.LUnif → (∀ i, OMPins J R κ v₀ O i) → QGuard R → (∀ i, OneMapRowR J R κ v₀ O (fun _ => 1) i) → BaseLinks R F → RankRows ((R.toCx F).data F.cr false) → (∀ t, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK D) (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel R t)) → TwistedRational R F (fun _ => 1) := by
  intro D G _ _ Pl0 T0 A J _ R F κ v₀ fw O hC hio hU hO hQ hrow hB hRk hray
  exact GlobalTheory.TwistedClassSum.twistedRational hC fw hio hU hO hQ hrow
    (GlobalTheory.TwistField.coverField_of_containsRayField D G Pl0 T0 A J R fw.laws hC.lev hQ hray) (baseLiftNeZero hU hB hRk)

end GlobalTheory.TwistedRatBase
