import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreePointHalfLevelLift
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreePointHalfLevelLiftStatement

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
section Point
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix Formalism.L2.Theta Formalism.IndefR
open scoped TensorProduct
namespace GlobalTheory.NeatOne
end GlobalTheory.NeatOne
end Point
section Family
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open Formalism.IndefR.FWT
namespace GlobalTheory.NeatOne
theorem neat_divisor_free_half_lifts : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Gram → Lifts fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ k : Fin 2,
    GlobalTheory.DefPt.FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c
      (fun h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k => (p.O i).lev2 ((p.R.eG.trans p.cG).symm (h : G0g (Fm.D x ι).nd))) := by
  intro _ _
  refine Formalism.MainNotions.Closed.imp (GlobalTheory.CovTop.Sizes.hostN 6) fun Fm CH _ hh => ?_
  obtain ⟨C, hC, a, ha⟩ := hh
  exact ⟨C, hC, a, fun x hx hle ι p hp i _ k => free_half p i (rank_add_one_lt Fm x hx ι _ C (ha x hx hle ι p hp i)) k⟩
end GlobalTheory.NeatOne
end Family
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open Formalism.IndefR.FWT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_free_half_lift_of_neat : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Gram → Lifts fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ k : Fin 2,
    GlobalTheory.DefPt.FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c
      (fun h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k => (p.O i).lev2 ((p.R.eG.trans p.cG).symm (h : G0g (Fm.D x ι).nd))) := by
  first | exact @_root_.GlobalTheory.NeatOne.neat_divisor_free_half_lifts | exact _root_.GlobalTheory.NeatOne.neat_divisor_free_half_lifts | (intros; apply _root_.GlobalTheory.NeatOne.neat_divisor_free_half_lifts <;> assumption)
end
