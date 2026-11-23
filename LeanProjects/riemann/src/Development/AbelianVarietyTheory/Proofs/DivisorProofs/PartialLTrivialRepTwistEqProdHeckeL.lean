import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFormAniso
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.RallisEuler

open GlobalTheory.LFun in

theorem trivPar_euler : ∀ {D : D7} (χ : (AE D)ˣ →* Circle) (Sf : Finset (FinPl D)) (n : ℕ), GlobalTheory.LFun.UnrOff χ (Sf : Set (FinPl D)) → EqRight (fun s => ∏ i ∈ Finset.range n, GlobalTheory.LFun.charL χ⁻¹ (Sf : Set (FinPl D)) (s + (n : ℂ) / 2 - i)) (fun s => GlobalTheory.LFun.LSD D Sf (GlobalTheory.BottomRallis.trivPar n) χ (s + 1 / 2)) := by
  intro D χ Sf n hU
  refine ⟨(n : ℝ) / 2 + 1, fun s hs => ?_⟩
  have hs' : (n : ℝ) / 2 + 1 < s.re := hs
  set T := above D.host.E (Sf : Set (FinPl D)) with hT

  have hc : ∀ i ∈ Finset.range n, HasProd (fun w : {w // w ∉ T} => locL (charFam χ⁻¹) w.1 (s + (n : ℂ) / 2 - i))
      (charL χ⁻¹ (Sf : Set (FinPl D)) (s + (n : ℂ) / 2 - i)) := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast Finset.mem_range.1 hi
    refine (converges_charFam T χ⁻¹ ?_).hasProd
    simp
    linarith
  have hp := hasProd_prod hc
  show (∏ i ∈ Finset.range n, charL χ⁻¹ (Sf : Set (FinPl D)) (s + (n : ℂ) / 2 - i)) =
    LSD D Sf (GlobalTheory.BottomRallis.trivPar n) χ (s + 1 / 2)
  rw [← hp.tprod_eq]
  unfold LSD LSTw LS eulerProd
  refine tprod_congr fun w => ?_
  have hw : UnrAt χ⁻¹ w.1 := (hU w.1 w.2).inv
  rw [GlobalTheory.BottomRallis.trivPar, twist_segFam, locL_segFam']
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [locL, locL, charFam_of_unrAt hw, val_inv]
  congr 2
  · simp
  · congr 1
    push_cast
    ring

end GlobalTheory.RallisEuler
