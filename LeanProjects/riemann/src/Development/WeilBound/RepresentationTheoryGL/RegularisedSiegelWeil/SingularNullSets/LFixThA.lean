import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCharacterNormEulerFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterConductorCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicAddCharEqArchimedeanMulFinprodLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFixTh

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open PositivityTheory.Rg.Rsw.L

variable {D : D7} {n : ℕ}

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := by simp [mat]

theorem mat_mul_inv (g : G D n) : mat g * mat g⁻¹ = 1 := by simp [mat]

theorem mat_proj (g : G D n) (v : Pl D) :
    ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) (proj D.sp.cm.sig (Jst D n) v g)).1 : Matrix _ _ _) =
      (mat g).map (cv D v) := rfl

theorem compInf_eq (w : InfinitePlace D.host.F) (x : AE D) :
    compInf D.host.F D.host.E w x = Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id D.host.F D.host.E)
      (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]

theorem kOff_inf {S : Finset (Pl D)} {g : G D n} (hg : g ∈ KOff D n S) (w : InfinitePlace D.host.F) (i j : Fin (n + n)) :
    compInf D.host.F D.host.E w (mat g i j) = (1 : Matrix (Fin (n + n)) (Fin (n + n)) _) i j := by
  have h1 := (mem_levelOff.1 hg).1
  have h2 : (mat g).map (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom = 1 := by
    exact congrArg Units.val (MonoidHom.mem_ker.1 h1)
  have h3 := congrFun (congrFun h2 i) j
  simp only [Matrix.map_apply] at h3
  rw [compInf_eq]
  change _ = (1 : Matrix (Fin (n + n)) (Fin (n + n)) _) i j
  rw [show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (mat g i j) = _ from h3]
  by_cases e : i = j
  · subst e; simp
  · simp [Matrix.one_apply_ne e]

theorem kOff_at {S : Finset (Pl D)} {g : G D n} (hg : g ∈ KOff D n S) {v : Pl D} (hv : v ∈ S) (i j : Fin (n + n)) :
    cv D v (mat g i j) = (1 : Matrix (Fin (n + n)) (Fin (n + n)) _) i j := by
  have h := (mem_levelOff.1 hg).2.1 v hv
  have := congrArg (fun x => ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) x).1 : Matrix _ _ _)) h
  simp only [mat_proj, map_one, Units.val_one] at this
  have := congrFun (congrFun this i) j
  simpa using this

theorem kOff_int {S : Finset (Pl D)} {g : G D n} (hg : g ∈ KOff D n S) {v : Pl D} (hv : v ∉ S) (i j : Fin (n + n)) :
    cv D v (mat g i j) ∈ intLoc D.host.F D.host.E v ∧ cv D v (mat g⁻¹ i j) ∈ intLoc D.host.F D.host.E v := by
  have h := (mem_levelOff.1 hg).2.2 v hv
  have hs : ∀ y, y ∈ latLoc D.host.F (stdLattice D.host.E (n + n)) v ↔
      (mat g).map (cv D v) *ᵥ y ∈ latLoc D.host.F (stdLattice D.host.E (n + n)) v := h
  have he : ∀ k : Fin (n + n), (Pi.single k 1 : Fin (n + n) → Fv D.host.F v ⊗[D.host.F] D.host.E) ∈
      latLoc D.host.F (stdLattice D.host.E (n + n)) v := fun k => by
    rw [mem_latLoc_stdLattice]
    intro l
    by_cases e : l = k
    · subst e; simp
    · simp [Pi.single_eq_of_ne e]
  have hM : (mat g).map (cv D v) * (mat g⁻¹).map (cv D v) = 1 := by
    have := (RingHom.mapMatrix (cv D v)).map_mul (mat g) (mat g⁻¹)
    rw [mat_mul_inv, map_one] at this
    exact this.symm
  constructor
  · have := mem_latLoc_stdLattice.1 ((hs _).1 (he j)) i
    simpa [Matrix.mulVec_single_one] using this
  · have h2 : (mat g⁻¹).map (cv D v) *ᵥ Pi.single j 1 ∈ latLoc D.host.F (stdLattice D.host.E (n + n)) v := by
      refine (hs _).2 ?_
      rw [Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]
      exact he j
    have := mem_latLoc_stdLattice.1 h2 i
    simpa [Matrix.mulVec_single_one] using this

end PositivityTheory.Rg.Rsw.L.LFixTh

end
