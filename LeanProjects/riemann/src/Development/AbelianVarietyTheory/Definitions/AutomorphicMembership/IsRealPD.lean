import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP

noncomputable section
namespace GlobalTheory.MemLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per
variable {l : ℕ} [Fact l.Prime]

def ringsOf (C : Core l) : LocRings l :=
  letI aU : Algebra ↥(MaximalUnramifiedExtension l) (Per.Bcris l) := C.u.toAlgebra
  letI aQ : Algebra ℚ_[l] (Per.Bcris l) := (C.u.comp (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))).toAlgebra
  letI aO : Algebra (Om l) (Per.BdR l) := ((algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o).toAlgebra
  letI aQ' : Algebra ℚ_[l] (Per.BdR l) :=
    (((algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o).comp (algebraMap ℚ_[l] (Om l))).toAlgebra
  { B := Per.Bcris l
    BdR := Per.BdR l
    aQB := aQ
    aUB := aU
    tUB := IsScalarTower.of_algebraMap_eq fun _ => rfl
    aOdR := aO
    aQdR := aQ'
    tQdR := IsScalarTower.of_algebraMap_eq fun _ => rfl }

def eB (C : Core l) : (ringsOf C).B ≃+* Per.Bcris l := RingEquiv.refl (Per.Bcris l)

def eD (C : Core l) : (ringsOf C).BdR ≃+* Per.BdR l := RingEquiv.refl (Per.BdR l)

structure IsRealPD (C : Core l) (K : FinExt l)
    (PD : WeaklyAdmissibleFiltrations.PeriodData ↥(GK K) ℚ_[l] ↥(K0 K) ↥K.1 (ringsOf C).B (ringsOf C).BdR) : Prop where
  p : PD.p = l
  actB : ∀ g b, eB C (PD.actB g b) = Per.σB (g : GQ l) (eB C b)
  actdR : ∀ g b, eD C (PD.actdR g b) = Per.σD (g : GQ l) (eD C b)
  φ : ∀ b, eB C (PD.φ b) = Per.φB l (eB C b)
  ι : ∀ b, eD C (PD.ι b) = C.ι (eB C b)
  t : eB C PD.t = algebraMap (Per.Acris l) (Per.Bcris l) C.t
  χ : ∀ g, ((PD.χ g : ℚ_[l]ˣ) : ℚ_[l]) = ((C.χ (g : GQ l) : ℤ_[l]) : ℚ_[l])
  fil : ∀ a x, x ∈ PD.Fil a ↔ eD C x ∈ Per.FilD l a
  σ : ∀ (x : ↥(K0 K)) (c : ↥(MaximalUnramifiedExtension l)), (c : Om l) = (x : Om l) →
    ((PD.σ x : ↥(K0 K)) : Om l) = ((C.σ c : ↥(MaximalUnramifiedExtension l)) : Om l)

end GlobalTheory.MemLoc
