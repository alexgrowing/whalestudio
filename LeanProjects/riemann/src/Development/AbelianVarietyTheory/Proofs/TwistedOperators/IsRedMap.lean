import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.StepVec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

open Classical in

def gLoc {a b : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ a) (PP : Formalism.L2.DIV.Pl D.host.E)
    (H : Subgroup (GL (Fin L.r) (Formalism.L2.DIV.kP PP))) (c : H →* ℂˣ) (χ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (y : Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) : ℂ :=
  if h : LowZero a y ∧ ∃ g : GL (Fin a) (Formalism.L2.DIV.kP PP),
      ((g : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a y ∧
      g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t) ∧ Formalism.L2.DIV.upperLeftBlock L.hr g ∈ H then
    ((c ⟨Formalism.L2.DIV.upperLeftBlock L.hr h.2.choose, h.2.choose_spec.2.2⟩ : ℂˣ) : ℂ) *
      (∏ i ∈ Finset.range L.s,
        ((L.cg (i + 1) PP (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf L.r L.t) (i + 1) h.2.choose) : ℂˣ) : ℂ)) *
      (((χ (Matrix.GeneralLinearGroup.det h.2.choose)) : ℂˣ) : ℂ)⁻¹
  else 0

open Classical in

def qLoc {a b : ℕ} (r : ℕ) (PP : Formalism.L2.DIV.Pl D.host.E) (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (y : Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) : ℂ :=
  if h : LowZero r y ∧ IsUnit (topL r y).det then ((ξ h.2.unit : ℂˣ) : ℂ) else 0

def IsRedMap {v : FinPl D} (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E)
    (r : v.adicCompletionIntegers D.host.F →+* Formalism.L2.DIV.kP PP) : Prop :=
  Function.Surjective r ∧ (∀ a : v.adicCompletionIntegers D.host.F, r a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1) ∧
    (∀ (a : Fv D.host.F v) (b : Formalism.L2.DIV.kP PP), RedRel φ PP a b ↔ ∃ h : a ∈ v.adicCompletionIntegers D.host.F, r ⟨a, h⟩ = b) ∧
    ∀ (N : EAf D) (hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
      ∃ h : rdE φ N ∈ v.adicCompletionIntegers D.host.F, r ⟨rdE φ N, h⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨N, hN⟩

open Classical in

def viaRed {v : FinPl D} {k : Type} [CommRing k] {a b : ℕ} (r : v.adicCompletionIntegers D.host.F →+* k)
    (ω : Matrix (Fin b) (Fin a) k → ℂ) (Y : Matrix (Fin b) (Fin a) (Fv D.host.F v)) : ℂ :=
  if h : ∀ i j, Y i j ∈ v.adicCompletionIntegers D.host.F then ω (Matrix.of fun i j => r ⟨Y i j, h i j⟩) else 0

open Classical in

def locFn (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (PP : Formalism.L2.DIV.Pl D.host.E) (ω : Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.DIV.kP PP) → ℂ) : WO S T → ℂ :=
  fun x => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then ω (redM PP (frMapO S T βS βT x)) else 0

end GlobalTheory.StepVec

end
