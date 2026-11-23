import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.StrictlyAntitoneWeights.ConstantCoeffAtReducedPoint
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.StrictlyAntitoneWeights.HatTripleRepresentations.GradedDegreeZeroIsLocal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TV NumberField IsDedekindDomain Polynomial

namespace Formalism.MainNotions.V.Pf.V3.P4

variable {D : D7} (V : VData D)

variable {V} in

def rhoHat {l : ℕ} [Fact l.Prime] {e : ℕ} {χ : Chi D} {K : IntermediateField ℚ QbarQ} {g1 : GQ}
    (φ : V.S3hat l e χ K g1 →+* QbarL l) : K.fixingSubgroup →* GL (Fin 3) (QbarL l) :=
  (Units.map (φ.mapMatrix : Matrix (Fin 3) (Fin 3) (V.S3hat l e χ K g1) →+*
    Matrix (Fin 3) (Fin 3) (QbarL l)).toMonoidHom).comp (V.rS3hat l e χ K g1)

def hatM (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) (g1 : GQ)
    (g : K.fixingSubgroup) : Matrix (Fin 3) (Fin 3) (V.S3hat l e χ K g1) :=
  ((V.rS3hat l e χ K g1 g : GL (Fin 3) (V.S3hat l e χ K g1)) : Matrix (Fin 3) (Fin 3) (V.S3hat l e χ K g1))

def IsHatPt {l : ℕ} [Fact l.Prime] {e : ℕ} {χ : Chi D} {K : IntermediateField ℚ QbarQ} {g1 : GQ}
    (φ : V.S3hat l e χ K g1 →+* QbarL l) : Prop :=
  φ.comp (algebraMap (V.Ol l) (V.S3hat l e χ K g1)) = V.jO l ∧ (∀ y, ‖φ y‖ ≤ 1) ∧
    (∀ y ∈ IsLocalRing.maximalIdeal (V.S3hat l e χ K g1), ‖φ y‖ < 1) ∧
    ∃ E' : IntermediateField ℚ_[l] (QbarL l), FiniteDimensional ℚ_[l] E' ∧ ∀ y, φ y ∈ E'

def HatCrys : Prop := AllDat V fun l _ e χ K g1 =>
  ∀ φ : V.S3hat l e χ K g1 →+* QbarL l, IsHatPt V φ →
    V.Crys l 3 (HL V l χ K) (V.plc l) ((rhoHat φ).comp (Subgroup.inclusion (inf_le_left.trans inf_le_right))) ∧
    ∀ τ, Formalism.MainNotions.UnitaryThreeHeightBounds.IndPl V l (HL V l χ K) τ →
      V.HT l 3 (HL V l χ K) (V.plc l) ((rhoHat φ).comp (Subgroup.inclusion (inf_le_left.trans inf_le_right))) τ =
        ({-(e : ℤ), 0, (e : ℤ)} : Multiset ℤ)

def HatChar : Prop := AllDat V fun l _ e χ K g1 =>
  ∀ s : K.fixingSubgroup, (s : GQ) ∈ V.Iq l →
    (hatM V l e χ K g1 s).charpoly =
      ∏ i : Fin 3, (X - C (algebraMap (V.Ol l) (V.S3hat l e χ K g1) (psi3 V l e χ i s)))

def HatTriple : Prop := AllDat V fun l _ e χ K g1 =>
  ∀ s : Fin 3 → K.fixingSubgroup, (∀ i, (s i : GQ) ∈ V.Iq l) →
    (hatM V l e χ K g1 (s 0) - Matrix.scalar (Fin 3) (algebraMap (V.Ol l) (V.S3hat l e χ K g1) (psi3 V l e χ 0 (s 0)))) *
      (hatM V l e χ K g1 (s 1) - Matrix.scalar (Fin 3) (algebraMap (V.Ol l) (V.S3hat l e χ K g1) (psi3 V l e χ 1 (s 1)))) *
      (hatM V l e χ K g1 (s 2) - Matrix.scalar (Fin 3) (algebraMap (V.Ol l) (V.S3hat l e χ K g1) (psi3 V l e χ 2 (s 2)))) = 0

def B_GenNeg : Prop := Giv V → StepPresT V → GenNeg V
def B_GenPos : Prop := Giv V → StepPresT V → GenPos V
def B_GenAll : Prop := Giv V → StepPresT V → GenAll V
def B_S0Loc : Prop := Giv V → StepPresT V → GradedDegreeZeroIsLocal V
def B_PtFin : Prop := Giv V → StepPresT V → PtFin V

def B_PtHat : Prop := Giv V → StepPresT V → PtInt V → PtLocal V → PtFin V → PtHat V

def B_HatCrys : Prop := Giv V → StepPresT V → HatCrys V
def B_HatChar : Prop := Giv V → StepPresT V → HatChar V
def B_HatTriple : Prop := Giv V → StepPresT V → HatTriple V

def F_NormInt : Prop := ∀ (l : ℕ) [Fact l.Prime] (z : QbarL l), IsIntegral ℤ_[l] z ↔ ‖z‖ ≤ 1

def F_NormO : Prop := ∀ (l : ℕ) [Fact l.Prime] (x : V.Ol l),
  ‖V.jO l x‖ ≤ 1 ∧ (x ∈ IsLocalRing.maximalIdeal (V.Ol l) ↔ ‖V.jO l x‖ < 1)

def F_CcSq : Prop := V.cc * V.cc = 1

def F_GK : Prop := ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K], Module.finrank ℚ K = 2 →
  (∀ g ∈ K.fixingSubgroup, ∀ x : GQ, x * g * x⁻¹ ∈ K.fixingSubgroup) ∧
  ∀ c : GQ, c ∉ K.fixingSubgroup → ∀ g : GQ, g ∈ K.fixingSubgroup ∨ g * c ∈ K.fixingSubgroup

def F_FinPlc : Prop := ∀ A : ValuationSubring QbarQ, Formalism.MainNotions.V.Lang.IsFinitePlace ℚ A →
  ∃ q : ℕ, q.Prime ∧ Formalism.MainNotions.V.Lang.IsPlaceAbove ℚ A q

def F_PlcConj : Prop := ∀ (q : ℕ), q.Prime → ∀ A : ValuationSubring QbarQ, Formalism.MainNotions.V.Lang.IsPlaceAbove ℚ A q →
  ∃ x : GQ, (∀ σ : GQ, σ ∈ Formalism.MainNotions.V.Lang.Ine (F := ℚ) A ↔ x⁻¹ * σ * x ∈ V.Iq q) ∧
    ∀ σ : GQ, σ ∈ Formalism.MainNotions.V.Lang.Dec (F := ℚ) A ↔ x⁻¹ * σ * x ∈ V.Dq q

def F_PsiMul : Prop := ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (e : ℕ) (χ : Chi D) (g h : GQ),
  V.psi l e χ (g * h) = V.psi l e χ g * V.psi l e χ h ∧ V.psi l e χ 1 = 1

def F_LocOpenHL : Prop := ∀ (l : ℕ) [Fact l.Prime] (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K],
  Formalism.MainNotions.UnitaryThreeHeightBounds.LocOpen V l (HL V l χ K)

def S_PtInt : Prop := F_NormInt → PtInt V

def S_PtLocal : Prop := F_NormInt → GradedDegreeZeroIsLocal V → PtInt V → PtLocal V

def S_PtCont : Prop := PtHat V → PtCont V

def S_PtDual : Prop := PtDual V

def S_PtDiag : Prop := PtLocal V → PtDiag V

def S_PtZ : Prop := F_NormO V → F_PsiMul V → PtDual V → PtDiag V → PtZ V

def RingUq0 : Prop := AllDat V fun l _ e χ K g1 =>
  ∀ q : ℕ, q.Prime → q ≠ l → ∀ σ : K.fixingSubgroup, (σ : GQ) ∈ V.Iq q → V.psiBar l e χ σ = 1 →
    V.unitaryGaloisRepresentation l e χ K g1 σ = 1

def S_RingUq0 : Prop := F_PsiMul V → RingUq0 V

def S_RingUq : Prop := F_CcSq V → F_GK → F_FinPlc → F_PlcConj V → F_PsiMul V → RingUq0 V → RingUq V

def S_PtCrys : Prop := Formalism.MainNotions.UnitaryThreeHeightBounds.FonIso V → F_LocOpenHL V → PtHat V → HatCrys V → PtCrys V

def S_PtChar : Prop := HatChar V → PtChar V
def S_PtTriple : Prop := HatTriple V → PtTriple V

def S_PtDet : Prop := GenAll V → PtDet V

def S_PtNeg : Prop := GenNeg V → PtNeg V
def S_PtPos : Prop := GenPos V → PtPos V

structure BridgeA : Prop where
  genNeg : B_GenNeg V
  genPos : B_GenPos V
  genAll : B_GenAll V
  gradedDegreeZeroLocal : B_S0Loc V
  ptFin : B_PtFin V
  ptHat : B_PtHat V
  hatCrys : B_HatCrys V
  hatChar : B_HatChar V
  hatTriple : B_HatTriple V

structure FieldA : Prop where
  normInt : F_NormInt
  normO : F_NormO V
  ccSq : F_CcSq V
  gk : F_GK
  finPlc : F_FinPlc
  plcConj : F_PlcConj V
  psiMul : F_PsiMul V
  locOpen : F_LocOpenHL V

structure StepsA : Prop where
  ptInt : S_PtInt V
  ptLocal : S_PtLocal V
  ptCont : S_PtCont V
  ptDual : S_PtDual V
  ptDiag : S_PtDiag V
  ptZ : S_PtZ V
  ringUq0 : S_RingUq0 V
  ringUq : S_RingUq V
  ptCrys : S_PtCrys V
  ptChar : S_PtChar V
  ptTriple : S_PtTriple V
  ptDet : S_PtDet V
  ptNeg : S_PtNeg V
  ptPos : S_PtPos V

end Formalism.MainNotions.V.Pf.V3.P4
