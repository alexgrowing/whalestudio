import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.StrictlyAntitoneWeights.StepEpsFrob

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TV NumberField IsDedekindDomain Polynomial

namespace Formalism.MainNotions.V.Pf.V3.P4

variable {D : D7} (V : VData D)

def ent (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) (g1 : GQ)
    (g : K.fixingSubgroup) (i k : Fin 3) : V.S3 l e χ K g1 :=
  ((V.unitaryGaloisRepresentation l e χ K g1 g : GL (Fin 3) (V.S3 l e χ K g1)) : Matrix (Fin 3) (Fin 3) (V.S3 l e χ K g1)) i k

def psi3 (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (i : Fin 3) (g : GQ) : V.Ol l :=
  ![V.psi l e χ g, 1, V.psi l e χ g⁻¹] i

variable {V} in

def rhoM {l : ℕ} [Fact l.Prime] {e : ℕ} {χ : Chi D} {K : IntermediateField ℚ QbarQ} {g1 : GQ}
    (ξ : V.S3 l e χ K g1 →+* QbarL l) (g : K.fixingSubgroup) : Matrix (Fin 3) (Fin 3) (QbarL l) :=
  ((V.rho3 ξ g : GL (Fin 3) (QbarL l)) : Matrix (Fin 3) (Fin 3) (QbarL l))

abbrev HL (l : ℕ) [Fact l.Prime] (χ : Chi D) (K : IntermediateField ℚ QbarQ) : Subgroup GQ :=
  HcrSub l (V.aOf l χ) (V.Dq l ⊓ K.fixingSubgroup)

variable {V} in

abbrev rhoL {l : ℕ} [Fact l.Prime] {e : ℕ} {χ : Chi D} {K : IntermediateField ℚ QbarQ} {g1 : GQ}
    (ξ : V.S3 l e χ K g1 →+* QbarL l) : HL V l χ K →* GL (Fin 3) (QbarL l) :=
  (V.rho3 ξ).comp (Subgroup.inclusion (inf_le_left.trans inf_le_right))

def AllDat (φ : ∀ (l : ℕ) [Fact l.Prime] (_e : ℕ) (_χ : Chi D) (_K : IntermediateField ℚ QbarQ) (_g1 : GQ), Prop) :
    Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (g1 : GQ),
    Dat V l e χ K g1 → φ l e χ K g1

def AllPt (φ : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) (g1 : GQ),
    (V.S3 l e χ K g1 →+* QbarL l) → Prop) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (g1 : GQ),
    Dat V l e χ K g1 → ∀ ξ : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ → φ l e χ K g1 ξ

def AllPtW (φ : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) (g1 : GQ),
    (V.S3 l e χ K g1 →+* QbarL l) → Prop) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (g1 : GQ),
    Dat V l e χ K g1 → LW V l e χ K g1 → ∀ ξ : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ → φ l e χ K g1 ξ

def GenNeg : Prop := AllDat V fun l _ e χ K g1 =>
  ∀ j : ℤ, j < 0 → ∀ x ∈ V.S3gr l e χ K g1 j,
    x ∈ Ideal.span {y | ∃ (g : K.fixingSubgroup) (i k : Fin 3), k < i ∧ y = ent V l e χ K g1 g i k}

def GenPos : Prop := AllDat V fun l _ e χ K g1 =>
  ∀ j : ℤ, 0 < j → ∀ x ∈ V.S3gr l e χ K g1 j,
    x ∈ Ideal.span {y | ∃ (g : K.fixingSubgroup) (i k : Fin 3), i < k ∧ y = ent V l e χ K g1 g i k}

def GenAll : Prop := AllDat V fun l _ e χ K g1 =>
  Algebra.adjoin (V.Ol l) {y | ∃ (g : K.fixingSubgroup) (i k : Fin 3), y = ent V l e χ K g1 g i k} = ⊤

def GradedDegreeZeroIsLocal : Prop := AllDat V fun l _ e χ K g1 =>
  ∀ x ∈ V.S3gr l e χ K g1 0, V.S3emb l e χ K g1 x ∉ IsLocalRing.maximalIdeal (V.S3hat l e χ K g1) →
    ∃ y ∈ V.S3gr l e χ K g1 0, x * y = 1

def PtInt : Prop := AllPt V fun l _ e χ K g1 ξ => ∀ x ∈ V.S3gr l e χ K g1 0, ‖ξ x‖ ≤ 1

def PtLocal : Prop := AllPt V fun l _ e χ K g1 ξ =>
  ∀ x ∈ V.S3gr l e χ K g1 0, V.S3emb l e χ K g1 x ∈ IsLocalRing.maximalIdeal (V.S3hat l e χ K g1) → ‖ξ x‖ < 1

def PtFin : Prop := AllPt V fun l _ _ _ _ _ ξ =>
  ∃ E' : IntermediateField ℚ_[l] (QbarL l), FiniteDimensional ℚ_[l] E' ∧ ∀ x, ξ x ∈ E'

def PtHat : Prop := AllPt V fun l _ e χ K g1 ξ =>
  ∃ (t : (QbarL l)ˣ) (φ : V.S3hat l e χ K g1 →+* QbarL l),
    φ.comp (algebraMap (V.Ol l) (V.S3hat l e χ K g1)) = V.jO l ∧ (∀ y, ‖φ y‖ ≤ 1) ∧
    (∀ y ∈ IsLocalRing.maximalIdeal (V.S3hat l e χ K g1), ‖φ y‖ < 1) ∧
    (∃ E' : IntermediateField ℚ_[l] (QbarL l), FiniteDimensional ℚ_[l] E' ∧ ∀ y, φ y ∈ E') ∧
    ∀ (j : ℤ), ∀ x ∈ V.S3gr l e χ K g1 j, φ (V.S3emb l e χ K g1 x) = (t : QbarL l) ^ j * ξ x

def PtCont : Prop := AllPt V fun _ _ _ _ _ _ ξ => Continuous (V.rho3 ξ)

def PtDual : Prop := AllPt V fun l _ _ _ K _ ξ =>
  ∀ g h : K.fixingSubgroup, (h : GQ) = V.cc * (g : GQ)⁻¹ * V.cc →
    rhoM ξ h = Jad3 (QbarL l) * (rhoM ξ g).transpose * Jad3 (QbarL l)

def PtZ : Prop := AllPt V fun l _ _ _ K g1 ξ =>
  ∀ g h : K.fixingSubgroup, (g : GQ) = g1 → (h : GQ) = V.cc * g1⁻¹ * V.cc →
    ∃ z : QbarL l, ‖z‖ = 1 ∧ rhoM ξ g - rhoM ξ h = Matrix.diagonal ![z, 0, -z]

def RingUq : Prop := AllDat V fun l _ e χ K g1 =>
  ∀ A : ValuationSubring QbarQ, Formalism.MainNotions.V.Lang.IsFinitePlace ℚ A → ¬ Formalism.MainNotions.V.Lang.IsPlaceAbove ℚ A l →
    ∀ σ : K.fixingSubgroup, (σ : GQ) ∈ Formalism.MainNotions.V.Lang.Ine (F := ℚ) A → V.psiBar l e χ σ = 1 →
    V.unitaryGaloisRepresentation l e χ K g1 σ = 1

def PtCrys : Prop := AllPt V fun l _ e χ K _ ξ =>
  V.Crys l 3 (HL V l χ K) (V.plc l) (rhoL ξ) ∧
  ∀ τ, Formalism.MainNotions.UnitaryThreeHeightBounds.IndPl V l (HL V l χ K) τ → V.HT l 3 (HL V l χ K) (V.plc l) (rhoL ξ) τ = ({-(e : ℤ), 0, (e : ℤ)} : Multiset ℤ)

def PtChar : Prop := AllPt V fun l _ e χ K _ ξ =>
  ∀ s : K.fixingSubgroup, (s : GQ) ∈ V.Iq l →
    (rhoM ξ s).charpoly = ∏ i : Fin 3, (X - C (V.jO l (psi3 V l e χ i s)))

def PtTriple : Prop := AllPt V fun l _ e χ K _ ξ =>
  ∀ s : Fin 3 → K.fixingSubgroup, (∀ i, (s i : GQ) ∈ V.Iq l) →
    (rhoM ξ (s 0) - Matrix.scalar (Fin 3) (V.jO l (psi3 V l e χ 0 (s 0)))) *
      (rhoM ξ (s 1) - Matrix.scalar (Fin 3) (V.jO l (psi3 V l e χ 1 (s 1)))) *
      (rhoM ξ (s 2) - Matrix.scalar (Fin 3) (V.jO l (psi3 V l e χ 2 (s 2)))) = 0

def PtDiag : Prop := AllPt V fun l _ e χ K _ ξ =>
  ∀ (g : K.fixingSubgroup) (i : Fin 3), ‖rhoM ξ g i i - V.jO l (psi3 V l e χ i g)‖ < 1

def PtDet : Prop := AllPt V fun l _ e χ K g1 ξ =>
  ∀ ξ' : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ' → V.rho3 ξ = V.rho3 ξ' → ξ = ξ'

def PtNeg : Prop := AllPt V fun l _ e χ K g1 ξ =>
  (∀ (g : K.fixingSubgroup) (i k : Fin 3), k < i → rhoM ξ g i k = 0) →
    ∀ j : ℤ, j < 0 → ∀ x ∈ V.S3gr l e χ K g1 j, ξ x = 0

def PtPos : Prop := AllPt V fun l _ e χ K g1 ξ =>
  (∀ (g : K.fixingSubgroup) (i k : Fin 3), i < k → rhoM ξ g i k = 0) →
    ∀ j : ℤ, 0 < j → ∀ x ∈ V.S3gr l e χ K g1 j, ξ x = 0

structure Pts : Prop where
  int : PtInt V
  loc : PtLocal V
  fin : PtFin V
  hat : PtHat V
  cont : PtCont V
  dual : PtDual V
  z : PtZ V
  uq : RingUq V
  crys : PtCrys V
  char : PtChar V
  triple : PtTriple V
  diag : PtDiag V
  det : PtDet V
  neg : PtNeg V
  pos : PtPos V

end Formalism.MainNotions.V.Pf.V3.P4
