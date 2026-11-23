import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.StrictlyAntitoneWeights.GaussianCaseFreeExponents

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TV NumberField IsDedekindDomain Polynomial

namespace Formalism.MainNotions.V.Pf.V3

variable {D : D7} (V : VData D)

abbrev epsK (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ QbarQ) : K.fixingSubgroup →* (QbarL l)ˣ :=
  (epsL l).comp K.fixingSubgroup.subtype

def StepEpsFrob : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (p : ℕ), p.Prime → p ≠ l →
    ∀ Fr : FrobAt K p, ((epsL l (Fr.φ : GQ) : (QbarL l)ˣ) : QbarL l) = ((Fr.q : ℕ) : QbarL l)⁻¹

def StepFrobQ : Prop :=
  ∀ (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K] (p : ℕ), p.Prime → ∀ Fr : FrobAt K p,
    Formalism.ConjugateSelfDual.IsPlaceOver (F := ℚ) Fr.A Fr.vp ∧ Formalism.ConjugateSelfDual.normV Fr.vp = p ∧
    ∃ σp : GQ, Formalism.ConjugateSelfDual.IsFrob (F := ℚ) Fr.A p σp ∧ (σp ^ Fr.h)⁻¹ * (Fr.σ : GQ) ∈ Formalism.ConjugateSelfDual.Inertia (F := ℚ) Fr.A

def StepShape : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ ξ : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ → Both3 ξ →
    Formalism.ConjugateSelfDual.Irred (VData.toRecRep (V.rho3 ξ)) ∨
      ∃ ρ₂ : K.fixingSubgroup →* GL (Fin 2) (QbarL l), Formalism.ConjugateSelfDual.Irred (VData.toRecRep ρ₂) ∧
        IsDirSum (m := 2) (k := 1) (V.rho3 ξ) ρ₂ (charRep 1)

def StepCont : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ ξ : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ → Continuous (V.rho3 ξ)

def StepPtLoc : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ ξ : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ →
    (∀ q : ℕ, q.Prime → q ≠ l → ∀ σ : K.fixingSubgroup, (σ : GQ) ∈ V.Iq q →
      (σ : GQ) ∈ Formalism.MainNotions.UnitaryThreeHeightBounds.FixMu (condV D) → V.rho3 ξ σ = 1) ∧
    V.Crys l 3 (HcrSub l (V.aOf l χ) (V.Dq l ⊓ K.fixingSubgroup)) (V.plc l)
      ((V.rho3 ξ).comp (Subgroup.inclusion (inf_le_left.trans inf_le_right))) ∧
    ∀ τ, Formalism.MainNotions.UnitaryThreeHeightBounds.IndPl V l (HcrSub l (V.aOf l χ) (V.Dq l ⊓ K.fixingSubgroup)) τ →
      V.HT l 3 (HcrSub l (V.aOf l χ) (V.Dq l ⊓ K.fixingSubgroup)) (V.plc l)
        ((V.rho3 ξ).comp (Subgroup.inclusion (inf_le_left.trans inf_le_right))) τ =
          ({-(e : ℤ), 0, (e : ℤ)} : Multiset ℤ)

def StepPtOrd : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ ξ : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ →
    IsCSDOne (VData.toRecRep (V.rho3 ξ)) ∧
      OrdFixAbove (VData.toRecRep (V.rho3 ξ)) ![(e : ℤ), 0, -(e : ℤ)] (condV D)

def StepW : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ ξ : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ →
    ∀ ρ₂ : K.fixingSubgroup →* GL (Fin 2) (QbarL l), Formalism.ConjugateSelfDual.Irred (VData.toRecRep ρ₂) →
    IsDirSum (m := 2) (k := 1) (V.rho3 ξ) ρ₂ (charRep 1) →
    ∃ W : GQ →* GL (Fin 2) (QbarL l), Continuous W ∧ IsIsoRep (W.comp K.fixingSubgroup.subtype) ρ₂ ∧
      Formalism.ConjugateSelfDual.IsOdd W ∧ Formalism.ConjugateSelfDual.Irred W ∧ Formalism.ConjugateSelfDual.AlmostUnram W ∧ V.DeRham l 2 ⊤ (V.plc l) (onTop W) ∧
      (∀ τ, V.HT l 2 ⊤ (V.plc l) (onTop W) τ = ({-(e : ℤ), (e : ℤ)} : Multiset ℤ)) ∧
      (∃ a b : GQ →* (QbarL l)ˣ, (∀ g : GQ,
          ‖(W g : Matrix (Fin 2) (Fin 2) (QbarL l)).trace - ((a g : QbarL l) + (b g : QbarL l))‖ < 1 ∧
          ‖(W g : Matrix (Fin 2) (Fin 2) (QbarL l)).det - (a g : QbarL l) * (b g : QbarL l)‖ < 1) ∧
        (l = 3 → ∃ g ∈ V.Dq 3, ¬ ‖((a g : QbarL l) / (b g : QbarL l)) - (epsL l g : QbarL l)‖ < 1)) ∧
      (∀ q : ℕ, q.Prime → q ≠ l → ∀ σ : GQ, σ ∈ V.Iq q → σ ∈ Formalism.MainNotions.UnitaryThreeHeightBounds.FixMu (condV D * dK K) → W σ = 1) ∧
      V.Iq l ≤ K.fixingSubgroup ∧
      V.Crys l 2 (HcrSub l (V.aOf l χ) (V.Dq l ⊓ K.fixingSubgroup)) (V.plc l)
        (W.comp (HcrSub l (V.aOf l χ) (V.Dq l ⊓ K.fixingSubgroup)).subtype) ∧
      (LW V l e χ K g1 → ∃ π : (V.spec ℚ 2).Rep, IsWeight2 V π (2 * e + 1) ∧ IsVg V π (twistRep W ((epsL l) ^ e)⁻¹))

def StepOrbIso : Prop :=
  Giv V → ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ ξ ξ' : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ → V.IsPt3 ξ' → Both3 ξ →
    Both3 ξ' → IsIsoRep (V.rho3 ξ) (V.rho3 ξ') → SameOrbit3 ξ ξ'

def Lab3 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ p : ℕ, p.Prime → ¬ p ∣ 30 * l * condV D * dK K → ∀ Fr : FrobAt K p,
    ∀ ξ : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ → Formalism.ConjugateSelfDual.Irred (VData.toRecRep (V.rho3 ξ)) →
    ∃ π ∈ Sig3G V K e,
      V.IsRi π (VData.toRecRep (twistRep (V.rho3 ξ) (epsK l K)⁻¹)) ∧
      V.iotaC l ((V.rho3 ξ Fr.φ : GL (Fin 3) (QbarL l)) : Matrix (Fin 3) (Fin 3) (QbarL l)).trace = t3 V Fr π

def Lab2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → LW V l e χ K g1 → ∀ p : ℕ, p.Prime → ¬ p ∣ 30 * l * condV D * dK K → ∀ Fr : FrobAt K p,
    ∀ ξ : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ →
    ∀ ρ₂ : K.fixingSubgroup →* GL (Fin 2) (QbarL l), Formalism.ConjugateSelfDual.Irred (VData.toRecRep ρ₂) →
    IsDirSum (m := 2) (k := 1) (V.rho3 ξ) ρ₂ (charRep 1) →
    ∃ π ∈ Sig2G V (condV D * dK K) e, ∃ W : GQ →* GL (Fin 2) (QbarL l), Continuous W ∧ Formalism.ConjugateSelfDual.Irred W ∧
      IsIsoRep (W.comp K.fixingSubgroup.subtype) ρ₂ ∧ V.IsRi π (twistRep W ((epsL l) ^ e)⁻¹) ∧
      V.iotaC l ((V.rho3 ξ Fr.φ : GL (Fin 3) (QbarL l)) : Matrix (Fin 3) (Fin 3) (QbarL l)).trace = t2 V e Fr π

def LabInj3 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ ξ ξ' : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ → V.IsPt3 ξ' → Both3 ξ →
    Both3 ξ' → Formalism.ConjugateSelfDual.Irred (VData.toRecRep (V.rho3 ξ)) → Formalism.ConjugateSelfDual.Irred (VData.toRecRep (V.rho3 ξ')) →
    ∀ π : (V.spec K 3).Rep, V.IsRi π (VData.toRecRep (twistRep (V.rho3 ξ) (epsK l K)⁻¹)) →
    V.IsRi π (VData.toRecRep (twistRep (V.rho3 ξ') (epsK l K)⁻¹)) → SameOrbit3 ξ ξ'

def LabInj2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : Chi D) (K : IntermediateField ℚ QbarQ) [FiniteDimensional ℚ K]
    (g1 : GQ), Dat V l e χ K g1 → ∀ ξ ξ' : V.S3 l e χ K g1 →+* QbarL l, V.IsPt3 ξ → V.IsPt3 ξ' → Both3 ξ →
    Both3 ξ' → ∀ ρ₂ ρ₂' : K.fixingSubgroup →* GL (Fin 2) (QbarL l),
    IsDirSum (m := 2) (k := 1) (V.rho3 ξ) ρ₂ (charRep 1) → IsDirSum (m := 2) (k := 1) (V.rho3 ξ') ρ₂' (charRep 1) →
    ∀ W W' : GQ →* GL (Fin 2) (QbarL l), Continuous W → Continuous W' → Formalism.ConjugateSelfDual.Irred W → Formalism.ConjugateSelfDual.Irred W' →
    IsIsoRep (W.comp K.fixingSubgroup.subtype) ρ₂ → IsIsoRep (W'.comp K.fixingSubgroup.subtype) ρ₂' →
    ∀ π : (V.spec ℚ 2).Rep, V.IsRi π (twistRep W ((epsL l) ^ e)⁻¹) → V.IsRi π (twistRep W' ((epsL l) ^ e)⁻¹) →
    SameOrbit3 ξ ξ'

end Formalism.MainNotions.V.Pf.V3
