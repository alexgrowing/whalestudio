import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.IsAutCsdA

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.W UpperTheory.V.Ws.Eb
namespace UpperTheory.V.Th
section Abstract
variable {l : ℕ} [Fact l.Prime] (F : GFrame l) {K : Type} [Field K] {n : ℕ}
end Abstract
section U
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V.frame c.O n} {B : UniversalOrdinaryDeterminantRing r}
structure AutomorphicPointGalois (ι : Qbar l ≃+* ℂ) (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) : Prop where
  cont : Continuous ρ
  rep : x.IsRep (ρ.comp V.pr)
  arith : ∃ h, x.Arith h
  aut : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (ρ.comp V.pr)
  unr0 : ∀ g ∈ V.frame.I0, ρ g = 1
  flag : ∀ v : V.frame.Vl, HasFlag (ρ.comp (V.frame.φ v)) (x.psi v)
structure AutomorphicPointLocallyGeneric (ι : Qbar l ≃+* ℂ) (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) : Prop extends toAPt : _root_.UpperTheory.V.Th.AutomorphicPointGalois ι x ρ where
  free : Free V.frame fun v => x.psi v
  irr : TypeI V.frame ρ
  n3 : N3 V.frame ρ
end U
def DenseThresholdMainCase : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → (¬ ∃ ζ : L, IsPrimitiveRoot ζ l) →
    ∀ (c : Coef l), Large L c → ∀ (n : ℕ), 2 ≤ n → n ≤ 4 → ∀ (r : Resid V.frame c.O n), r.V0ok → ∀ (B : UniversalOrdinaryDeterminantRing r) (ι : Qbar l ≃+* ℂ)
      (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)), _root_.UpperTheory.V.Th.AutomorphicPointLocallyGeneric ι x ρ → OrdZero r ρ fun v => x.psi v
def AdjointLiftingTheorem : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → (¬ ∃ ζ : L, IsPrimitiveRoot ζ l) →
    ∀ (c : Coef l), Large L c → ∀ (n : ℕ), 2 ≤ n → n ≤ 4 → ∀ (r : Resid V.frame c.O n), r.V0ok → ∀ (B : UniversalOrdinaryDeterminantRing r) (ι : Qbar l ≃+* ℂ)
      (x : B.Pt) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)), _root_.UpperTheory.V.Th.AutomorphicPointLocallyGeneric ι x ρ → Par x → AdZero V ρ
end UpperTheory.V.Th
end
end
