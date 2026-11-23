import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountNonIntegrality.RingInverseMulEquiv

noncomputable section

namespace PI.CntNotIntW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def TrDual : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (p : PlF D), ∀ c ∈ 𝒪[(D.s.atP p).Fp],
      haveI : Fact (Loc.resChar p).Prime := (D.s.atP p).ellPrime
      ‖Algebra.trace ℚ_[Loc.resChar p] (D.s.atP p).Fp (c * (δ p)⁻¹)‖ ≤ 1

def DualApprox : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) [Fact (Loc.resChar p).Prime]
    (Fp : Type) [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp] [IsNonarchimedeanLocalField Fp]
    [Algebra ℚ_[Loc.resChar p] Fp], Continuous (algebraMap ℚ_[Loc.resChar p] Fp) →
    FiniteDimensional ℚ_[Loc.resChar p] Fp → ∀ (ι : K →+* Fp), DenseRange ι →
    (∀ x y : K, (ι x ≤ᵥ ι y) ↔ p.valuation K x ≤ p.valuation K y) →
    ∀ z : Fp, (∀ c ∈ 𝒪[Fp], ‖Algebra.trace ℚ_[Loc.resChar p] Fp (c * z)‖ ≤ 1) →
    ∀ k : ℕ, ∃ t : K, (∀ a : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (t * a) = n) ∧
      ∃ μ ∈ 𝒪[Fp], ι t = z + ((Loc.resChar p : ℕ) : Fp) ^ k * μ

def LocDiff : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (p : PlF D), ∃ t : D.host.F,
      (∀ a : 𝓞 D.host.F, ∃ n : ℤ, Algebra.trace ℚ D.host.F (t * a) = n) ∧
      δ p * (D.s.atP p).ιF t ≠ 0 ∧ δ p * (D.s.atP p).ιF t ∈ 𝒪[(D.s.atP p).Fp] ∧ (δ p * (D.s.atP p).ιF t)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]

def PowSmall : Prop :=
  ∀ (Fp : Type) [Field Fp] [ValuativeRel Fp] [TopologicalSpace Fp] [IsNonarchimedeanLocalField Fp] (x y : Fp),
    valuation Fp y < 1 → ∃ k : ℕ, valuation Fp (y ^ k * x) < 1

def DualPow : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (t : D.host.F), (∀ a : 𝓞 D.host.F, ∃ n : ℤ, Algebra.trace ℚ D.host.F (t * a) = n) →
    ∀ m : ℕ, ((t : D.host.E) ^ m) ∈
      ((ddS D) ^ (-(m : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)

end PI.CntNotIntW
