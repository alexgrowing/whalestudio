import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.ClassGroupAction
import GroundTheory.GlobalFields.ComplexMultiplication.JInvariant
import GroundTheory.GlobalFields.ComplexMultiplication.DifferentialConstantField
import GroundTheory.GlobalFields.AnalyticClassNumber.Quadratic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic GroundTheory.Arith.Abelian Filter Topology
open scoped nonZeroDivisors Real ModularForm UpperHalfPlane

noncomputable section

def eisensteinSum (Λ : Submodule ℤ ℂ) (n : ℕ) : ℂ := ∑' l : Λ, ((l : ℂ) ^ n)⁻¹

def latticeG₂ (Λ : Submodule ℤ ℂ) : ℂ := 60 * eisensteinSum Λ 4

def latticeG₃ (Λ : Submodule ℤ ℂ) : ℂ := 140 * eisensteinSum Λ 6

def latticeDiscr (Λ : Submodule ℤ ℂ) : ℂ := latticeG₂ Λ ^ 3 - 27 * latticeG₃ Λ ^ 2

theorem latticeDiscr_lattice (L : PeriodPair) : latticeDiscr L.lattice = discr L := rfl

def latticeArea (Λ : Submodule ℤ ℂ) : ℝ := ZLattice.covolume Λ

def logPeriod (Λ : Submodule ℤ ℂ) : ℝ :=
  Real.log (latticeArea Λ / π) + (1 / 6) * Real.log ‖latticeDiscr Λ‖

def scaleLattice (c : ℂ) (Λ : Submodule ℤ ℂ) : Submodule ℤ ℂ := Λ.map (LinearMap.mulLeft ℤ c)

def conjLattice (Λ : Submodule ℤ ℂ) : Submodule ℤ ℂ :=
  Λ.map (starRingEnd ℂ).toIntAlgHom.toLinearMap

def kroneckerSum (τ : ℍ) (s : ℝ) : ℝ :=
  ∑' p : ℤ × ℤ, if p = 0 then 0 else τ.im ^ s / ‖(p.1 : ℂ) * τ + p.2‖ ^ (2 * s)

def epsteinSum (Λ : Submodule ℤ ℂ) (s : ℝ) : ℝ :=
  ∑' l : Λ, if (l : ℂ) = 0 then 0 else latticeArea Λ ^ s / ‖(l : ℂ)‖ ^ (2 * s)

def PhScale.Statement : Prop :=
  ∀ (L : PeriodPair) (c : ℂ), c ≠ 0 → logPeriod (scaleLattice c L.lattice) = logPeriod L.lattice

def PhConj.Statement : Prop :=
  ∀ L : PeriodPair, logPeriod (conjLattice L.lattice) = logPeriod L.lattice

def DeltaEta.Statement : Prop :=
  ∀ τ : ℍ, latticeDiscr (latticeOfTau τ).lattice = ((2 * π : ℝ) : ℂ) ^ 12 * η (τ : ℂ) ^ 24

def PhTau.Statement : Prop :=
  ∀ τ : ℍ, logPeriod (latticeOfTau τ).lattice = Real.log (4 * π * τ.im * ‖η (τ : ℂ)‖ ^ 4)

def KroneckerLimit.Statement : Prop :=
  ∀ τ : ℍ, Tendsto (fun s : ℝ ↦ kroneckerSum τ s - π / (s - 1)) (𝓝[>] 1)
    (𝓝 (2 * π * (Real.eulerMascheroniConstant - Real.log 2 -
      Real.log (Real.sqrt τ.im * ‖η (τ : ℂ)‖ ^ 2))))

def DeltaRatioIntegral.Statement : Prop :=
  ∀ (L L' : PeriodPair) (p : ℕ), p.Prime → L.lattice ≤ L'.lattice →
    L.lattice.toAddSubgroup.relIndex L'.lattice.toAddSubgroup = p →
      IsIntegral (Algebra.adjoin ℤ {(weierstrassCurve L).j})
        (latticeDiscr L'.lattice / latticeDiscr L.lattice)

structure PrimeDiscriminant (K : Type) [Field K] [NumberField K]
    [Algebra.IsQuadraticExtension ℚ K] where

  d : ℕ
  prime : d.Prime
  mod_four : d % 4 = 3
  discr_eq : discr K = -(d : ℤ)

variable {K : Type} [Field K] [NumberField K]

def classRep (C : ClassGroup (𝓞 K)) : (Ideal (𝓞 K))⁰ := (ClassGroup.mk0_surjective C).choose

theorem mk0_classGroupRep (C : ClassGroup (𝓞 K)) : ClassGroup.mk0 (classRep C) = C :=
  (ClassGroup.mk0_surjective C).choose_spec

def classLattice (σ : K →+* ℂ) (C : ClassGroup (𝓞 K)) : Submodule ℤ ℂ :=
  idealLattice σ ((classRep C : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)

def classLogPeriod (σ : K →+* ℂ) (C : ClassGroup (𝓞 K)) : ℝ := logPeriod (classLattice σ C)

def classMean (σ : K →+* ℂ) : ℝ :=
  (classNumber K : ℝ)⁻¹ * ∑ C : ClassGroup (𝓞 K), classLogPeriod σ C

def partialZeta (C : ClassGroup (𝓞 K)) (s : ℝ) : ℝ :=
  ∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C},
    ((Ideal.absNorm (I.1 : Ideal (𝓞 K)) : ℝ) ^ s)⁻¹

def discrRatio (σ : K →+* ℂ) (Λ : Submodule ℤ ℂ) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℂ :=
  latticeDiscr (idealLattice σ ↑𝔞⁻¹ * Λ) / latticeDiscr Λ

def IsPeriodLattice (W : WeierstrassCurve ℂ) (Λ : Submodule ℤ ℂ) : Prop :=
  ∃ (L : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ),
    C • weierstrassCurve L = W ∧ Λ = scaleLattice (C.u : ℂ) L.lattice

structure CMFamily (K : Type) [Field K] [NumberField K] where

  k : Type
  [field : Field k]
  [numberField : NumberField k]
  [algebra : Algebra K k]

  E : WeierstrassCurve k
  [isElliptic : E.IsElliptic]

  normalised : ∀ a : 𝓞 K, a ≠ 0 → ∃ φ : Isogeny E E, invConst φ = algebraMap K k (a : K)

  periodLattice : (k →+* ℂ) → Submodule ℤ ℂ
  isPeriodLattice : ∀ s, IsPeriodLattice (E.map s) (periodLattice s)

attribute [instance] CMFamily.field CMFamily.numberField CMFamily.algebra CMFamily.isElliptic

def embMean (k : Type) [Field k] [NumberField k] (f : (k →+* ℂ) → ℝ) : ℝ :=
  (Fintype.card (k →+* ℂ) : ℝ)⁻¹ * ∑ s : k →+* ℂ, f s

abbrev CMFamily.restrict (F : CMFamily K) (s : F.k →+* ℂ) : K →+* ℂ := s.comp (algebraMap K F.k)

variable [Algebra.IsQuadraticExtension ℚ K]

def ClassLogPeriodWellDefined.Statement (_S : PrimeDiscriminant K) : Prop :=
  ∀ (σ : K →+* ℂ) (C : ClassGroup (𝓞 K)) (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ),
    ClassGroup.mk K 𝔟 = C → logPeriod (idealLattice σ 𝔟) = classLogPeriod σ C

def ClassEpstein.Statement (S : PrimeDiscriminant K) : Prop :=
  ∀ (σ : K →+* ℂ) (C : ClassGroup (𝓞 K)) (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ),
    ClassGroup.mk K 𝔟 = C → ∀ s : ℝ, 1 < s →
      partialZeta C s = (Units.torsionOrder K : ℝ)⁻¹ * (2 / Real.sqrt S.d) ^ s *
        epsteinSum (idealLattice σ 𝔟) s

def ZetaFactor.Statement (_S : PrimeDiscriminant K) : Prop :=
  ∀ s : ℝ, 1 < s →
    dedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction (Quadratic.kronecker K) s ∧
      ∑ C : ClassGroup (𝓞 K), (partialZeta C s : ℂ) = dedekindZeta K s

def ClassMean.Statement (S : PrimeDiscriminant K) : Prop :=
  ∀ σ : K →+* ℂ, ((classMean σ : ℝ) : ℂ) =
    (Real.eulerMascheroniConstant : ℂ) + (Real.log (2 * π / Real.sqrt S.d) : ℂ) -
      deriv (DirichletCharacter.LFunction (Quadratic.kronecker K)) 1 /
        DirichletCharacter.LFunction (Quadratic.kronecker K) 1

def WCocycle.Statement (_S : PrimeDiscriminant K) : Prop :=
  ∀ (σ : K →+* ℂ) (L : PeriodPair), latticeEnd L = cmRing σ →
    ∀ 𝔞 𝔭 : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
      discrRatio σ L.lattice (𝔞 * 𝔭) =
        discrRatio σ L.lattice 𝔞 * discrRatio σ (idealLattice σ ↑𝔞⁻¹ * L.lattice) 𝔭

def JIntegral.Statement (_S : PrimeDiscriminant K) : Prop :=
  ∀ (σ : K →+* ℂ) (L : PeriodPair), latticeEnd L = cmRing σ → IsIntegral ℤ (weierstrassCurve L).j

def WUnitOffPrime.Statement (_S : PrimeDiscriminant K) : Prop :=
  ∀ (σ : K →+* ℂ) (L : PeriodPair), latticeEnd L = cmRing σ →
    ∀ 𝔭 : (Ideal (𝓞 K))⁰, (𝔭 : Ideal (𝓞 K)).IsPrime → (Ideal.absNorm (𝔭 : Ideal (𝓞 K))).Prime →
      IsAlgebraic ℚ (discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔭)) ∧
      ∀ (F : Type) [Field F] [NumberField F] (ι : K →+* F) (τ : F →+* ℂ), τ.comp ι = σ →
        discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔭) ∈ Set.range τ →
          ∃ w : 𝓞 F, τ (w : F) = discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔭) ∧
            ∀ Q : Ideal (𝓞 F), Q.IsMaximal →
              ¬ Ideal.map (RingOfIntegers.mapRingHom ι) (𝔭 : Ideal (𝓞 K)) ≤ Q → w ∉ Q

def WIdeal.Statement (_S : PrimeDiscriminant K) : Prop :=
  ∀ (σ : K →+* ℂ) (L : PeriodPair), latticeEnd L = cmRing σ →
    ∀ 𝔞 : (Ideal (𝓞 K))⁰,
      IsAlgebraic ℚ (discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔞)) ∧
      ∀ (F : Type) [Field F] [NumberField F] (ι : K →+* F) (τ : F →+* ℂ), τ.comp ι = σ →
        discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔞) ∈ Set.range τ →
          ∃ w : 𝓞 F, τ (w : F) = discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔞) ∧
            Ideal.span {w} = Ideal.map (RingOfIntegers.mapRingHom ι) (𝔞 : Ideal (𝓞 K)) ^ 12

def WConjugate.Statement (_S : PrimeDiscriminant K) (F : CMFamily K) : Prop :=
  ∀ 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∃ (k' : Type) (_ : Field k') (_ : NumberField k')
    (_ : Algebra F.k k') (w : k'), ∀ s' : k' →+* ℂ,
      s' w = discrRatio (F.restrict (s'.comp (algebraMap F.k k')))
        (F.periodLattice (s'.comp (algebraMap F.k k'))) 𝔞

def MeanOverEmbeddings.Statement (_S : PrimeDiscriminant K) (F : CMFamily K) : Prop :=
  ∀ 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ,
    embMean F.k (fun s ↦ logPeriod (idealLattice (F.restrict s) 𝔟 * F.periodLattice s)) =
      embMean F.k (fun s ↦ logPeriod (F.periodLattice s))

def ClassMeanOverEmbeddings.Statement (_S : PrimeDiscriminant K) (F : CMFamily K) : Prop :=
  ∀ σ : K →+* ℂ, embMean F.k (fun s ↦ logPeriod (F.periodLattice s)) = classMean σ

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
