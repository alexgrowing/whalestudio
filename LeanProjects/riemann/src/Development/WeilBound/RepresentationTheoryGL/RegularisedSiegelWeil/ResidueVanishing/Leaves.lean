import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.HasLevel
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingWittTowerReduction
import Development.AutomorphicSpectrum.PublishedTheorems.SiegelWeil₂.RegularisedSiegelWeilFirstTermIdentity2
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsHeckeCharRestrictionEtaInv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartMemRationalIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CosetSumAlongMulEquivSubgroups
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledFlatSectionEqTranslateStandardSection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodMajorantLevelConjUnitaryAdelicMaximalCompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GodementSectionInvariantConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RightTranslateCommutesCenterAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanPairingLieDerivativeAntisymm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GodementSectionSmoothBounded
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentAtTauMemStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GelfandTransposeEqOfInvariantWords
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterActionSmoothCommuting
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanPairingEisensteinSimplePole
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralTranslateSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactAverageProjectionThetaSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaMapSchrodingerPartialIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilChartSiegelParabolicAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntertwiningStabilizerTranslateScalar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardUnitaryChartDoubledSpace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryHeightIsSiegelHeightFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumTransportSchwartzBruhatStandard
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSiegelParabolicConjDoubledCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelEqTsumSchrodingerFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilChartScalarAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaCenterActionLeft
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterActionTransportChart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerModelSmoothInGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerModelCenterEquivariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EisensteinSeriesContinuationModuli
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFSingleOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContAutRapidDecBoundedIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.DmOfHyp

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Eis
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.StdUnn PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.Kplug

def K0 : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle)
    (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ omh →
    ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 →
    ∀ a : GL (Fin A.rank) (AE D), IsMaj A a → ∀ f, IsThetaFunO ψ (dblSp A) B f → IsKFinVec omh (Khat A a) f →
      swSec A B omh ν 𝓨 f ∈ degPS A a χ⁻¹ (sZero A B)

def K1 : Prop :=
  ∀ (D : D7) (V : HSp D) (Φ : ℂ → GA D (dblSp V) → ℂ), EisContinues V Φ → (∀ s₀, ∃ k, EisRegularAt V Φ s₀ k) →
    (∀ g, AnalyticOnNhd ℂ (eisSer V Φ g) {z : ℂ | (V.rank : ℝ) / 2 < z.re}) → ∀ s₀ : ℂ,
    ∃ (U : Set ℂ) (d : Polynomial ℂ) (E : ℂ → GA D (dblSp V) → ℂ) (ε : ℝ),
      IsOpen U ∧ IsRightDomain U ∧ s₀ ∈ U ∧ d ≠ 0 ∧ (∀ g, DifferentiableOn ℂ (E · g) U) ∧
      ContinuousOn (fun y : ℂ × GA D (dblSp V) => E y.1 y.2) (U ×ˢ Set.univ) ∧
      (∀ z ∈ U, ∀ γ ∈ GQ (dblSp V), ∀ g, E z (γ * g) = E z g) ∧
      (∀ z : ℂ, (V.rank : ℝ) / 2 < z.re → ∀ g, E z g = d.eval z * eisSer V Φ g z) ∧ IsRad U d s₀ ε

def K2 : Prop :=
  ∀ (h e : ℂ → ℂ) (U : Set ℂ) (d : Polynomial ℂ) (s₀ : ℂ) (ε σ : ℝ), IsOpen U → IsRightDomain U → DifferentiableOn ℂ e U →
    d ≠ 0 → IsRad U d s₀ ε → (∀ z : ℂ, σ < z.re → e z = d.eval z * h z) →
    (∀ k : ℕ, 2 ≤ k → (2 * Real.pi * Complex.I)⁻¹ * ∮ z in C(s₀, ε), (z - s₀) ^ (k - 1) * (e z / d.eval z) = 0) →
    CoeffAt h s₀ (-1) ((2 * Real.pi * Complex.I)⁻¹ * ∮ z in C(s₀, ε), (z - s₀) ^ (1 - 1) * (e z / d.eval z)) ∧
      PoleLE h s₀ 1

def SimplePoleRescaling : Prop :=
  ∀ (h h' : ℂ → ℂ) (s₀ c : ℂ) (r : ℝ≥0) (σ : ℝ), 0 < r → CoeffAt h s₀ (-1) c → PoleLE h s₀ 1 →
    (∀ s : ℂ, σ < s.re → h' s = npow r (s₀ - s) * h s) → CoeffAt h' s₀ (-1) c

def ContinuousInvariantCoefficients : Prop :=
  ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0) (φ : G D n → ℂ) (s₀ : ℂ) (U : Set ℂ) (d : Polynomial ℂ) (E : ℂ → G D n → ℂ) (σ : ℝ),
    IsCont H φ s₀ U d E σ → ∀ ε, IsRad U d s₀ ε → ∀ k, Continuous (cf d E s₀ ε k) ∧ LeftInv (GF D n) (cf d E s₀ ε k)

def KillingPolyConst : Prop :=
  ∀ (D : D7) (A : HSp D) (μ : D.host.E), GlobalTheory.StdUnn.IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ →
    ∀ (a : GL (Fin A.rank) (AE D)), IsMaj A a → ∀ p : siegel A, IsConj A a κ p →
      IsHt (hgtStd A a κ p) ∧ HasLevel (hgtStd A a κ p)

def ContinuationThroughChart : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle)
    (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ omh →
    ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ θ : InfFam D, IsInfFam θ →
    ∀ μ : D.host.E, GlobalTheory.StdUnn.IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ →
    ∀ omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank), IsTransport ψ θ A B ν 𝓨 omh κ omS →
    ∀ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ →
    ∀ (a : GL (Fin A.rank) (AE D)), IsMaj A a → ∀ p : siegel A, IsConj A a κ p →
    ∀ f, IsThetaFunO ψ (dblSp A) B f → IsKFinVec omh (Khat A a) f →
    ∀ Φ : schwartzA θ B.rank A.rank, Φ.1 = sch ψ A B ν 𝓨 (omh ((p : GA D (dblSp A))⁻¹, 1) f) →
    ∀ (U : Set ℂ) (d : Polynomial ℂ) (E : ℂ → GA D (dblSp A) → ℂ),
      IsOpen U → IsRightDomain U → sZero A B ∈ U → d ≠ 0 → (∀ g, DifferentiableOn ℂ (E · g) U) →
      ContinuousOn (fun y : ℂ × GA D (dblSp A) => E y.1 y.2) (U ×ˢ Set.univ) →
      (∀ z ∈ U, ∀ γ ∈ GQ (dblSp A), ∀ g, E z (γ * g) = E z g) →
      (∀ z : ℂ, (A.rank : ℝ) / 2 < z.re → ∀ g,
        E z g = d.eval z * eisSer A (flat A a (swSec A B omh ν 𝓨 f) (sZero A B)) g z) →
      Continuous (fun g => (omS g Φ).1 0) ∧
      IsCont (hgtStd A a κ p) (fun g => (omS g Φ).1 0) (sZero A B) U d
        (fun z g => npow (absA D (aP A p)) (z - sZero A B) * E z (κ.symm g * ((p : GA D (dblSp A))⁻¹))) ((A.rank : ℝ) / 2) ∧
      ∀ (z : ℂ), (A.rank : ℝ) / 2 < z.re → ∀ g : GA D (dblSp A),
        eisSer A (flat A a (swSec A B omh ν 𝓨 f) (sZero A B)) g z =
          npow (absA D (aP A p)) (sZero A B - z) * eisS (fam (hgtStd A a κ p) (fun g => (omS g Φ).1 0) (sZero A B) z) (κ (g * p))

def K4 : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)),
    GlobalTheory.Core.Rk.Exh.Defin θ A cA a → ∀ (W : HSp D) (χ : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D W →* Module.End ℂ (WO (dblSp A) W → ℂ)),
    IsWeilDatumO ψ (dblSp A) W 1 χ omh → ∀ (ν : Measure (WO A W)) (𝓨 : Set (WO A W)), IsCovolOne (ratL W A) ν 𝓨 →
    ∀ μ : D.host.E, GlobalTheory.StdUnn.IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ →
    ∀ omS : G D A.rank →* Module.End ℂ (schwartzA θ W.rank A.rank), IsTransport ψ θ A W ν 𝓨 omh κ omS →
    ∀ p : siegel A, ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u : GA D A → ℂ, Continuous u → (∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) →
    GlobalTheory.Core.Rk.Exh.Kills ψ χ omh m u → ∀ F : G D A.rank → ℂ, Continuous F → LeftInv (GF D A.rank) F →
    (∀ (X : Type) [MeasurableSpace X] (νX : Measure X) [IsFiniteMeasure νX] (c : X → G D A.rank), Measurable c →
      IsCompact (closure (Set.range c)) → ∀ w : X → ℂ, Integrable w νX →
      (∀ (Ψ : schwartzA θ W.rank A.rank) (h : GA D W), ∫ x, theta omS Ψ (c x) h * w x ∂νX = 0) →
      ∫ x, F (c x) * w x ∂νX = 0) →
    dblInt A χ⁻¹ m (fun g => F (κ (g * p))) (fun g => conj (u g)) (fun g => conj (u g)) = 0

section Target

open scoped ComplexConjugate Matrix NNReal
open IsDedekindDomain NumberField GlobalTheory.Cusp
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta)
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

def ResidueVanishing : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)),
    Defin θ A cA a → (∀ v : FinPl D, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) →
    ∀ (B W : HSp D) (t : ℕ) (_ : HypDec B W t), HSpace.SigOK B → HSpace.SigOK W → 0 < W.rank → 0 < t →
    A.rank = W.rank + t → W.rank + 2 < 2 * t → W.rank < t →
    ∀ (χ : (AE D)ˣ →* Circle) (omB : WRep (dblSp A) B) (omW : WRep (dblSp A) W),
    IsWeilDatumO ψ (dblSp A) B 1 χ omB → IsWeilDatumO ψ (dblSp A) W 1 χ omW → ∀ ν 𝓕, IsCovolOne (ratL B A) ν 𝓕 →
    ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u : GA D A → ℂ, Continuous u → (∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) →
    Kills ψ χ omW m u → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → IsKFinVec omB (Khat A a) φ →
    ∃ E₁, GlobalTheory.Eis.EisCoeffAt A (flat A a (swSec A B omB ν 𝓕 φ) (sZero A B)) (sZero A B) (-1) E₁ ∧
      GlobalTheory.Eis.dblInt A χ⁻¹ m E₁ (fun g => conj (u g)) (fun g => conj (u g)) = 0

end Target

end PositivityTheory.Rg.Rsw.Kplug

end
