import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionAlgebraCp
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittEmbeddingsCompatible
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.UniformGaussModelCondition

noncomputable section

namespace Formalism.L2.KerInert.K1

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp OcC)
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def sumBe (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι] (be : MvPowerSeries (Fin 2) (K0 p)) :
    MvPowerSeries (ι ⊕ ι) (K0 p) :=
  ∑ e : ι, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e))

def FirstKernelGeneratorOfSum : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ι : Type) [Fintype ι] (K1 : Type) [Field K1] [Algebra (K0 p) K1] (R1 : Subring K1)
    (be : MvPowerSeries (Fin 2) (K0 p)) (Th : MvPowerSeries (ι ⊕ ι) K1),
    BeProp p be →
    Formalism.MainNotions.FormalGroupSystem.Simeq p (MvPowerSeries.subst (fun i => -MvPowerSeries.X i) (sumBe p be) :
      MvPowerSeries (ι ⊕ ι) (K0 p)) (sumBe p be) →
    IntR R1 (inParamK p K1 (Th * MvPowerSeries.map (algebraMap (K0 p) K1) (expS p (sumBe p be)))) →
    ExtensionGeneratorCondition p K1 R1 be Th

def FirstKernelGeneratorIff : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
  ∀ (ι : Type) [Fintype ι] (K1 : Type) [Field K1] [Algebra (K0 p) K1] (R1 : Subring K1),
    (∀ w : WW p, algebraMap (K0 p) K1 (algebraMap (WW p) (K0 p) w) ∈ R1) →
  ∀ (be : MvPowerSeries (Fin 2) (K0 p)) (Th : MvPowerSeries (ι ⊕ ι) K1),
    ExtensionGeneratorCondition p K1 R1 be Th ↔
      (BeProp p be ∧
        Formalism.MainNotions.FormalGroupSystem.Simeq p (MvPowerSeries.subst (fun i => -MvPowerSeries.X i) (sumBe p be) :
          MvPowerSeries (ι ⊕ ι) (K0 p)) (sumBe p be) ∧
        IntR R1 (inParamK p K1 (Th * MvPowerSeries.map (algebraMap (K0 p) K1) (expS p (sumBe p be)))))

def SumBeEven : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (ι : Type) [Fintype ι] (be : MvPowerSeries (Fin 2) (K0 p)),
    BeProp p be →
    Formalism.MainNotions.FormalGroupSystem.Simeq p (MvPowerSeries.subst (fun i => -MvPowerSeries.X i) (sumBe p be) :
      MvPowerSeries (ι ⊕ ι) (K0 p)) (sumBe p be)

def hypLin (l : ℕ) [Fact l.Prime] {ι n : Type} [Fintype ι] (f f' : ι → n → MaximalUnramifiedExtension l) (i : n) :
    MvPowerSeries (ι ⊕ ι) ℂ_[l] :=
  ∑ e : ι, (MvPowerSeries.C (f e i : ℂ_[l]) * MvPowerSeries.X (Sum.inl e) +
    MvPowerSeries.C (f' e i : ℂ_[l]) * MvPowerSeries.X (Sum.inr e))

def HypOfOrth : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l →
  ∀ g2 g3 ε s2 : MaximalUnramifiedExtension l, ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  (∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α) →
  ∀ (ι n : Type) [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
    (f f' : ι → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
  ∀ be : MvPowerSeries (Fin 2) (K0 l), MvPowerSeries.constantCoeff be = 0 →
    Formalism.InvariantFactorPaths.G7.Simeq (MvPowerSeries.map (k0ToC l) (inParam l be))
      (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (cob F (phFF l g2 g3 s2 ε))) →
  ∀ Θ : MvPowerSeries n ℂ_[l],
    Integral (mvExp (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l]) *
      @inParamK l _ n ℂ_[l] _ (wittFractionAlgebraCp l) Θ) →
    IntR (OcC l) (@inParamK l _ (ι ⊕ ι) ℂ_[l] _ (wittFractionAlgebraCp l)
      (MvPowerSeries.subst (hypLin l f f') Θ * MvPowerSeries.map (k0ToC l) (expS l (sumBe l be))))

def FirstKernelGeneratorOfOrthogonal : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l →
  ∀ g2 g3 ε s2 : MaximalUnramifiedExtension l, ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  (∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α) →
  ∀ (ι n : Type) [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
    (f f' : ι → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
  ∀ be : MvPowerSeries (Fin 2) (K0 l), BeProp l be →
    Formalism.InvariantFactorPaths.G7.Simeq (MvPowerSeries.map (k0ToC l) (inParam l be))
      (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (cob F (phFF l g2 g3 s2 ε))) →
  ∀ Θ : MvPowerSeries n ℂ_[l],
    Integral (mvExp (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l]) *
      @inParamK l _ n ℂ_[l] _ (wittFractionAlgebraCp l) Θ) →
    @ExtensionGeneratorCondition l _ ι _ ℂ_[l] _ (wittFractionAlgebraCp l) (OcC l) be (MvPowerSeries.subst (hypLin l f f') Θ)

end Formalism.L2.KerInert.K1
