import Formalism.LocalToGlobal.Divisibility.JetBounds.PlaceInputAllEntries
import Formalism.LocalToGlobal.Divisibility.JetBounds.JetCounting.RelShape
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.FinalFree
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.HasSubstBlock
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.GramFrameCompositionMvExpFact
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.IntOpTwoFreeOf
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Inertia
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.AgreeOnAdjoin
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.EigenCompatOf
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.EigenFrameEOf
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Tensor
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.EigenFinal

open scoped BigOperators

noncomputable section

namespace Formalism.L2.DIV.C

open Formalism.L2.DIV Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds Formalism.IncomingBounds
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (OwOK TrDual beMean xOfZ sumE phFF thetaS NormRel expF PV)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob at1)

def CurveAt (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) : Prop :=
  5 ≤ l ∧ ‖g2‖ ≤ 1 ∧ ‖g3‖ ≤ 1 ∧ ‖ε‖ = 1 ∧ (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) ∧
    UnrOK (MaximalUnramifiedExtension l) l σ ∧ IsLawOfLog l F ∧
    (∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α) ∧
    ‖(g2 : ℂ_[l]) ^ 3 - 27 * (g3 : ℂ_[l]) ^ 2‖ = 1

def HostInt (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) {n : Type} [Fintype n] (Θ : MvPowerSeries n ℂ_[l]) : Prop :=
  Integral (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum (Formalism.L2.Th1.Top.phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l]) * Θ)

inductive IsHostA (l : ℕ) [Fact l.Prime] (Q : OrbSys ℂ_[l] → ℝ → Prop) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) (N0 N1 : ℕ) :
    (ιr P : Type) → (PV ιr N0 N1 → P) → (S : OrbSys ℂ_[l]) → (P → MvPowerSeries S.ι ℂ_[l]) → MvPowerSeries P ℂ_[l] → ℝ → Prop
  | orbit (d : ℕ) [NeZero d] (h2 : 2 ≤ d) (he : Even d) (hN0 : 0 < N0)
      (ιr : Type) [Fintype ιr] [DecidableEq ιr] (om oms : ιr → MaximalUnramifiedExtension l) (hO : OwOK d σ om oms) (hT : TrDual d σ om oms)
      (ζ : MaximalUnramifiedExtension l) (hζ : IsPrimitiveRoot ζ (l ^ d - 1))
      (g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) ℂ_[l])
      (hg0 : ∀ y, MvPowerSeries.constantCoeff (g y) = 0)
      (hg : ∀ y, MvPowerSeries.subst g (entLog (K := ℂ_[l]) l y) = MvPowerSeries.X y)
      (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0) (hp1 : ∀ s c, 1 ≤ p s c) (I : ∀ s c, Fin (p s c) → Fin N1)
      (nu1 nu2 size : ZMod d → ℕ) (h1 : ∀ s, nu1 s = colN s)
      (h22 : ∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card)
      (hs : ∀ s, size s = ∑ c, p s c)
      (hJ : ∀ s, JnumOneLetter l d TT nu1 size s + (if s ∈ TT then 1 else 0) ≤ N0)
      (δ : MvPolynomial (ZMod d × Fin N0 × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] ℂ_[l])
      (hδ : ∀ R ∈ nablaO (K := ℂ_[l]) colN p hp, ‖δ R‖ ≤ 1) :
      IsHostA l Q σ be0 N0 N1 ιr (PV ιr N0 N1) (fun y => y)
        ((sysA l d N0 N1 (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (beMean l σ be0 om oms ζ)) g (-1) colN p hp I).ap δ)
        (xOfZ (d := d) l (MaximalUnramifiedExtension l).subtype σ om oms) (sumE (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0))
        (expA l d N0 N1 TT nu1 nu2 size)
  | quoted (d : ℕ) [NeZero d] (h2 : 2 ≤ d) (he : Even d)
      (ιr : Type) [Fintype ιr] [DecidableEq ιr] (om oms : ιr → MaximalUnramifiedExtension l) (hO : OwOK d σ om oms) (hT : TrDual d σ om oms)
      (ζ : MaximalUnramifiedExtension l) (hζ : IsPrimitiveRoot ζ (l ^ d - 1))
      (g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) ℂ_[l])
      (hg0 : ∀ y, MvPowerSeries.constantCoeff (g y) = 0)
      (hg : ∀ y, MvPowerSeries.subst g (entLog (K := ℂ_[l]) l y) = MvPowerSeries.X y)
      (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, p s c ≤ N0) (I : ∀ s c, Fin (p s c) → Fin N1) (β : ℝ)
      (hq : Q (sysF l d N0 N1 g (Formalism.DworkPowerSeriesWeights.mvExp ((-1 : ℂ_[l]) • bSum (idM : ZV d N0 N1 → ZV d N0 N1 → ℂ_[l])
        (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (beMean l σ be0 om oms ζ)))) colN p hp I) β)
      (δ : MvPolynomial (ZMod d × Fin N0 × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] ℂ_[l])
      (hδ : ∀ R ∈ nablaO (K := ℂ_[l]) colN p hp, ‖δ R‖ ≤ 1) :
      IsHostA l Q σ be0 N0 N1 ιr (PV ιr N0 N1) (fun y => y)
        ((sysF l d N0 N1 g (Formalism.DworkPowerSeriesWeights.mvExp ((-1 : ℂ_[l]) • bSum (idM : ZV d N0 N1 → ZV d N0 N1 → ℂ_[l])
          (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (beMean l σ be0 om oms ζ)))) colN p hp I).ap δ)
        (xOfZ (d := d) l (MaximalUnramifiedExtension l).subtype σ om oms) (sumE (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0)) β
  | mul {ι₁ ι₂ P₁ P₂ : Type} {e₁ : PV ι₁ N0 N1 → P₁} {e₂ : PV ι₂ N0 N1 → P₂} {S₁ S₂ : OrbSys ℂ_[l]}
      {x₁ : P₁ → MvPowerSeries S₁.ι ℂ_[l]} {x₂ : P₂ → MvPowerSeries S₂.ι ℂ_[l]}
      {Ψ₁ : MvPowerSeries P₁ ℂ_[l]} {Ψ₂ : MvPowerSeries P₂ ℂ_[l]} {β₁ β₂ : ℝ}
      (h₁ : IsHostA l Q σ be0 N0 N1 ι₁ P₁ e₁ S₁ x₁ Ψ₁ β₁) (h₂ : IsHostA l Q σ be0 N0 N1 ι₂ P₂ e₂ S₂ x₂ Ψ₂ β₂) :
      IsHostA l Q σ be0 N0 N1 (ι₁ ⊕ ι₂) (P₁ ⊕ P₂)
        (fun y => Sum.elim (fun i => Sum.inl (e₁ (y.1, i, y.2.2))) (fun i => Sum.inr (e₂ (y.1, i, y.2.2))) y.2.1)
        (S₁.mul S₂)
        (Sum.elim (fun q => serAlong Sum.inl (x₁ q)) (fun q => serAlong Sum.inr (x₂ q)))
        (serAlong Sum.inl Ψ₁ + serAlong Sum.inr Ψ₂) (β₁ + β₂)

inductive IsHostB (l : ℕ) [Fact l.Prime] (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) (ph : PowerSeries (MaximalUnramifiedExtension l))
    (N0 N1 : ℕ) :
    (P : Type) → (S : OrbSys ℂ_[l]) → (P → MvPowerSeries S.ι ℂ_[l]) → MvPowerSeries P ℂ_[l] → ℝ → Prop
  | orbit (Cn : ℕ) (ζ : MaximalUnramifiedExtension l) (hζ : IsPrimitiveRoot ζ (l ^ 2 - 1))
      (g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) ℂ_[l])
      (hg0 : ∀ y, MvPowerSeries.constantCoeff (g y) = 0)
      (hg : ∀ y, MvPowerSeries.subst g (oneLog (K := ℂ_[l]) l y) = MvPowerSeries.X y)
      (p : Fin Cn → ℕ) (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1)
      (δ : MvPolynomial (Fin N0 × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] ℂ_[l])
      (hδ : ∀ R ∈ minorProductsLattice (k := ℂ_[l]) p hp, ‖δ R‖ ≤ 1) :
      IsHostB l σ be0 ph N0 N1 (Fin N0 × Fin N1)
        ((sysB l N0 N1 Cn (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype
          (beMean (d := 2) l σ be0 (fun _ : Unit => (1 : MaximalUnramifiedExtension l)) (fun _ => 1) ζ)) 1 g (-1) p hp I).ap δ)
        (fun y => at1 y (expF ℂ_[l] l)) (∑ y, at1 y (PowerSeries.map (MaximalUnramifiedExtension l).subtype ph))
        (expB l N0 N1 Cn p)
  | mul {P₁ P₂ : Type} {S₁ S₂ : OrbSys ℂ_[l]}
      {x₁ : P₁ → MvPowerSeries S₁.ι ℂ_[l]} {x₂ : P₂ → MvPowerSeries S₂.ι ℂ_[l]}
      {Ψ₁ : MvPowerSeries P₁ ℂ_[l]} {Ψ₂ : MvPowerSeries P₂ ℂ_[l]} {β₁ β₂ : ℝ}
      (h₁ : IsHostB l σ be0 ph N0 N1 P₁ S₁ x₁ Ψ₁ β₁) (h₂ : IsHostB l σ be0 ph N0 N1 P₂ S₂ x₂ Ψ₂ β₂) :
      IsHostB l σ be0 ph N0 N1 (P₁ ⊕ P₂) (S₁.mul S₂)
        (Sum.elim (fun q => serAlong Sum.inl (x₁ q)) (fun q => serAlong Sum.inr (x₂ q)))
        (serAlong Sum.inl Ψ₁ + serAlong Sum.inr Ψ₂) (β₁ + β₂)

end Formalism.L2.DIV.C
