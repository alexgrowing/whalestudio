import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactSubgroupSmallAnnihilator
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFourierExpansion
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitriangularMapInduction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def uM (n : ℕ) (x : Fin n → k) : Mir k n := unipIn k n (Multiplicative.ofAdd x)

def shearGL (n : ℕ) (b : Fin (n + 1) → k) : GL (Fin (n + 1)) k :=
  open Classical in if h : IsUnit (1 + vecMulVec (eLast k n) b) then h.unit else 1

def piHaar [MeasurableSpace k] (ν : Measure k) (m : ℕ) : Measure (Fin m → k) := Measure.pi fun _ => ν

def wt (ψ : AddChar k Circle) (n : ℕ) (x : Fin (n + 1) → k) : ℂ := ((ψ (-x (Fin.last n)) : Circle) : ℂ)

section Rep

variable {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

def coef (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (v : V) (v' : V') (x : Fin n → k) : ℂ :=
  B (T (uM n x) v) v'

def TwInv (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V')
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ) : Prop :=
  ∀ (p : Mir k (n + 1)) v v', B (T p v) (T' p v') =
    ((detChar (Fin (n + 1 + 1)) (absPow k (s : ℂ)) (p : GL (Fin (n + 1 + 1)) k) : ℂˣ) : ℂ) * B v v'

def JJ [MeasurableSpace k] (ν : Measure k) (ψ : AddChar k Circle) (T : Representation ℂ (Mir k (n + 1)) V)
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (M : Set (Fin (n + 1) → k)) (v : V) (v' : V') : ℂ :=
  ∫ x in M, wt ψ n x * coef T B v v' x ∂(piHaar ν (n + 1))

def EvVal [MeasurableSpace k] (ν : Measure k) (ψ : AddChar k Circle) (T : Representation ℂ (Mir k (n + 1)) V)
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (v : V) (v' : V') (A : ℂ) : Prop :=
  ∃ t₀ : kˣ, ∀ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) →
    JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' = A

end Rep

end GlobalTheory.CompanionTheory.MirPair

end
