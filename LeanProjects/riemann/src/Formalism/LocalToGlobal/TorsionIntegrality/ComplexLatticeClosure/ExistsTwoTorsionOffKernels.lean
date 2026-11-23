import Formalism.LocalToGlobal.GlobalTheory.LinkTiesTh
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.CMQuasiPeriodConst
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaZeroTranslateProduct

noncomputable section

namespace Formalism.L2.Th1.F2

open Formalism.L2.GlobalTheoryTheory Formalism.MainNotions

def IsLat (Λ : AddSubgroup ℂ) : Prop := ∃ L : PeriodPair, L.lattice.toAddSubgroup = Λ

def HasCM (d : ℕ) (Λ : AddSubgroup ℂ) : Prop := ∀ x ∈ Λ, F.cmTheta 1 d * x ∈ Λ

def IsLatOfZLattice : Prop :=
  ∀ (Λ : AddSubgroup ℂ), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set ℂ) = ⊤ → IsLat Λ

def AreaEq : Prop := ∀ L : PeriodPair, TaylorLogMetric.area L.lattice.toAddSubgroup = F.area L

def AreaPosLat : Prop := ∀ Λ : AddSubgroup ℂ, IsLat Λ → 0 < TaylorLogMetric.area Λ

def QInt : Prop :=
  ∀ (d : ℕ) (Λ : AddSubgroup ℂ), IsLat Λ → HasCM d Λ → ∀ x ∈ Λ, ∃ k : ℤ, Real.sqrt d / 2 * (H1 Λ x x).re = k

def ExistsTwoTorsionOffKernels : Prop :=
  ∀ (d : ℕ) (L : PeriodPair),
    ∃ ω₀ ∈ L.lattice, F.cmTheta 1 d * (ω₀ / 2) ∉ L.lattice ∧ (1 - F.cmTheta 1 d) * (ω₀ / 2) ∉ L.lattice

def ThetaZeroWitness : Prop :=
  ∀ (d : ℕ) (L : PeriodPair) (ω₀ : ℂ), d % 8 = 7 → HasCM d L.lattice.toAddSubgroup → ω₀ ∈ L.lattice →
    F.cmTheta 1 d * (ω₀ / 2) ∉ L.lattice → (1 - F.cmTheta 1 d) * (ω₀ / 2) ∉ L.lattice →
    IsTheta0 d L.lattice.toAddSubgroup (F.th0 L (ω₀ / 2))

def ThetaZeroExistence : Prop :=
  ∀ (d : ℕ) (Λ : AddSubgroup ℂ), d % 8 = 7 → IsLat Λ → HasCM d Λ → ∃ G, IsTheta0 d Λ G

def ThetaZeroUniqueness : Prop :=
  ∀ (d : ℕ) (Λ : AddSubgroup ℂ) (G G' : ℂ → ℂ), IsLat Λ → IsTheta0 d Λ G → IsTheta0 d Λ G' → G = G'

def DensityPeriodic : Prop :=
  ∀ (d : ℕ) (Λ : AddSubgroup ℂ) (G : ℂ → ℂ), IsTheta0 d Λ G → ∀ x ∈ Λ, ∀ z,
    ‖G (z + x)‖ ^ 2 * Real.exp (-Real.pi * (H1 Λ (z + x) (z + x)).re) = ‖G z‖ ^ 2 * Real.exp (-Real.pi * (H1 Λ z z).re)

def NormAny : Prop :=
  ∀ (d : ℕ) (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) (Fd : Set ℂ), IsLat Λ → IsTheta0 d Λ G →
    MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume →
    MeasureTheory.volume Fd = ENNReal.ofReal (TaylorLogMetric.area Λ) ∧
    MeasureTheory.IntegrableOn (fun z => ‖G z‖ ^ 2 * Real.exp (-Real.pi * (H1 Λ z z).re)) Fd MeasureTheory.volume ∧
    normSq1 Λ G = (TaylorLogMetric.area Λ)⁻¹ * ∫ z in Fd, ‖G z‖ ^ 2 * Real.exp (-Real.pi * (H1 Λ z z).re)

def NormPos : Prop :=
  ∀ (d : ℕ) (Λ : AddSubgroup ℂ) (G : ℂ → ℂ), IsLat Λ → IsTheta0 d Λ G → 0 < normSq1 Λ G

def ThetaZeroEpsilon : Prop :=
  ∀ (d : ℕ) (Λ : AddSubgroup ℂ), d % 8 = 7 → IsLat Λ → HasCM d Λ →
    IsTheta0 d Λ (Classical.epsilon (IsTheta0 d Λ)) ∧ 0 < normSq1 Λ (Classical.epsilon (IsTheta0 d Λ))

def CmExample : Prop :=
  ∀ (d : ℕ) (hd : 0 < d), d % 4 = 3 →
    IsLat (F.cmPair 1 1 d one_pos hd).lattice.toAddSubgroup ∧ HasCM d (F.cmPair 1 1 d one_pos hd).lattice.toAddSubgroup

def BotNotUnique : Prop :=
  ∀ d : ℕ, IsTheta0 d ⊥ (fun _ => 1) ∧ IsTheta0 d ⊥ (fun z => 1 + z)

end Formalism.L2.Th1.F2
