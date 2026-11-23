import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.TaylorMvLinear
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EndoZInstance

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Classical
open Formalism.L2.Th1.H (taylorMv tens4 kernel4 alphaQ stdH matH)

def CoefIn1 (f : ℂ → ℂ) (M : IntermediateField ℚ ℂ) : Prop :=
  ∀ k : ℕ, PowerSeries.coeff k (Formalism.L2.Th1.F.taylor0 f) ∈ M

def CoefInMv {n : Type} [Fintype n] [DecidableEq n] (F : (n → ℂ) → ℂ) (M : IntermediateField ℚ ℂ) : Prop :=
  ∀ ν : n →₀ ℕ, MvPowerSeries.coeff ν (taylorMv F) ∈ M

def AlgMv {n : Type} [Fintype n] [DecidableEq n] (F : (n → ℂ) → ℂ) : Prop :=
  ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ CoefInMv F M

def ThetaConstantTermCoefficient : Prop :=
  ∀ (L : PeriodPair) (ω₀ : ℂ), ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    ∀ M : IntermediateField ℚ ℂ, L.g₂ ∈ M → L.g₃ ∈ M → Formalism.L2.Th1.F.s2 L ∈ M → L.weierstrassP (ω₀ / 2) ∈ M →
      CoefIn1 (Formalism.L2.Th1.F.th0 L (ω₀ / 2)) M

def Tens4Alg : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (θ : (n → ℂ) → ℂ), AnalyticOnNhd ℂ θ Set.univ → θ ≠ 0 →
    AlgMv (tens4 θ) → AlgMv θ

section Data

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def kerB (B : Ker.Base D cc δ) : (Fin 4 × D.what₂.Tau → ℂ) → ℂ :=
  kernel4 B.L B.ω₀ B.lamM (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))) B.gC

def KapAlg (B : Ker.Base D cc δ) : Prop := IsAlgebraic ℚ B.kappa

def KerAlg (B : Ker.Base D cc δ) : Prop := AlgMv (kerB B)

def IsTors (B : Ker.Base D cc δ) (x : D.what₂.Tau → ℂ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ (m : ℂ) • x ∈ B.lamM

def trM (B : Ker.Base D cc δ) (x : D.what₂.Tau → ℂ) (θ : (D.what₂.Tau → ℂ) → ℂ) : (D.what₂.Tau → ℂ) → ℂ :=
  Formalism.L2.Th1.H.opU (matH (Ker.hOne B.L D.what₂.Tau)) x θ

def diag4 (x : D.what₂.Tau → ℂ) : Fin 4 × D.what₂.Tau → ℂ := fun w => x w.2

def KerTransAlg (B : Ker.Base D cc δ) : Prop :=
  ∀ x, IsTors B x →
    AlgMv (Formalism.L2.Th1.H.opU (stdH B.L (Fin 4 × D.what₂.Tau)) (diag4 x) (kerB B))

end Data

def ThMMAlg : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Ker.Base D cc δ), B.StdOK → KapAlg B → KerAlg B → AlgMv B.thMM

def ThMMTransAlg : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Ker.Base D cc δ), B.StdOK → KapAlg B → KerTransAlg B →
    ∀ x, IsTors B x → AlgMv (trM B x B.thMM)

end Formalism.L2.KerInert
