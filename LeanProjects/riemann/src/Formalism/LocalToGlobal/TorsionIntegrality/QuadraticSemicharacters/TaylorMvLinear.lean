import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EndoZInstance
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementN

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

def taylorMv {n : Type*} [Fintype n] [DecidableEq n] (F : (n → ℂ) → ℂ) : MvPowerSeries n ℂ :=
  fun ν => ((ν.degree.factorial : ℕ) : ℂ)⁻¹ *
    ∑ f : Fin ν.degree → n with ∀ i, (Finset.univ.filter fun j => f j = i).card = ν i,
      iteratedFDeriv ℂ ν.degree F 0 fun j => Pi.single (f j) (1 : ℂ)

def lineRestr {K : Type*} [CommRing K] {n : Type*} (v : n → K) (T : MvPowerSeries n K) : PowerSeries K :=
  MvPowerSeries.subst (fun i => (PowerSeries.C (v i) * PowerSeries.X : PowerSeries K)) T

def linSubst {K : Type*} [CommRing K] {m n : Type*} [Fintype n] (M : Matrix m n K) (T : MvPowerSeries m K) :
    MvPowerSeries n K :=
  MvPowerSeries.subst (fun i => ∑ j, MvPowerSeries.C (M i j) * (MvPowerSeries.X j : MvPowerSeries n K)) T

def LineCoeff : Prop :=
  ∀ (K : Type) [CommRing K] (n : Type) [Fintype n] [DecidableEq n] (v : n → K) (T : MvPowerSeries n K) (k : ℕ),
    PowerSeries.coeff k (lineRestr v T)
      = ∑ ν ∈ Finset.finsuppAntidiag Finset.univ k, MvPowerSeries.coeff ν T * ∏ i, v i ^ ν i

def LineUnique : Prop :=
  ∀ (K : Type) [Field K] [Infinite K] (n : Type) [Fintype n] (T T' : MvPowerSeries n K),
    (∀ v, lineRestr v T = lineRestr v T') → T = T'

def TaylorLine : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (F : (n → ℂ) → ℂ), AnalyticAt ℂ F 0 → ∀ v : n → ℂ,
    lineRestr v (taylorMv F) = Formalism.L2.Th1.F.taylor0 fun t => F (t • v)

def TaylorMvLinear : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (F G : (n → ℂ) → ℂ), AnalyticAt ℂ F 0 → AnalyticAt ℂ G 0 →
    taylorMv (fun z => F z + G z) = taylorMv F + taylorMv G ∧
    ∀ c : ℂ, taylorMv (fun z => c * F z) = MvPowerSeries.C c * taylorMv F

def TaylorMvMul : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (F G : (n → ℂ) → ℂ), AnalyticAt ℂ F 0 → AnalyticAt ℂ G 0 →
    taylorMv (fun z => F z * G z) = taylorMv F * taylorMv G

def TaylorMvComp : Prop :=
  ∀ (m n : Type) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (M : Matrix m n ℂ)
    (F : (m → ℂ) → ℂ), AnalyticAt ℂ F 0 →
    taylorMv (fun w : n → ℂ => F (M.mulVec w)) = linSubst M (taylorMv F)

def TaylorMvCoord : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (i : n) (f : ℂ → ℂ), AnalyticAt ℂ f 0 →
    taylorMv (fun z : n → ℂ => f (z i)) = Formalism.InvariantFactorPaths.G7.at1 i (Formalism.L2.Th1.F.taylor0 f)

def TaylorMvProd : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (f : n → ℂ → ℂ), (∀ i, AnalyticAt ℂ (f i) 0) →
    taylorMv (prodFn f) = ∏ i, Formalism.InvariantFactorPaths.G7.at1 i (Formalism.L2.Th1.F.taylor0 (f i))

def TaylorMvTens4 : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (θ : (n → ℂ) → ℂ), AnalyticAt ℂ θ 0 →
    taylorMv (tens4 θ) = Formalism.L2.Th1.E.tensor4 (taylorMv θ)

def TaylorMvInj : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (F G : (n → ℂ) → ℂ), AnalyticOnNhd ℂ F Set.univ →
    AnalyticOnNhd ℂ G Set.univ → taylorMv F = taylorMv G → F = G

end Formalism.L2.Th1.H
