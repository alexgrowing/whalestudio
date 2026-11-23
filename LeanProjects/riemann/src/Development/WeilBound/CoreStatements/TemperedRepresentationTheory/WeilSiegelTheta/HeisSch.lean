import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.GramSchwartzFunctions.EC

open GlobalTheory.StdUnn

variable {D : D7}

def xPart {m n : ℕ} (v : Mx D m (n + n)) : Mx D m n := Matrix.of fun i j => v i (finSumFinEquiv (Sum.inl j))

def yPart {m n : ℕ} (v : Mx D m (n + n)) : Mx D m n := Matrix.of fun i j => v i (finSumFinEquiv (Sum.inr j))

def zy {m n : ℕ} (y : Mx D m n) : Mx D m (n + n) :=
  Matrix.of fun i k => Sum.elim (fun _ => (0 : AE D)) (y i) (finSumFinEquiv.symm k)

def Heisenberg₂ (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {n : ℕ} (v : Mx D V.rank (n + n)) (Φ : Mx D V.rank n → ℂ) :
    Mx D V.rank n → ℂ :=
  fun z => ψ (trA (Matrix.trace (inner V z (yPart v))) + halfTr (Matrix.trace (inner V (xPart v) (yPart v)))) *
    Φ (z + xPart v)

def HeisSch : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ θ : InfFam D, IsInfFam θ →
  ∀ (V : HSp D) (n : ℕ) (v : Mx D V.rank (n + n)) (Φ : Mx D V.rank n → ℂ),
    Φ ∈ schwartzA θ V.rank n → Heisenberg₂ ψ V v Φ ∈ schwartzA θ V.rank n

def Covar : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω, HidaSetting D n V ψ χ θ μ ω →
  ∀ γ ∈ GF D n, ∀ (v : Mx D V.rank (n + n)) (Φ Ψ : schwartzA θ V.rank n), Ψ.1 = Heisenberg₂ ψ V v Φ.1 →
    (ω γ Ψ).1 = Heisenberg₂ ψ V (HMul.hMul v (mat γ⁻¹)) (ω γ Φ).1

def Zero : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ θ : InfFam D, IsInfFam θ →
  ∀ (V : HSp D) (n : ℕ) (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
  ∀ Φ : Mx D V.rank n → ℂ, Φ ∈ schwartzA θ V.rank n →
    Φ 0 = ∫ y in 𝓕, ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, Heisenberg₂ ψ V (zy y) Φ (ξ.map (incA D)) ∂μ

def Unfold : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ θ : InfFam D, IsInfFam θ →
  ∀ (V : HSp D) (n r : ℕ) (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
  ∀ μr : Measure (Mx D V.rank r), (∃ 𝓕r, IsCovolOne (ratMx D V.rank r) μr 𝓕r) →
  ∀ (c : Matrix (Fin r) (Fin n) D.host.E) (a : Matrix (Fin n) (Fin n) D.host.E), IsCompl c a → ∀ b : HermE D r,
  ∀ Φ : Mx D V.rank n → ℂ, Φ ∈ schwartzA θ V.rank n →
    ∫ y in 𝓕, ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
        Heisenberg₂ ψ V (HMul.hMul (zy y) ((repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b.1 a).map (incA D))) Φ
          (ξ.map (incA D)) ∂μ =
      J ψ V μr (pull c Φ) b

end PositivityTheory.GramSchwartzFunctions.EC
