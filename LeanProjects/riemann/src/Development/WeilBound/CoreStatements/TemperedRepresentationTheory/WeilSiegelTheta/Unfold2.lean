import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.HeisSch

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.GramSchwartzFunctions.EC

open GlobalTheory.StdUnn

def Term2 : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) ψ χ θ μ ω, HidaSetting D n V ψ χ θ μ ω →
  ∀ Φ : schwartzA θ V.rank n, ∀ (r : ℕ), r ≤ n → ∀ (μr : Measure (Mx D V.rank r)),
    (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕) →
  ∀ (c : Matrix (Fin r) (Fin n) D.host.E) (a : Matrix (Fin n) (Fin n) D.host.E), IsCompl c a →
  ∀ b : HermE D r, ∀ γ ∈ GF D n, mat γ = (repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b.1 a).map (incA D) →
    (ω γ Φ).1 0 = J ψ V μr (pull c Φ.1) b

def Unfold2 : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ θ : InfFam D, IsInfFam θ →
  ∀ (V : HSp D) (n r : ℕ), r ≤ n → ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)),
    IsCovolOne (ratMx D V.rank n) μ 𝓕 →
  ∀ μr : Measure (Mx D V.rank r), (∃ 𝓕r, IsCovolOne (ratMx D V.rank r) μr 𝓕r) →
  ∀ (c : Matrix (Fin r) (Fin n) D.host.E) (a : Matrix (Fin n) (Fin n) D.host.E), IsCompl c a → ∀ b : HermE D r,
  ∀ Φ : Mx D V.rank n → ℂ, Φ ∈ schwartzA θ V.rank n →
    ∫ y in 𝓕, ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E,
        Heisenberg₂ ψ V (HMul.hMul (zy y) ((repMat (D.sp.cm.sig : D.host.E →+* D.host.E) b.1 a).map (incA D))) Φ
          (ξ.map (incA D)) ∂μ =
      J ψ V μr (pull c Φ) b

end PositivityTheory.GramSchwartzFunctions.EC
