import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger

noncomputable section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published

open GlobalTheory.StdUnn

def SiegelWeilUnitarySchrodingerLit : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D), n < V.rank → V.rank ≤ 2 * n → n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank →
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ →
  ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank →
  ∀ θ : InfFam D, IsInfFam θ →
  ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
  ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω →
  ∀ H : G D n → ℝ≥0, IsHeight H →
  ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l →
  ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) →
  ∀ ν : Measure (GA D V), ν.IsHaarMeasure →
  ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s →
    ∀ g, HolValueAt (fun z => Eis.cosetSum (P D n) (GF D n) (sect ω H Φ z) g) (s0 V n) (thetaInt ω ν Φ g)

end GlobalTheory.Published

end
