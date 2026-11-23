import Development.WeilBound.ThetaLifts.EigenvalueEndgame.PlaneRemovalConfiguration
import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable

noncomputable section

namespace PositivityTheory.ThKEnd.Orth

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl

def SigRapid : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ f ∈ Sig B G om om', IsCusp G.W f → IsRapid (Y := G.W) f

def SigThConst : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ f ∈ Sig B G om om', IsRapid (Y := G.W) f →
    ∀ (μ : Measure (UA σ G.W.J)) (D : Set (UA σ G.W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ G.W.J) D μ →
      (∀ Ψ ∈ schA F _, ∀ g, th om μ D f Ψ g = th om μ D f Ψ 1) ∧ ∀ Ψ ∈ schA F _, ∀ g, th om' μ D f Ψ g = th om' μ D f Ψ 1

end PositivityTheory.ThKEnd.Orth

end
