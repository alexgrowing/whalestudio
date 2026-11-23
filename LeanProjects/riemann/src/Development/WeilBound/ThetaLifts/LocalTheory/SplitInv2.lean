import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical

noncomputable section

namespace PositivityTheory.ThKG.Loc

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def SplitInv2 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ →
    ∀ f, ((∃ Φ ∈ PolData B G.M, f = G.M.I om Φ) ∨
      ∃ Φ' ∈ PolData B G.M', (Φ' ∈ G.M'.So B.ψ B.τ₁ ∨ G.q = 0) ∧ f = G.M'.I om' Φ') →
    ∀ fa fb, Split2 W₁ H' X f fa fb → (∀ u ∈ unip σ G.W H', ∀ h, fa (u * h) = fa h ∧ fb (u * h) = fb h) ∧
      (f = 0 → fa = 0 ∧ fb = 0)

end PositivityTheory.ThKG.Loc

end
