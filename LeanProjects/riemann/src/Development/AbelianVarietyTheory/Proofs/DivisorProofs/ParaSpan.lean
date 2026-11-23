import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IndLine

def paraSpan {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d d₁ : ℕ} {Y : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) (W₁ : Spc F E d₁)
    (H' : Plane E d d₁) {P : Type} [AddCommGroup P] [Module ℂ P] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) : Submodule ℂ P :=
  sInf {S | lowPartInf B M p ≤ S ∧ ∀ γ ∈ Lines σ W, ((∀ s, γ s ∈ unip σ W H') ∨
      ∃ γ₁ ∈ Lines σ W₁, ∃ t : Multiplicative ℝ →* (AE F E)ˣ, ∀ s, IsLevi H' (t s) (γ₁ s) (γ s)) →
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ → p f ∈ S → p f₁ ∈ S}

end GlobalTheory.IndLine
