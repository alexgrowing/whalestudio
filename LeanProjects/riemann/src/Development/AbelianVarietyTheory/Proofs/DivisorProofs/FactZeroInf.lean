import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf

noncomputable section

namespace GlobalTheory.ThK.RealB

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def coneB (B : Base F E) {a b : ℕ} (G : Geo σ a (b + 2)) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b))
    (om' : Rep σ G.V' G.W) (ei' : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
    (K : Subgroup (UA σ G.V'.J)) (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F))) (ν : Chr F E) :
    SInf F (Fin (b + 2) × Fin (a + (b + 2))) → SInf F (Fin b × Fin (a + b)) :=
  coneInf B G.M' om' ei' K μK μ (shiftB σ H H') ν ((a - (b + 2)) / 2 + 1)

def FactZeroInf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (R : RealMaps F a (b + 2)) (R₁ : RealMaps F a b) e, IsEv B G.M G₁.M 1 H'.ι (iso0 a H') e →
    ∀ ei ev, LemF.IsLocPart G.M G₁.M e ei ev →
    ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∃ lam : R.Pi →ₗ[ℂ] R₁.Pi, ∀ f ∈ G.M.Pol B.ψ B.emb, R₁.p (ei f) = lam (R.p f)

def FactConeInf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (R : RealMaps F a (b + 2)) (R₁ : RealMaps F a b) e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ ei' ev', LemF.IsLocPart G.M' G₁.M' e' ei' ev' → ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K →
    ∀ (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F))), μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∃ mu : R.Pi →ₗ[ℂ] R₁.Pi, ∀ f' ∈ G.M'.Pol B.ψ B.emb, R₁.p' (coneB B G H H' om' ei' K μK μ X.ν f') = mu (R.p' f')

def FrobZeroInf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (R : RealMaps F a (b + 2)) (R₁ : RealMaps F a b) e, IsEv B G.M G₁.M 1 H'.ι (iso0 a H') e →
    ∀ ei ev, LemF.IsLocPart G.M G₁.M e ei ev →
    ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
    ∀ lam : R.Pi →ₗ[ℂ] R₁.Pi, (∀ f ∈ G.M.Pol B.ψ B.emb, R₁.p (ei f) = lam (R.p f)) →
      IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.β ((a : ℝ) / 2) lam

def FrobConeInf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (R : RealMaps F a (b + 2)) (R₁ : RealMaps F a b) e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ ei' ev', LemF.IsLocPart G.M' G₁.M' e' ei' ev' → ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K →
    ∀ (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F))), μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
    ∀ mu : R.Pi →ₗ[ℂ] R₁.Pi, (∀ f' ∈ G.M'.Pol B.ψ B.emb, R₁.p' (coneB B G H H' om' ei' K μK μ X.ν f') = mu (R.p' f')) →
      IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.β ((a : ℝ) / 2) mu

def NeZeroInf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (R : RealMaps F a (b + 2)) (R₁ : RealMaps F a b) e, IsEv B G.M G₁.M 1 H'.ι (iso0 a H') e →
    ∀ ei ev, LemF.IsLocPart G.M G₁.M e ei ev →
    ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∃ f ∈ G.M.Pol B.ψ B.emb, R₁.p (ei f) ≠ 0

def NeConeInf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (R : RealMaps F a (b + 2)) (R₁ : RealMaps F a b) e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ ei' ev', LemF.IsLocPart G.M' G₁.M' e' ei' ev' → ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K →
    ∀ (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F))), μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∃ f' ∈ G.M'.Pol B.ψ B.emb, R₁.p' (coneB B G H H' om' ei' K μK μ X.ν f') ≠ 0

def WeilInfLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X X₂ : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₂ : Rep σ G.V G.W)
    (om₂' : Rep σ G.V' G.W), IsTriple B G X om om' → IsTriple B G X₂ om₂ om₂' →
    (∀ k ∈ UAt σ G.V (evI F), ∀ f : SInf F (Fin a × Fin (a + a')), locOpInf (om (k, 1)) f = locOpInf (om₂ (k, 1)) f) ∧
    ∀ k ∈ UAt σ G.V' (evI F), ∀ f : SInf F (Fin a' × Fin (a + a')), locOpInf (om' (k, 1)) f = locOpInf (om₂' (k, 1)) f

def RealConstB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (R : RealMaps F a (b + 2)) (R₁ : RealMaps F a b) e, IsEv B G.M G₁.M 1 H'.ι (iso0 a H') e →
    ∀ ei ev, LemF.IsLocPart G.M G₁.M e ei ev → ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ ei' ev', LemF.IsLocPart G.M' G₁.M' e' ei' ev' → ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K →
    ∀ (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F))), μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∃ (lam : R.Pi →ₗ[ℂ] R₁.Pi) (u : ℂ), u ≠ 0 ∧ ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B G X om om' R Rf →
      IsMatched B G₁ X om₁ om₁' R₁ Rf₁ → (∀ f ∈ G.M.Pol B.ψ B.emb, R₁.p (ei f) = lam (R.p f)) ∧
        ∀ f' ∈ G.M'.Pol B.ψ B.emb, R₁.p' (coneB B G H H' om' ei' K μK μ X.ν f') = u • lam (R.p' f')

end GlobalTheory.ThK.RealB

end
