import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart

noncomputable section

namespace GlobalTheory.ThK.RealA

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def coneA (B : Base F E) {b a' : ℕ} (G : Geo σ (b + 2) a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (om : Rep σ G.V G.W) (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
    (K : Subgroup (UA σ G.V.J)) (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F))) (ν : Chr F E) :
    SInf F (Fin (b + 2) × Fin (b + 2 + a')) → SInf F (Fin b × Fin (b + a')) :=
  coneInf B G.M om ei K μK μ (shiftA H H') ν ((b + 2 - a') / 2)

def FrobConeA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (R : RealMaps F (b + 2) a') (R₁ : RealMaps F b a') e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ ei ev, LemF.IsLocPart G.M G₁.M e ei ev → ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F))), μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
    ∀ A : R.Pi →ₗ[ℂ] R₁.Pi, (∀ f ∈ G.M.Pol B.ψ B.emb, R₁.p (coneA B G H H' om ei K μK μ X.ν f) = A (R.p f)) →
      IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.α ((a' : ℝ) / 2) A

def FrobZeroA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (R : RealMaps F (b + 2) a') (R₁ : RealMaps F b a') e', IsEv B G.M' G₁.M' 1 H'.ι (iso0 a' H') e' →
    ∀ ei' ev', LemF.IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
    ∀ A' : R.Pi →ₗ[ℂ] R₁.Pi, (∀ f' ∈ G.M'.Pol B.ψ B.emb, R₁.p' (ei' f') = A' (R.p' f')) →
      IsFrobInf B G.M G₁.M om om₁ R.p R₁.p H' X.α ((a' : ℝ) / 2) A'

def NeConeA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (R : RealMaps F (b + 2) a') (R₁ : RealMaps F b a') e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ ei ev, LemF.IsLocPart G.M G₁.M e ei ev → ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F))), μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∃ f ∈ G.M.Pol B.ψ B.emb, R₁.p (coneA B G H H' om ei K μK μ X.ν f) ≠ 0

def NeZeroA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (R : RealMaps F (b + 2) a') (R₁ : RealMaps F b a') e', IsEv B G.M' G₁.M' 1 H'.ι (iso0 a' H') e' →
    ∀ ei' ev', LemF.IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∃ f' ∈ G.M'.Pol B.ψ B.emb, R₁.p' (ei' f') ≠ 0

def RealConstA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (R : RealMaps F (b + 2) a') (R₁ : RealMaps F b a') e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ ei ev, LemF.IsLocPart G.M G₁.M e ei ev → ∀ e', IsEv B G.M' G₁.M' 1 H'.ι (iso0 a' H') e' →
    ∀ ei' ev', LemF.IsLocPart G.M' G₁.M' e' ei' ev' → ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F))), μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∃ (lam : R.Pi →ₗ[ℂ] R₁.Pi) (u : ℂ), u ≠ 0 ∧ ∀ X om om' Rf om₁ om₁' Rf₁, IsMatched B G X om om' R Rf →
      IsMatched B G₁ X om₁ om₁' R₁ Rf₁ → (∀ f ∈ G.M.Pol B.ψ B.emb, R₁.p (coneA B G H H' om ei K μK μ X.ν f) = lam (R.p f)) ∧
        ∀ f' ∈ G.M'.Pol B.ψ B.emb, R₁.p' (ei' f') = u⁻¹ • lam (R.p' f')

end GlobalTheory.ThK.RealA

end
