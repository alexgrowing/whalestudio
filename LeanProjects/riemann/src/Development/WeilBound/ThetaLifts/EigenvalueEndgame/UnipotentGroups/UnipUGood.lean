import Development.WeilBound.ThetaLifts.EigenvalueEndgame.PlaneRemovalConfiguration

noncomputable section

namespace PositivityTheory.ThKEnd.Grp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

structure UnipGood {d : ℕ} {J : Matrix (Fin d) (Fin d) E} (N : Subgroup (UA σ J)) : Prop where
  closed : IsClosed (N : Set (UA σ J))
  lc : LocallyCompactSpace N
  sc : SecondCountableTopology N
  cnt : Countable ((ratU σ J).subgroupOf N)
  cov : ∃ C : Set N, IsCompact C ∧ ∀ u : N, ∃ γ : N, γ.1 ∈ ratU σ J ∧ γ * u ∈ C
  ex : ∃ (μ : Measure N) (𝓕 : Set N), μ.IsHaarMeasure ∧ IsFundamentalDomain ((ratU σ J).subgroupOf N) 𝓕 μ ∧ μ 𝓕 = 1
  dom : ∀ μ : Measure N, μ.IsHaarMeasure → ∃ 𝓕 : Set N, MeasurableSet 𝓕 ∧ IsFundamentalDomain ((ratU σ J).subgroupOf N) 𝓕 μ
  right : ∀ μ : Measure N, μ.IsHaarMeasure → μ.IsMulRightInvariant
  fin : ∀ (μ : Measure N) (𝓕 : Set N), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ J).subgroupOf N) 𝓕 μ → μ 𝓕 ≠ 0 ∧ μ 𝓕 < ⊤

def UnipUGood : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (d : ℕ) (W : Spc F E d), ((∀ i j, σ (W.J j i) = W.J i j) ∨ ∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
    ∀ U : Submodule E (Fin d → E), UnipGood (unipU σ W U) ∧ ∀ m, m ∈ unipU σ W U ↔ (∀ u ∈ U, mat m *ᵥ incV F u = incV F u) ∧
      ∀ z : Fin d → E, (∀ u ∈ U, form σ W.J z u = 0) →
        mat m *ᵥ incV F z - incV F z ∈ Submodule.span (AE F E) (incV F '' (U : Set (Fin d → E)))

def UnipLine : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H : Plane E d d₁),
    ((∀ i j, σ (W.J j i) = W.J i j) ∨ ∀ i j, σ (W.J j i) = -W.J i j) → IsPlane σ H W W₁ →
    unip σ W H = unipU σ W (Submodule.span E {H.x})

def LeviPlane : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H : Plane E d d₁), (∀ i j, σ (W.J j i) = -W.J i j) → IsPlane σ H W W₁ →
    (∀ t (h₁ : UA σ W₁.J), ∃ m : UA σ W.J, IsLevi H t h₁ m) ∧
    ∀ t (h₁ : UA σ W₁.J) (m : UA σ W.J), IsLevi H t h₁ m → ∀ u ∈ unip σ W H, m * u * m⁻¹ ∈ unip σ W H

def WittVec : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (d : ℕ) (J : Matrix (Fin d) (Fin d) E), (∀ i j, σ (J j i) = -J i j) → J.det ≠ 0 → ∀ x x' : Fin d → E, x ≠ 0 → x' ≠ 0 →
    form σ J x x = 0 → form σ J x' x' = 0 → ∃ g : GL (Fin d) E, g.1ᵀ * J * g.1.map σ = J ∧ g.1 *ᵥ x = x'

def Decomp : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ k ∈ FinK σ B G.W, ∀ Φ ∈ schA F _, ∀ Φ' ∈ schA F _,
    ∃ k₀ ∈ KInf σ G.W B.emb, ∃ (l : List (UA σ G.W.J)) (r : UA σ G.W.J), (∀ h ∈ l, ∃ v, h ∈ UAt σ G.W (evFin F v)) ∧
      k = k₀ * l.prod * r ∧ om (1, r) Φ = Φ ∧ om' (1, r) Φ' = Φ'

end PositivityTheory.ThKEnd.Grp

end
