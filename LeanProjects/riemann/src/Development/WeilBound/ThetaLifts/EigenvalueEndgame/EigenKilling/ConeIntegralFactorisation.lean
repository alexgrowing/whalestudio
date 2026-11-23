import Development.WeilBound.ThetaLifts.EigenvalueEndgame.PlaneRemovalConfiguration
import Development.WeilBound.ThetaLifts.SmallCones.ThetaKernelGeneralIdentity
import Development.WeilBound.ThetaLifts.FrameEstimates.HodgeTateFromSandwich
import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical

noncomputable section

namespace PositivityTheory.ThKEnd.Comp

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKF PositivityTheory.ThKG.Loc

def BigAny : Prop := PositivityTheory.ThKCT.AnySplit (fun n d r s => ∃ z, 2 * n = d + 2 * z ∧ min r s + 1 ≤ z) false

def SmallAny : Prop := PositivityTheory.ThKCT.AnySplit (fun n d _ _ => ∃ z, d + 2 = 2 * n + 2 * z ∧ 2 ≤ z) true

def RealVanish : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ m : InfinitePlace F → ℤ, HasExp B.emb χW m → (∀ w, (d : ℤ) < |m w|) → min r' s' < min r s →
    ∀ L : SInf F (Fin n × Fin d) →L[ℂ] ℂ, (∀ g ∈ UAt σ X (evI F), ∀ T, IsArchOp om (g, 1) T → ∀ f, L (T f) = L f) → L = 0

def SoLower : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁)
    (M : Model σ X W) (M₁ : Model σ X W₁) (χX χW : Chr F E) (om : Rep σ X W) (om₁ : Rep σ X W₁) (r s r' s' r₁ s₁ : ℕ)
    (H' : Plane E d d₁) (i₀ i₁ : ℕ), IsPair B M χX χW om r s r' s' → IsPair B M₁ χX χW om₁ r s r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    1 ≤ n → 1 ≤ d₁ → (∀ t : E →ₐ[F] Fv F B.v₁, chrW χW t ≠ 1) →
    ∀ e ei ev, IsEv B M M₁ 1 H'.ι (iso0 n H') e → IsEvLoc M M₁ e ei ev →
    ∀ φ ∈ M.SoLoc B.ψ B.τ₁, ∃ φ' ∈ M.SoLoc B.ψ B.τ₁, φ - φ' ∈ augOn om B.v₁ (M.SoLoc B.ψ B.τ₁) ∧ ev B.v₁ φ' ∈ M₁.SoLoc B.ψ B.τ₁

open Classical in

def ConeIntegralFactorisation : Prop :=
  ∃ e₁ e₂ : ℤˣ, ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), PlaneRemovalConfiguration B G G₁ H H' →
    ∀ e ei ev, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → IsEvLoc G.M G₁.M e ei ev →
    ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ) (m : LocMeas K), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → m.Is →
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∃ (L : SInf F _ →L[ℂ] SInf F _) (Λ : ∀ v : Pl F, Fl F v _ _ →ₗ[ℂ] Fl F v _ _) (u : Pl F → ℂ),
        IsConeI B G.M om m ei (shiftA H H') X.ν ((b + 2 - a') / 2) L ∧ (∀ f ∈ G.M.Pol B.ψ B.emb, L f ∈ G₁.M.Pol B.ψ B.emb) ∧
        (∀ v, ∀ φ ∈ SB _, Λ v φ = coneF B G.M om m v (ev v) (shiftA H H') X.ν ((b + 2 - a') / 2) φ ∧ Λ v φ ∈ SB _) ∧
        (∀ v ∉ X.T, u v ≠ 0 ∧ Λ v (G.M.vac v) = u v • G₁.M.vac v) ∧
        (∀ Φ ∈ schA F _, ∀ Ψ ∈ schA F _, ∀ c : ℂ, cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (Φ + c • Ψ) =
          cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Φ + c • cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Ψ) ∧
        ∀ T : Finset (Pl F), X.T ⊆ T → ∀ (f : SInf F _) φ, (∀ v, φ v ∈ SB _) → (∀ v ∉ T, φ v = G.M.vac v) →
          (∏ v ∈ T \ X.T, u v) • cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (pure f φ) =
            (κ * ((idealVal X.ν H.𝔟 ^ (e₁ : ℤ) * idealVal X.ν H'.𝔟 ^ (e₂ : ℤ) : ℂˣ) : ℂ) * charL X.ν (X.S₀ : Set (Pl F)) ((((b + 2 - a') / 2) : ℕ) : ℂ)) •
              pure (L f) fun v => if v ∈ T then Λ v (φ v) else G₁.M.vac v

def ConePol : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')),
    PlaneRemovalConfiguration B G G₁ H H' → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ ∈ PolData B G.M, cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Φ ∈ PolData B G₁.M

def PolStab : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ k ∈ FinK σ B G.W,
    (∀ Φ ∈ PolData B G.M, om (1, k) Φ ∈ PolData B G.M) ∧
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, om' (1, k) Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁

def SoMove : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) i₀ i₁ (M₁ : Model σ G.V' W₁) om₁ r₁ s₁, H'.IsAdapted σ B G.W W₁ i₀ i₁ →
    IsPair B M₁ X.α (X.α / X.β) om₁ G.q (a' - G.q) r₁ s₁ → ∀ e, IsEv B G.M' M₁ 1 H'.ι (iso0 a' H') e →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∃ Ψ ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      G.M'.I om' Ψ = G.M'.I om' Φ' ∧ e Ψ ∈ M₁.So B.ψ B.τ₁

def IZero : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ m : InfinitePlace F → ℤ, HasExp B.emb χW m → (∀ w, (d : ℤ) < |m w|) → min r' s' < min r s →
    (d + 2 * min r s < 2 * n → ∀ Φ ∈ schA F _, M.I om Φ = 0) ∧ ∀ Φ ∈ M.So B.ψ B.τ₁, M.I om Φ = 0

end PositivityTheory.ThKEnd.Comp

end
