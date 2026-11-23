import Development.WeilBound.ThetaLifts.FrameEstimates.HodgeTateFromSandwich
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.PlaneRemovalConfiguration

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {d : ℕ} {W : Spc F E d}

def IsLie (τ : ∀ w : InfinitePlace F, EmbOver E w) (W : Spc F E d) (Y : InfinitePlace F → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ w, (Y w)ᵀ * W.J.map (τ w).1 + W.J.map (τ w).1 * (Y w).map star = 0

def Gen (τ : ∀ w : InfinitePlace F, EmbOver E w) (W : Spc F E d) (γ : Multiplicative ℝ →* UA σ W.J)
    (Y : InfinitePlace F → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ w (t : ℝ), (mat (γ (Multiplicative.ofAdd t))).map (piInf (τ w)) = NormedSpace.exp ((t : ℂ) • Y w)

variable (W) in

def UMG (f : UA σ W.J → ℂ) : Prop :=
  ∃ (k : ℕ) (S : Set (UA σ W.J → ℂ)), f ∈ S ∧ ∀ f₁ ∈ S, Continuous f₁ ∧ (∃ C : ℝ, ∀ h, ‖f₁ h‖ ≤ C * (ht h : ℝ) ^ k) ∧
    ∀ γ ∈ Lines σ W, ∃ f₂ ∈ S, ∀ h, HasDerivAt (fun t : ℝ => f₁ (h * γ (Multiplicative.ofAdd t))) (f₂ h) 0

variable (W) in

def SmoothFin (τ : ∀ w : InfinitePlace F, EmbOver E w) (f : UA σ W.J → ℂ) : Prop :=
  ∃ U ∈ 𝓝 (1 : UA σ W.J), ∀ u ∈ U, (∀ w, (mat u).map (piInf (τ w)) = 1) → ∀ h, f (h * u) = f h

def LeftInv {J : Matrix (Fin d) (Fin d) E} (f : UA σ J → ℂ) : Prop := ∀ γ ∈ ratU σ J, ∀ h, f (γ * h) = f h

def Rapid {J : Matrix (Fin d) (Fin d) E} (f : UA σ J → ℂ) : Prop := ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C

end

def LineGen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∀ γ ∈ Lines σ W, ∃ Y : InfinitePlace F → Matrix (Fin d) (Fin d) ℂ, IsLie τ W Y ∧ Gen τ W γ Y

def LineEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∀ Y : InfinitePlace F → Matrix (Fin d) (Fin d) ℂ, IsLie τ W Y → ∃ γ ∈ Lines σ W, Gen τ W γ Y ∧ ∀ γ' ∈ Lines σ W, Gen τ W γ' Y → γ' = γ

def LinDer : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∃ (m : ℕ) (β : Fin m → (Multiplicative ℝ →* UA σ W.J)) (c : Fin m → (InfinitePlace F → Matrix (Fin d) (Fin d) ℂ) →ₗ[ℝ] ℝ), (∀ i, β i ∈ Lines σ W) ∧ ∀ (f : UA σ W.J → ℂ) (f' : Fin m → UA σ W.J → ℂ), (∀ i, Continuous (f' i) ∧ ∀ h, HasDerivAt (fun t : ℝ => f (h * β i (Multiplicative.ofAdd t))) (f' i h) 0) → ∀ γ ∈ Lines σ W, ∀ Y, Gen τ W γ Y → ∀ h, HasDerivAt (fun t : ℝ => f (h * γ (Multiplicative.ofAdd t))) (∑ i, (c i Y : ℂ) * f' i h) 0

def UMGSmooth : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∀ f : UA σ W.J → ℂ, UMG W f → ∀ (k : ℕ) (γ : Fin k → (Multiplicative ℝ →* UA σ W.J)), (∀ i, γ i ∈ Lines σ W) → ∀ g, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (Multiplicative.ofAdd (t i))).prod)

def UMGLin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∀ f f' : UA σ W.J → ℂ, UMG W f → UMG W f' → ∀ a b : ℂ, UMG W (a • f + b • f')

def CuspRapid : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) (W : Spc F E d), EpsHerm σ W.J → ∀ f : UA σ W.J → ℂ, LeftInv f → UMG W f → SmoothFin W τ f → PositivityTheory.ThKEnd.IsCusp W f → Rapid f

def Level : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ φ ∈ SB (Fin n × Fin d → Af F), ∃ U ∈ 𝓝 (1 : UA σ W.J), ∀ u ∈ U, (∀ w, (mat u).map (piInf (B.emb w)) = 1) → ∀ f : SInf F (Fin n × Fin d), om (1, u) (pureA F f φ) = pureA F f φ

def IDer : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ 𝓕, Dom M om 𝓕 → ∀ φ ∈ 𝓕, φ ∈ SB _ → ∀ f ∈ M.Pol B.ψ B.emb, (∀ γ ∈ Lines σ W, ∃ f₁ ∈ M.Pol B.ψ B.emb, ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ ∧ ∀ h, HasDerivAt (fun t : ℝ => M.I om (pureA F f φ) (h * γ (Multiplicative.ofAdd t))) (M.I om (pureA F f₁ φ) h) 0) ∧ ∀ γ ∈ Lines σ X, ∃ f₁ ∈ M.Pol B.ψ B.emb, ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ ∧ M.I om (pureA F f₁ φ) = 0

def IInv : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), LeftInv (M.I om Φ) ∧ (∀ g, M.I om (om (g, 1) Φ) = M.I om Φ) ∧ ∀ h h', M.I om (om (1, h') Φ) h = M.I om Φ (h * h')

def IUMG : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ 𝓕, Dom M om 𝓕 → ∀ φ ∈ 𝓕, φ ∈ SB _ → ∀ f ∈ M.Pol B.ψ B.emb, UMG W (M.I om (pureA F f φ)) ∧ SmoothFin W B.emb (M.I om (pureA F f φ))

end PositivityTheory.ThKEst

end
