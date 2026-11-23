import Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.SigThConst
import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj

noncomputable section

namespace PositivityTheory.ThKEnd.Orth

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Notions

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

variable (σ W) in

def FinPts : Set (UA σ W.J) := UAt σ W (fun a : AF F => a.2)

variable (W) in

structure Smooth (f : UA σ W.J → ℂ) : Prop where
  aut : IsAut f
  level : ∃ U ∈ 𝓝 (1 : UA σ W.J), ∀ k ∈ U, k ∈ FinPts σ W → ∀ g, f (g * k) = f g
  smooth : ∀ (k : ℕ) (γ : Fin k → Multiplicative ℝ →* UA σ W.J), (∀ i, γ i ∈ Lines σ W) → ∀ g,
    ContDiff ℝ (⊤ : ℕ∞) fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (Multiplicative.ofAdd (t i))).prod)
  growth : ∃ (N : ℕ) (𝒞 : Set (UA σ W.J → ℂ)), f ∈ 𝒞 ∧ ∀ φ ∈ 𝒞, (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C * (ht g : ℝ) ^ N) ∧
    ∀ γ ∈ Lines σ W, ∃ φ₁ ∈ 𝒞, ∀ g, HasDerivAt (fun t => φ (g * γ (Multiplicative.ofAdd t))) (φ₁ g) 0

def LocMap (om : Rep σ X W) (v : Pl F) (T : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (UA σ W.J → ℂ)) : Prop :=
  (∀ φ ∈ SB _, IsRapid (Y := W) (T φ)) ∧ ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _,
    Acts (evFin F v) (om (1, h)) φ φ₁ → T φ₁ = fun x => T φ (x * h)

def Comes (om : Rep σ X W) (v : Pl F) (f : UA σ W.J → ℂ) : Prop :=
  ∃ (m : ℕ) (T : Fin m → ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (UA σ W.J → ℂ)) (φ : Fin m → (Fin n × Fin d → Fv F v) → ℂ),
    (∀ i, LocMap om v (T i) ∧ φ i ∈ SB _) ∧ f = ∑ i, T i (φ i)

end Notions

def ArchSmooth : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (k : ℕ) (δ : Fin k → Multiplicative ℝ →* UA σ W.J), (∀ i, δ i ∈ Lines σ W) →
    ∀ T : Fin k → ℝ → SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d),
      (∀ i t, PositivityTheory.ThKF.IsArchOp om (1, δ i (Multiplicative.ofAdd t)) (T i t)) →
      ∀ (f : SInf F (Fin n × Fin d)) (L : SInf F (Fin n × Fin d) →L[ℂ] ℂ),
        ContDiff ℝ (⊤ : ℕ∞) fun t : Fin k → ℝ => L ((List.ofFn fun i => T i (t i)).prod f)

def LevelFix : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∃ U ∈ 𝓝 (1 : UA σ W.J), ∀ k ∈ U, k ∈ FinPts σ W → om (1, k) Φ = Φ

def SigSmooth : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ f ∈ Sig B G om om', Smooth G.W f

def CuspRapid : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d : ℕ) (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ f : UA σ W.J → ℂ, Smooth W f → IsCusp W f → IsRapid (Y := W) f

def LocDecomp : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ f ∈ Sig B G om om', IsRapid (Y := G.W) f →
    ∀ v, X.Good v → v ≠ B.v₁ → Comes om v f ∧ Comes om' v f

def PairLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n' : ℕ) (X' : Spc F E n') (M' : Model σ X' W) (χX' χW' : Chr F E) (om' : Rep σ X' W) (r₁ s₁ : ℕ),
    IsPair B M' χX' χW' om' r₁ s₁ r' s' → n + n' = d → χW = χX / χX' → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), chrW χW t (unifAt v) ≠ 1 →
    ∀ (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) D μ →
    ∀ f, Comes om' v f → ∀ Ψ ∈ schA F _, ∀ u ∈ UAt σ X (evFin F v), ∀ g, th om μ D f Ψ (g * u) = th om μ D f Ψ g

def ThAut : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) D μ →
    ∀ f, IsRapid (Y := W) f → ∀ Ψ ∈ schA F _, Continuous (th om μ D f Ψ) ∧ ∀ γ ∈ ratU σ X.J, ∀ g, th om μ D f Ψ (γ * g) = th om μ D f Ψ g

def ThZero : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → 1 ≤ r → 1 ≤ s → 3 ≤ n → 1 ≤ d →
    (∀ t : E →ₐ[F] Fv F B.v₁, chrW χW t ≠ 1) →
    ∀ (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) D μ →
    ∀ f, IsRapid (Y := W) f → (∀ Ψ ∈ schA F _, ∀ g, th om μ D f Ψ g = th om μ D f Ψ 1) → ∀ Ψ ∈ schA F _, ∀ g, th om μ D f Ψ g = 0

def ThPerp : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ f, IsRapid (Y := W) f → ∀ Ψ ∈ schA F _, M.Conv om Ψ → (∃ (C : ℝ) (k : ℕ), ∀ h, ∫ g in M.dom, ‖theta om Ψ g h‖ ∂M.μ ≤ C * (ht h : ℝ) ^ k) →
    (∀ (μ : Measure (UA σ W.J)) (D : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) D μ → ∀ g, th om μ D f Ψ g = 0) →
    Perp W (M.I om Ψ) f

end PositivityTheory.ThKEnd.Orth

end
