import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def augInf (B : Base F E) (M : Model σ X W) (om : Rep σ X W) : Submodule ℂ (SInf F (Fin n × Fin d)) :=
  Submodule.span ℂ {z | ∃ f ∈ M.Pol B.ψ B.emb,
    (∃ γ ∈ Lines σ X, ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f z) ∨
      ∃ k ∈ KInf σ X B.emb, ∃ f₁ : SInf F _, Acts (evI F) (om (k, 1)) f f₁ ∧ z = f₁ - f}

def augOn (om : Rep σ X W) (v : Pl F) (S : Set ((Fin n × Fin d → Fv F v) → ℂ)) : Submodule ℂ ((Fin n × Fin d → Fv F v) → ℂ) :=
  Submodule.span ℂ {z | ∃ g ∈ UAt σ X (evFin F v), ∃ φ ∈ S, ∃ φ₁ ∈ SB _, Acts (evFin F v) (om (g, 1)) φ φ₁ ∧ z = φ₁ - φ}

def IsArchOp (om : Rep σ X W) (x : UA σ X.J × UA σ W.J) (T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)) : Prop :=
  (∀ f : SInf F (Fin n × Fin d), ∀ φ ∈ SB (Fin n × Fin d → Af F), om x (pureA F f φ) = pureA F (T f) φ) ∧
    ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om x) f (T f)

def ArchOp : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∃ T, IsArchOp om (g, h) T ∧
      (g ∈ KInf σ X B.emb → h ∈ KInf σ W B.emb → ∀ f ∈ M.Pol B.ψ B.emb, T f ∈ M.Pol B.ψ B.emb)

def ArchLie : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ γ ∈ Lines σ X, ∀ δ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d),
      (∀ t, IsArchOp om (γ (Multiplicative.ofAdd t), δ (Multiplicative.ofAdd t)) (T t)) →
      ∀ f ∈ M.Pol B.ψ B.emb, ∃ f₁ ∈ M.Pol B.ψ B.emb,
        ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), δ (Multiplicative.ofAdd t))) f f₁ ∧
        ∀ L : SInf F (Fin n × Fin d) →L[ℂ] ℂ, HasDerivAt (fun t => L (T t f)) (L f₁) 0

def ICont : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    (d + 2 * min r s < 2 * n ∨ min r s = 0 → ∀ Φ ∈ schA F _, Continuous (M.I om Φ)) ∧
      ((∀ x, ∀ Φ ∈ M.So B.ψ B.τ₁, om x Φ ∈ M.So B.ψ B.τ₁) → ∀ Φ ∈ M.So B.ψ B.τ₁, Continuous (M.I om Φ))

def Unimod : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ε : ℤˣ), (∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) → J.det ≠ 0 →
      Countable (ratU σ J) ∧ (∃ (μ : Measure (UA σ J)) (𝓕 : Set (UA σ J)), μ.IsHaarMeasure ∧ IsFundamentalDomain (ratU σ J) 𝓕 μ) ∧
      ∀ μ : Measure (UA σ J), μ.IsHaarMeasure → μ.IsMulRightInvariant

def MaxFin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ v : Pl F, ∀ N N', Maximal (fun P => GlobalTheory.Published.ThetaSub om v P ∧ P ≠ SB _) N →
      Maximal (fun P => GlobalTheory.Published.ThetaSub om v P ∧ P ≠ SB _) N' → N = N'

def AdmFin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ v : Pl F, ∀ U ∈ 𝓝 (1 : UA σ W.J), ∃ t : Finset (((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ),
      ∀ l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ, augAt om v ≤ LinearMap.ker l →
        (∀ h ∈ U, h ∈ UAt σ W (evFin F v) → ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ → l φ₁ = l φ) →
        ∃ l' ∈ Submodule.span ℂ (t : Set (((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ)), ∀ φ ∈ SB _, l φ = l' φ

def AdmInf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    (∀ f ∈ M.Pol B.ψ B.emb, ∃ t : Finset (SInf F (Fin n × Fin d)), ∀ k ∈ KInf σ W B.emb, ∀ f₁ : SInf F _,
      Acts (evI F) (om (1, k)) f f₁ → f₁ ∈ Submodule.span ℂ (t : Set _) ⊔ augInf B M om) ∧
    ∀ (m : ℕ) (ρ : UA σ W.J → Module.End ℂ (Fin m → ℂ)), ∃ t : Finset (SInf F (Fin n × Fin d) →ₗ[ℂ] (Fin m → ℂ)),
      ∀ L : SInf F (Fin n × Fin d) →ₗ[ℂ] (Fin m → ℂ), augInf B M om ≤ LinearMap.ker L →
        (∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F _, Acts (evI F) (om (1, k)) f f₁ → L f₁ = ρ k (L f)) →
        ∃ L' ∈ Submodule.span ℂ (t : Set (SInf F (Fin n × Fin d) →ₗ[ℂ] (Fin m → ℂ))), ∀ f ∈ M.Pol B.ψ B.emb, L f = L' f

def SoCoinv : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' →
    ∀ φ ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁), φ ∈ augAt om' B.v₁ → φ ∈ augOn om' B.v₁ (G.M'.SoLoc B.ψ B.τ₁)

def CartanMove : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (X₂ : Spc F E n) (W₂ : Spc F E d) (M₂ : Model σ (reS X X₂) (reS W W₂)), M₂.co = M.co →
      IsPair B M₂ χX χW om r s r' s' → ∀ h ∈ UAt σ W (evI F),
      (∀ w, (mat h).map (piInf (B.emb w)) * W₂.θ w = W.θ w * (mat h).map (piInf (B.emb w))) →
      ∃ g ∈ UAt σ X (evI F), (∀ w, (mat g).map (piInf (B.emb w)) * X₂.θ w = X.θ w * (mat g).map (piInf (B.emb w))) ∧
        ∀ T, IsArchOp om (g, h) T → (M₂.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) = M.Pol B.ψ B.emb

def CartanConj : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d : ℕ) (W W₂ : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s → (reS W W₂).IsSkew σ B r s →
    ∃ h ∈ UAt σ W (evI F), ∀ w, (mat h).map (piInf (B.emb w)) * W₂.θ w = W.θ w * (mat h).map (piInf (B.emb w))

def AbsUnit : Prop :=
  ∀ (Q : Type) [AddCommGroup Q] [Module ℂ Q] (β : Q →ₗ⋆[ℂ] Q →ₗ[ℂ] ℂ) (𝒪 : Set (Module.End ℂ Q)) (A₀ : Submodule ℂ Q),
    (∀ x y, β x y = starRingEnd ℂ (β y x)) → (∀ x, 0 ≤ (β x x).re) → (∀ x ∈ A₀, β x x = 0) →
    (∀ A ∈ 𝒪, ∃ A' ∈ 𝒪, ∃ c : ℂ, ∀ x y, β (A x) y = c * β x (A' y)) →
    (∀ f, ∃ (K : Type) (_ : Group K) (κ : K →* Module.End ℂ Q), (∀ k, κ k ∈ 𝒪) ∧ (∀ k x y, β (κ k x) (κ k y) = β x y) ∧
      (∀ x, ∃ t : Finset Q, ∀ k, κ k x ∈ Submodule.span ℂ (t : Set Q) ⊔ A₀) ∧
      ∀ (m : ℕ) (ρ : K →* Module.End ℂ (Fin m → ℂ)), ((∀ k, κ k f = f) → ∀ k, ρ k = 1) →
        ∃ t : Finset (Q →ₗ[ℂ] (Fin m → ℂ)), ∀ L : Q →ₗ[ℂ] (Fin m → ℂ), A₀ ≤ LinearMap.ker L →
          (∀ k x, L (κ k x) = ρ k (L x)) → L ∈ Submodule.span ℂ (t : Set _)) →
    ∀ N : Submodule ℂ Q, Maximal (fun P => (A₀ ≤ P ∧ ∀ A ∈ 𝒪, ∀ x ∈ P, A x ∈ P) ∧ P ≠ ⊤) N →
      (∀ N', Maximal (fun P => (A₀ ≤ P ∧ ∀ A ∈ 𝒪, ∀ x ∈ P, A x ∈ P) ∧ P ≠ ⊤) N' → N' = N) → ∀ x ∈ N, β x x = 0

def TensInj : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (vac : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, vac v ≠ 0) →
    (∀ᶠ v in cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ (T : Finset (Pl F)) (m : ℕ) (c : Fin m → ℂ) (f : Fin m → SInf F κ) (φ : Fin m → ∀ v : Pl F, (κ → Fv F v) → ℂ),
      (∀ i, ∀ v ∉ T, φ i v = vac v) → ∑ i, c i • pure (f i) (φ i) = 0 →
      ∑ i, c i • f i ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => φ i v) = 0

def PureAct : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl F) (S : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ), (∀ u, φ u ∈ SB _) →
    (∀ᶠ u in cofinite, φ u = Set.indicator {x | ∀ i, x i ∈ u.adicCompletionIntegers F} 1) →
    (∃ ψ ∈ SB (κ → Af F), ∀ f' : SInf F κ, pure f' φ = pureA F f' ψ) ∧
    (∀ φ₁ φ₂ (a : ℂ), pure f (by classical exact Function.update φ v (φ₁ + a • φ₂)) =
      pure f (by classical exact Function.update φ v φ₁) + a • pure f (by classical exact Function.update φ v φ₂)) ∧
    ∀ φ₁, Acts (evFin F v) S (φ v) φ₁ → S (pure f φ) = pure f (by classical exact Function.update φ v φ₁)

def ArchUniq : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (f f₁ f₂ : SInf F κ),
    (∀ S, Acts (evI F) S f f₁ → Acts (evI F) S f f₂ → f₁ = f₂) ∧
    ∀ S, ActsD (evI F) S f f₁ → ActsD (evI F) S f f₂ → f₁ = f₂

def Kills : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
    (∀ f ∈ G.M.Pol B.ψ B.emb, ∀ φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) →
      (R.p f = 0 ∨ ∃ v, Rf.p v (φ v) = 0) → G.M.I om (pure f φ) = 0) ∧
    ∀ f ∈ G.M'.Pol B.ψ B.emb, ∀ φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
      φ B.v₁ ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁) → (R.p' f = 0 ∨ ∃ v, Rf.p' v (φ v) = 0) → G.M'.I om' (pure f φ) = 0

end PositivityTheory.ThKF

end
