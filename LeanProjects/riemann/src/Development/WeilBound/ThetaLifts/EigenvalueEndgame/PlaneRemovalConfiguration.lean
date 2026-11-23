import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace PositivityTheory.ThKEnd

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Space

variable {d d₁ : ℕ}

variable (σ) in

structure IsPlane (H : Plane E d d₁) (Y : Spc F E d) (Y₁ : Spc F E d₁) : Prop where
  rank : d = d₁ + 2
  xx : form σ Y.J H.x H.x = 0
  yy : form σ Y.J H.y H.y = 0
  xy : form σ Y.J H.x H.y = 1
  orth : ∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0
  gram : H.ιᵀ * Y.J * H.ι.map σ = Y₁.J
  nondeg : Y₁.J.det ≠ 0

variable (σ) in

def FinK (B : Base F E) (W : Spc F E d) : Set (UA σ W.J) := {k | ∀ w, Commute ((mat k).map (piInf (B.emb w))) (W.θ w)}

def IsAut {W : Spc F E d} (f : UA σ W.J → ℂ) : Prop := Continuous f ∧ ∀ γ ∈ ratU σ W.J, ∀ h, f (γ * h) = f h

variable (σ) in

def unipU (W : Spc F E d) (U : Submodule E (Fin d → E)) : Subgroup (UA σ W.J) :=
  Subgroup.closure {m | (∀ u ∈ U, mat m *ᵥ incV F u = incV F u) ∧ ∀ z : Fin d → E, (∀ u ∈ U, form σ W.J z u = 0) →
    mat m *ᵥ incV F z - incV F z ∈ Submodule.span (AE F E) (incV F '' (U : Set (Fin d → E)))}

def IsCusp (W : Spc F E d) (f : UA σ W.J → ℂ) : Prop :=
  ∀ U : Submodule E (Fin d → E), U ≠ ⊥ → (∀ u ∈ U, ∀ u' ∈ U, form σ W.J u u' = 0) →
    ∀ (μ : Measure (unipU σ W U)) (𝓕 : Set (unipU σ W U)), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ W.J).subgroupOf (unipU σ W U)) 𝓕 μ → ∀ h, ∫ u in 𝓕, f (u.1 * h) ∂μ = 0

def IsLow {W : Spc F E d} {W₁ : Spc F E d₁} (H' : Plane E d d₁) (T : UA σ W.J → ℂ) (k : UA σ W.J) (f₁ : UA σ W₁.J → ℂ) : Prop :=
  ∀ h₁ l, IsLevi H' 1 h₁ l → f₁ h₁ = T (l * k)

def Pure (W : Spc F E d) (χ : Chr F E) (z : ℝ) (f : UA σ W.J → ℂ) : Prop :=
  ∃ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (c : UA σ W.J → ℂ), IsPlane σ H' W W₁ ∧ IsCT H' f c ∧ HasLaw W₁ H' χ z c

def Perp (W : Spc F E d) (g f : UA σ W.J → ℂ) : Prop :=
  ∀ (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ W.J) 𝓕 μ →
    ∫ h in 𝓕, g h * starRingEnd ℂ (f h) ∂μ = 0

end Space

def Sig {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) : Set (UA σ G.W.J → ℂ) :=
  {f | ∃ Φ ∈ PolData B G.M, ∃ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, f = G.M.I om Φ - G.M'.I om' Φ'}

structure PlaneRemovalConfiguration (B : Base F E) {b a' : ℕ} (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')) : Prop where
  eV : G₁.V' = G.V'
  eq : G₁.q = G.q
  ep : G₁.p + 1 = G.p
  hH : H.IsAdapted σ B G.V G₁.V 0 (b + 1)
  hH' : H'.IsAdapted σ B G.W G₁.W 0 (b + 1)

def Iwa : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) i₀ i₁ r s, B.IsGood σ → W.IsSkew σ B r s →
    H'.IsAdapted σ B W W₁ i₀ i₁ → IsPlane σ H' W W₁ ∧ ∀ x : UA σ W.J, ∃ u ∈ unip σ W H', ∃ t m, ∃ (h₁ : UA σ W₁.J), ∃ l, ∃ k ∈ FinK σ B W,
      IsLevi (W₁ := W₁) H' t 1 m ∧ IsLevi H' 1 h₁ l ∧ x = u * (m * (l * k))

def CTBasic : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) r s, B.IsGood σ → W.IsSkew σ B r s → IsPlane σ H' W W₁ →
    (∀ (f g cf cg : UA σ W.J → ℂ) (c : ℂ), IsAut f → IsAut g → IsCT H' f cf → IsCT H' g cg → IsCT H' (f - c • g) (cf - c • cg)) ∧
    ∀ (f T T' : UA σ W.J → ℂ) (χ χ' : Chr F E) (z z' : ℝ), IsAut f → z ≠ z' → IsCT H' f (T + T') → HasLaw W₁ H' χ z T →
      HasLaw W₁ H' χ' z' T' → ∀ u ∈ unip σ W H', ∀ h, T (u * h) = T h ∧ T' (u * h) = T' h

def LineMove : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) r s (χ : Chr F E) (z : ℝ) (f : UA σ W.J → ℂ), B.IsGood σ →
    W.IsSkew σ B r s → IsPlane σ H' W W₁ → IsAut f → Pure W χ z f → ∃ c, IsCT H' f c ∧ HasLaw W₁ H' χ z c

def IAut : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    (∀ Φ ∈ PolData B G.M, IsAut (W := G.W) (G.M.I om Φ)) ∧ ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, IsAut (W := G.W) (G.M'.I om' Φ')

def MatchStab : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a')
    (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → ∀ k ∈ FinK σ B G.W, ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁,
      PolMatch B G X R Rf Φ Φ' → om' (1, k) Φ' ∈ G.M'.So B.ψ B.τ₁ ∧ PolMatch B G X R Rf (om (1, k) Φ) (om' (1, k) Φ')

def SigRe : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ V V' W, IsTriple B (reG G V V' W) X om om' → ∃ h₀ : UA σ G.W.J, ∀ f ∈ Sig B G om om',
      (fun h => f (h * h₀)) ∈ Sig B (reG G V V' W) om om'

def TowerCodimensionTwo : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → 1 ≤ G.p →
    ∃ V V' W, IsTriple B (reG G V V' W) X om om' ∧ ∃ (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')),
      PlaneRemovalConfiguration B (reG G V V' W) G₁ H H' ∧ ∃ om₁ om₁', IsTriple B G₁ X om₁ om₁'

def AlphaZero : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.p = 0 → 1 ≤ G.q →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) i₀ i₁ r s, H'.IsAdapted σ B G.W W₁ i₀ i₁ → W₁.IsSkew σ B r s →
      ∀ f ∈ Sig B G om om', ∀ fa fb, Split2 W₁ H' X f fa fb → fa = 0

def BetaZero : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → G.q = 0 → 1 ≤ G.p →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) i₀ i₁, H'.IsAdapted σ B G.W W₁ i₀ i₁ →
      ∀ f ∈ Sig B G om om', ∀ fa fb, Split2 W₁ H' X f fa fb → fb = 0

def AlphaLow : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → PlaneRemovalConfiguration B G G₁ H H' → 1 ≤ G.q →
    ∀ f ∈ Sig B G om om', ∀ fa fb, Split2 G₁.W H' X f fa fb → ∀ k ∈ FinK σ B G.W, ∃ f₁ ∈ Sig B G₁ om₁ om₁', IsLow H' fa k f₁

def TwoStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → PlaneRemovalConfiguration B G G₁ H H' → 1 ≤ G.q →
    ∀ f ∈ Sig B G om om', ∀ fa, Split2 G₁.W H' X f fa 0 → (∀ k ∈ FinK σ B G.W, ∃ f₁ ∈ Sig B G₁ om₁ om₁', IsLow H' fa k f₁) →
      ∀ k ∈ FinK σ B G.W, ∀ f₁ ∈ Sig B G₁ om₁ om₁', IsLow H' fa k f₁ → Pure G₁.W X.α ((a' : ℝ) / 2) f₁

def CuspOfLine : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁), IsPlane σ H' G.W W₁ → ∀ f ∈ Sig B G om om', IsCT H' f 0 → IsCusp G.W f

def OrthIso : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ f ∈ Sig B G om om', IsCusp G.W f →
    (1 ≤ G.p → ∀ Φ ∈ PolData B G.M, Perp G.W (G.M.I om Φ) f) ∧
    (1 ≤ G.q → ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, Perp G.W (G.M'.I om' Φ') f)

def OrthAn : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ f ∈ Sig B G om om', IsCusp G.W f →
    (G.p = 0 → 1 ≤ G.q → ∀ Φ ∈ PolData B G.M, Perp G.W (G.M.I om Φ) f) ∧
    (G.q = 0 → 1 ≤ G.p → ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, Perp G.W (G.M'.I om' Φ') f)

def PerpZero : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ f ∈ Sig B G om om',
    (∀ Φ ∈ PolData B G.M, Perp G.W (G.M.I om Φ) f) →
    (∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, Perp G.W (G.M'.I om' Φ') f) → f = 0

end PositivityTheory.ThKEnd

end
