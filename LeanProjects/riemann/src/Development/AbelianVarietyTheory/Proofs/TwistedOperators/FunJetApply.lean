import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.RealPlaceAnalysis.QuotientSettingHolds

open Matrix Formalism.REAL Filter Topology
open scoped InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet

variable {n : ℕ}

def actM {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)
    (Z : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ V :=
  ∑ a, ∑ b, Z a b • E a b

def thE (ε : Fin n → Bool) (p : Fin n × Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  -((sgn ε p.1 p.2 : ℝ) : ℂ) • Matrix.single p.2 p.1 (1 : ℂ)

def thM (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ p : Fin n × Fin n, Z p.1 p.2 • thE ε p

def arr1 {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (j : W →ₗᵢ[ℂ] V) (G : Fin n × Fin n → W) : Arr V n 1 :=
  arrTo V n 1 fun α => j (G (α 0))

def Rz {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (Z : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → B) : Matrix (Fin n) (Fin n) ℂ → B :=
  fun z => fderiv ℂ f z (z * Z)

def Rw {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (ε : Fin n → Bool) (l : List (Fin n × Fin n))
    (f : Matrix (Fin n) (Fin n) ℂ → B) : Matrix (Fin n) (Fin n) ℂ → B :=
  l.foldr (fun p g => Rz (thE ε p) g) f

def formOf {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (T : W →ₗ[ℂ] W) : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ :=
  (innerₛₗ ℂ).compl₂ T

@[simp] theorem formOf_apply {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (T : W →ₗ[ℂ] W) (y x : W) :
    formOf T y x = ⟪y, T x⟫_ℂ := rfl

def funJet {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ε : Fin n → Bool)
    (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (l : List (Fin n × Fin n)) : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ :=
  formOf (Rw ε l f 1 : W →L[ℂ] W).toLinearMap

theorem funJet_apply {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ε : Fin n → Bool)
    (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (l : List (Fin n × Fin n)) (y x : W) :
    funJet ε f l y x = ⟪y, Rw ε l f 1 x⟫_ℂ := rfl

def modJet {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (E : Fin n → Fin n → Module.End ℂ V) (j : W →ₗᵢ[ℂ] V) (l : List (Fin n × Fin n)) :
    W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ :=
  ((innerₛₗ ℂ).compl₂ (ew E l ∘ₗ j.toLinearMap)) ∘ₛₗ j.toLinearMap

theorem modJet_apply {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (E : Fin n → Fin n → Module.End ℂ V) (j : W →ₗᵢ[ℂ] V) (l : List (Fin n × Fin n))
    (y x : W) : modJet E j l y x = ⟪j y, ew E l (j x)⟫_ℂ := rfl

section Rel

variable {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
  [InnerProductSpace ℂ W]

def JetRel (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V)
    (B : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : Prop :=
  (∀ (l₁ l₂ : List (Fin n × Fin n)) (a b c d : Fin n),
    B (l₁ ++ (a, b) :: (c, d) :: l₂) - B (l₁ ++ (c, d) :: (a, b) :: l₂) =
      (if b = c then B (l₁ ++ (a, d) :: l₂) else 0) - (if d = a then B (l₁ ++ (c, b) :: l₂) else 0)) ∧
  (∀ (l : List (Fin n × Fin n)) (a b : Fin n), ε a = ε b → ∀ y x x' : W, j x' = E a b (j x) →
    B (l ++ [(a, b)]) y x = B l y x') ∧
  (∀ (l : List (Fin n × Fin n)) (a b : Fin n), ε a = ε b → ∀ y y' x : W, j y' = E b a (j y) →
    B ((a, b) :: l) y x = B l y' x) ∧
  ∀ (l : List (Fin n × Fin n)) (G : Fin n × Fin n → W), arr1 j G ∈ Vminus ε E Λ u →
    ∀ y : W, ∑ p, B (l ++ [p]) y (G p) = 0

theorem JetRel.sub {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {Λ : Fin n → ℝ} {u : V}
    {j : W →ₗᵢ[ℂ] V} {B B' : List (Fin n × Fin n) → W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ} (h : JetRel ε E Λ u j B)
    (h' : JetRel ε E Λ u j B') : JetRel ε E Λ u j (fun l => B l - B' l) := by
  refine ⟨fun l₁ l₂ a b c d => ?_, fun l a b hab y x x' hx => ?_, fun l a b hab y y' x hy => ?_,
    fun l G hG y => ?_⟩
  · have h1 := h.1 l₁ l₂ a b c d
    have h2 := h'.1 l₁ l₂ a b c d
    rw [sub_sub_sub_comm, h1, h2]
    split_ifs <;> (ext y x; simp only [LinearMap.sub_apply, LinearMap.zero_apply]; ring)
  · simp only [LinearMap.sub_apply, h.2.1 l a b hab y x x' hx, h'.2.1 l a b hab y x x' hx]
  · simp only [LinearMap.sub_apply, h.2.2.1 l a b hab y y' x hy, h'.2.2.1 l a b hab y y' x hy]
  · simp only [LinearMap.sub_apply, Finset.sum_sub_distrib, h.2.2.2 l G hG y, h'.2.2.2 l G hG y, sub_self]

def FunEquiv (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (j : W →ₗᵢ[ℂ] V)
    (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) : Prop :=
  ∀ a b : Fin n, ε a = ε b → ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ),
    (∀ x x' : W, j x' = E a b (j x) → fderiv ℂ f z (z * thE ε (a, b)) x = f z x') ∧
    ∀ y y' x : W, j y' = E b a (j y) → ⟪y, fderiv ℂ f z (thE ε (a, b) * z) x⟫_ℂ = ⟪y', f z x⟫_ℂ

def FunSchmid (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V)
    (f : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) : Prop :=
  ∀ G : Fin n × Fin n → W, arr1 j G ∈ Vminus ε E Λ u → ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ),
    ∑ p, fderiv ℂ f z (z * thE ε p) (G p) = 0

def TauTie (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (j : W →ₗᵢ[ℂ] V)
    (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) : Prop :=
  ∀ Y, inK ε Y → ∀ v v' : W, j v' = actM E (Y.map star) (j v) →
    HasDerivAt (fun t : ℝ => τ (NormedSpace.exp ((t : ℂ) • Y)) v) v' 0

def LowData (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V) (j : W →ₗᵢ[ℂ] V) :
    Prop :=
  GlRel E ∧ IsUnitary ε E ∧ KHighest ε E Λ u ∧ FiniteDimensional ℂ (kSpan ε E u) ∧
    LinearMap.range j.toLinearMap = kSpan ε E u

def DerTie {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (E : Fin n → Fin n → Module.End ℂ V) (ι : V →ₗᵢ[ℂ] H) : Prop :=
  ∀ X, inG ε X → ∀ v : V,
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (ι v)) (ι (actM E X v)) 0

end Rel

end GlobalTheory.SphJet
