import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2

noncomputable section

open Matrix
open scoped ContDiff

namespace GlobalTheory.TorFin

variable {n : ℕ} {G : Type} [Group G]

def IsUni (J u : Matrix (Fin n) (Fin n) ℂ) : Prop := uᴴ * J * u = J

def IsSkew (J Z : Matrix (Fin n) (Fin n) ℂ) : Prop := Zᴴ * J + J * Z = 0

def IsMulOn (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G) : Prop :=
  ∀ a b, IsUni J a → IsUni J b → s (a * b) = s a * s b

def lineOf (s : Matrix (Fin n) (Fin n) ℂ → G) (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : G := s (NormedSpace.exp (t • Z))

def smLoc (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G) : Submodule ℂ (G → ℂ) where
  carrier := {f | ∀ (k : ℕ) (Z : Fin k → Matrix (Fin n) (Fin n) ℂ), (∀ i, IsSkew J (Z i)) → ∀ g,
    ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => lineOf s (Z i) (t i)).prod)}
  add_mem' := fun hf hf' k Z hZ g => (hf k Z hZ g).add (hf' k Z hZ g)
  zero_mem' := fun _ _ _ _ => contDiff_const
  smul_mem' := fun c _ hf k Z hZ g => (hf k Z hZ g).const_smul c

theorem mem_smLoc {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G} {f : G → ℂ} :
    f ∈ smLoc J s ↔ ∀ (k : ℕ) (Z : Fin k → Matrix (Fin n) (Fin n) ℂ), (∀ i, IsSkew J (Z i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => lineOf s (Z i) (t i)).prod) := Iff.rfl

example (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G) (a : ℂ) : (fun _ => a) ∈ smLoc J s :=
  fun _ _ _ _ => contDiff_const

def IsLieRep {A : Type} [Ring A] [Algebra ℂ A] (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A) : Prop :=
  ∀ X Y, ρ (X * Y - Y * X) = ρ X * ρ Y - ρ Y * ρ X

example : IsLieRep (LinearMap.id : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) := fun _ _ => rfl

def IsRightDer (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G)
    (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)) : Prop :=
  ∀ Z, IsSkew J Z → ∀ (f : smLoc J s) (g : G) (t : ℝ),
    HasDerivAt (fun τ : ℝ => f.1 (g * lineOf s Z τ)) ((ρ Z f).1 (g * lineOf s Z t)) t

def rder (γ : ℝ → G) (φ : G → ℂ) : G → ℂ := fun g => deriv (fun t => φ (g * γ t)) 0

def wop (z : List (ℝ → G) →₀ ℂ) (f : G → ℂ) : G → ℂ := fun g => z.sum fun l c => c * l.foldr rder f g

def invAlg {A : Type} [Ring A] [Algebra ℂ A] (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A) : Subalgebra ℂ A :=
  Algebra.adjoin ℂ (Set.range ρ) ⊓ Subalgebra.centralizer ℂ
    {r | ∃ g g' : Matrix (Fin n) (Fin n) ℂ, g * g' = 1 ∧ ∀ Y, r * ρ Y = ρ (g * Y * g') * r}

theorem mem_invAlg {A : Type} [Ring A] [Algebra ℂ A] {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A} {T : A} :
    T ∈ invAlg ρ ↔ T ∈ Algebra.adjoin ℂ (Set.range ρ) ∧ ∀ r, ∀ g g' : Matrix (Fin n) (Fin n) ℂ, g * g' = 1 →
      (∀ Y, r * ρ Y = ρ (g * Y * g') * r) → r * T = T * r :=
  ⟨fun h => ⟨h.1, fun r g g' h1 h2 => h.2 r ⟨g, g', h1, h2⟩⟩, fun h => ⟨h.1, fun r ⟨g, g', h1, h2⟩ => h.2 r g g' h1 h2⟩⟩

def leftIdl {A : Type} [Ring A] [Algebra ℂ A] (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A) (𝔫 : Set (Matrix (Fin n) (Fin n) ℂ)) :
    Submodule ℂ A :=
  Submodule.span ℂ {a | ∃ Y ∈ 𝔫, ∃ w ∈ Algebra.adjoin ℂ (Set.range ρ), a = ρ Y * w}

def IsIntMod {A : Type} [Ring A] [Algebra ℂ A] (Z : Subalgebra ℂ A) (I : Submodule ℂ A) (H : A) : Prop :=
  ∃ N : ℕ, H ^ N ∈ I ⊔ Submodule.span ℂ {a | ∃ k < N, ∃ z ∈ Z, a = H ^ k * z}

example {A : Type} [Ring A] [Algebra ℂ A] (Z : Subalgebra ℂ A) (I : Submodule ℂ A) {H : A} (h : H ∈ Z) : IsIntMod Z I H :=
  ⟨1, Submodule.mem_sup_right (Submodule.subset_span ⟨0, one_pos, H, h, by simp⟩)⟩

def nilRad (J : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {Y | Y *ᵥ x = 0 ∧ (star x ᵥ* J) ᵥ* Y = 0 ∧ ∀ v, (star x ᵥ* J) ⬝ᵥ v = 0 → ∃ a : ℂ, Y *ᵥ v = a • x}
  add_mem' := fun {Y Y'} h h' => ⟨by rw [add_mulVec, h.1, h'.1, add_zero], by rw [vecMul_add, h.2.1, h'.2.1, add_zero],
    fun v hv => let ⟨a, e⟩ := h.2.2 v hv; let ⟨a', e'⟩ := h'.2.2 v hv; ⟨a + a', by rw [add_mulVec, e, e', add_smul]⟩⟩
  zero_mem' := ⟨zero_mulVec _, vecMul_zero _, fun v _ => ⟨0, by simp⟩⟩
  smul_mem' := fun c Y h => ⟨by rw [smul_mulVec, h.1, smul_zero], by rw [vecMul_smul, h.2.1, smul_zero],
    fun v hv => let ⟨a, e⟩ := h.2.2 v hv; ⟨c * a, by rw [smul_mulVec, e, smul_smul]⟩⟩

theorem mem_nilRad {J Y : Matrix (Fin n) (Fin n) ℂ} {x : Fin n → ℂ} : Y ∈ nilRad J x ↔
    Y *ᵥ x = 0 ∧ (star x ᵥ* J) ᵥ* Y = 0 ∧ ∀ v, (star x ᵥ* J) ⬝ᵥ v = 0 → ∃ a : ℂ, Y *ᵥ v = a • x := Iff.rfl

def projL (J : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ := vecMulVec x (star y ᵥ* J)

def torMat (J : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) (z : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + (z - 1) • projL J x y + ((star z)⁻¹ - 1) • projL J y x

example (J : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) : torMat J x y 1 = 1 := by simp [torMat]

end GlobalTheory.TorFin

end
