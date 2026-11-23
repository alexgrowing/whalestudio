import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure

noncomputable section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg

namespace GlobalTheory.SteepMult

variable {R S : ℕ}

abbrev NC (R S : ℕ) : Type := {x : Ix R S × Ix R S // ¬ sameBlock x.1 x.2}

def eNC (x : NC R S) : Mat R S := Eab x.1.1 x.1.2

def adP (Z : Mat R S) (y x : NC R S) : ℂ :=
  Z y.1.1 x.1.1 * (if y.1.2 = x.1.2 then 1 else 0) - (if y.1.1 = x.1.1 then 1 else 0) * Z x.1.2 y.1.2

lemma adCoeff_add (Z Z' : Mat R S) (y x : NC R S) : adP (Z + Z') y x = adP Z y x + adP Z' y x := by
  simp only [adP, Matrix.add_apply]; ring

lemma adCoeff_smul (c : ℂ) (Z : Mat R S) (y x : NC R S) : adP (c • Z) y x = c * adP Z y x := by
  simp only [adP, Matrix.smul_apply, smul_eq_mul]; ring

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def factorOp (k : ℕ) (i : Fin k) (Z : Mat R S) : Module.End ℂ ((Fin k → NC R S) → W) where
  toFun Ψ g := ∑ x, adP Z (g i) x • Ψ (Function.update g i x)
  map_add' Ψ Φ := by ext g; simp [Finset.sum_add_distrib]
  map_smul' c Ψ := by ext g; simp [Finset.smul_sum, smul_comm c]

def tAct (k : ℕ) (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) : Mat R S →ₗ[ℂ] Module.End ℂ ((Fin k → NC R S) → W) where
  toFun Z := LinearMap.pi (fun g => actW Z ∘ₗ LinearMap.proj g) + ∑ i, factorOp k i Z
  map_add' Z Z' := by
    ext Ψ g
    simp [factorOp, adCoeff_add, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c Z := by
    ext Ψ g
    simp [factorOp, adCoeff_smul, mul_smul, Finset.smul_sum]

lemma tAct_apply (k : ℕ) (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (Z : Mat R S) (Ψ : (Fin k → NC R S) → W)
    (g : Fin k → NC R S) :
    tAct k actW Z Ψ g = actW Z (Ψ g) + ∑ i, ∑ x, adP Z (g i) x • Ψ (Function.update g i x) := by
  simp [tAct, factorOp]

def formT (k : ℕ) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) :
    ((Fin k → NC R S) → W) →ₗ⋆[ℂ] ((Fin k → NC R S) → W) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun Ψ Φ => ∑ g, B (Ψ g) (Φ g))
    (fun Ψ Ψ' Φ => by simp [Finset.sum_add_distrib])
    (fun c Ψ Φ => by simp [Finset.mul_sum])
    (fun Ψ Φ Φ' => by simp [Finset.sum_add_distrib])
    (fun c Ψ Φ => by simp [Finset.mul_sum])

lemma formT_apply (k : ℕ) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (Ψ Φ : (Fin k → NC R S) → W) :
    formT k B Ψ Φ = ∑ g, B (Ψ g) (Φ g) := rfl

def IsUnitary (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : Prop :=
  (∀ x y, star (B x y) = B y x) ∧ (∀ x, x ≠ 0 → 0 < (B x x).re) ∧
    ∀ a b, sameBlock a b → ∀ x y, B (actW (Eab a b) x) y = B x (actW (Eab b a) y)

example : IsUnitary (R := 1) (S := 1) (W := ℂ) 0
    (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => star x * y) (fun _ _ _ => by simp [add_mul])
      (fun _ _ _ => by simp [mul_assoc]) (fun _ _ _ => by simp [mul_add]) (fun _ _ _ => by simp; ring)) := by
  refine ⟨fun x y => by simp [mul_comm], fun x hx => ?_, fun a b _ x y => by simp⟩
  have : star x * x = ((Complex.normSq x : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  simp only [LinearMap.mk₂'ₛₗ_apply, this, Complex.ofReal_re]
  exact Complex.normSq_pos.2 hx

def kpart (Z : Mat R S) : Mat R S := Matrix.of fun a b => if sameBlock a b then Z a b else 0

lemma isKC_kpart (Z : Mat R S) : IsKC (kpart Z) := fun a b h => by simp [kpart, h]

lemma kpart_of_isKC {Z : Mat R S} (h : IsKC Z) : kpart Z = Z := by
  ext a b
  by_cases hab : sameBlock a b
  · simp [kpart, hab]
  · simp [kpart, hab, h a b hab]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def restrAct (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) (hN : KStable act N) :
    Mat R S →ₗ[ℂ] Module.End ℂ N where
  toFun Z := (act (kpart Z)).restrict fun x hx => hN _ (isKC_kpart Z) x hx
  map_add' Z Z' := by
    ext x
    have : kpart (Z + Z') = kpart Z + kpart Z' := by ext a b; by_cases h : sameBlock a b <;> simp [kpart, h]
    simp [this]
  map_smul' c Z := by
    ext x
    have : kpart (c • Z) = c • kpart Z := by ext a b; by_cases h : sameBlock a b <;> simp [kpart, h]
    simp [this]

lemma restrAct_apply (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) (hN : KStable act N) (Z : Mat R S)
    (x : N) : (restrAct act N hN Z x : V) = act (kpart Z) x := rfl

def word (act : Mat R S →ₗ[ℂ] Module.End ℂ V) {k : ℕ} (g : Fin k → NC R S) : Module.End ℂ V :=
  (List.ofFn fun i => act (eNC (g i))).prod

def phiN (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) (k : ℕ) :
    ((Fin k → NC R S) → N) →ₗ[ℂ] V :=
  ∑ g, word act g ∘ₗ N.subtype ∘ₗ LinearMap.proj g

lemma phiN_apply (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) (k : ℕ) (Ψ : (Fin k → NC R S) → N) :
    phiN act N k Ψ = ∑ g, word act g (Ψ g) := by
  simp [phiN]

def filt (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) (k : ℕ) : Submodule ℂ V :=
  ⨆ j : Fin (k + 1), LinearMap.range (phiN act N j)

def section1 {k : ℕ} (Ψ : (Fin k → NC R S) → W) (i : Fin k) (g : Fin k → NC R S) : (Fin 1 → NC R S) → W :=
  fun h => Ψ (Function.update g i (h 0))

end GlobalTheory.SteepMult

end
