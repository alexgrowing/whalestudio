import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors

namespace GlobalTheory.SgGlob

variable {E : Type} [Field E] [NumberField E]

def dInv (E : Type) [Field E] [NumberField E] (j : ℕ) : FractionalIdeal (𝓞 E)⁰ E :=
  ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)⁻¹) ^ j

def SelfDual (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  Λ.FG ∧ ∀ v, v ∈ Λ ↔ ∀ w ∈ Λ, form σ J v w ∈ (algebraMap (𝓞 E) E).range

def frameLat {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) {v | ∃ (b : Fin (r + 1)) (a : E), a ∈ dInv E (r - (b : ℕ)) ∧ v = a • fun i => P i b}

def PrimIn {n : ℕ} (M Λ : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  M ≤ Λ ∧ ∀ v ∈ Λ, v ∈ Submodule.span E (M : Set (Fin n → E)) → v ∈ M

def pairLat {n r : ℕ} (g : ℕ) (P P' : Matrix (Fin n) (Fin (r + 1)) E) :
    Submodule (𝓞 E) (Fin n → E) :=
  frameLat P ⊔ frameLat (((g : E)⁻¹) • (P' - P))

def latMap {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (𝓞 E) (Fin n → E) := Λ.map (γ.mulVecLin.restrictScalars (𝓞 E))

def massOf {G X : Type} (C : Set X) (iso : G → X → X → Prop) : ENNReal :=
  ∑' c : Quot (fun x y : C => ∃ γ, iso γ x.1 y.1),
    (ENat.toENNReal (ENat.card {γ : G // iso γ (Quot.out c).1 (Quot.out c).1}))⁻¹

abbrev Tri (E : Type) [Field E] [NumberField E] (n r : ℕ) : Type :=
  Submodule (𝓞 E) (Fin n → E) × Matrix (Fin n) (Fin (r + 1)) E × Matrix (Fin n) (Fin (r + 1)) E

def GenConf (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T T' : E) (g : ℕ)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Set (Tri E n r) :=
  {x | SelfDual σ J x.1 ∧ (x.2.1, x.2.2) ∈ XZ σ J T T' Z ∧ PrimIn (pairLat g x.2.1 x.2.2) x.1}

def IsoTri (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (γ : Matrix (Fin n) (Fin n) E) (x y : Tri E n r) : Prop :=
  IsUn σ J γ ∧ latMap γ x.1 = y.1 ∧ γ * x.2.1 = y.2.1 ∧ γ * x.2.2 = y.2.2

def Mass (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T T' : E) (g : ℕ)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ENNReal :=
  massOf (GenConf σ J T T' g Z) (IsoTri σ J)

def LzSet (σ : E →+* E) {m : ℕ} (Jb : Matrix (Fin m) (Fin m) E) (T : E) :
    Set (Submodule (𝓞 E) (Fin m → E) × (Fin m → E)) :=
  {x | SelfDual σ Jb x.1 ∧ form σ Jb x.2 x.2 = -T ∧ PrimIn (Submodule.span (𝓞 E) {x.2}) x.1}

def IsoLz (σ : E →+* E) {m : ℕ} (Jb : Matrix (Fin m) (Fin m) E) (γ : Matrix (Fin m) (Fin m) E)
    (x y : Submodule (𝓞 E) (Fin m → E) × (Fin m → E)) : Prop :=
  IsUn σ Jb γ ∧ latMap γ x.1 = y.1 ∧ γ.mulVec x.2 = y.2

def massLz (σ : E →+* E) {m : ℕ} (Jb : Matrix (Fin m) (Fin m) E) (T : E) : ENNReal :=
  massOf (LzSet σ Jb T) (IsoLz σ Jb)

def FrameLats (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P : Matrix (Fin n) (Fin (r + 1)) E) : Set (Submodule (𝓞 E) (Fin n → E)) :=
  {Λ | SelfDual σ J Λ ∧ PrimIn (frameLat P) Λ}

def TotPos (x : E) : Prop := ∀ τ : E →+* ℂ, 0 < (τ x).re

def normInf (x : E) : ℝ := ∏ v : InfinitePlace E, (v.embedding x).re

end GlobalTheory.SgGlob
