import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SuccAboveEqFc
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SpanPrism

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

variable {P Q : Type} [Group P] [Group Q]

abbrev Bi (P Q : Type) (a b : ℕ) : Type := (Fin a → Q) → (Fin b → P) → ℝ

def dh {a b : ℕ} (F : Bi P Q (a + 1) b) : Bi P Q (a + 2) b := fun x y => dc (fun x' => F x' y) x

def dv {a b : ℕ} (F : Bi P Q a (b + 1)) : Bi P Q a (b + 2) := fun x y => dc (F x) y

def PInv (pr : P →* Q) {a b : ℕ} (F : Bi P Q a b) : Prop :=
  ∀ (g : P) x y, F (fun i => pr g * x i) (fun j => g * y j) = F x y

def Ru (u : Q) {a b : ℕ} (F : Bi P Q a b) : Bi P Q a b := fun x y => F (fun i => x i * u) y

def Rt (t : P) {a b : ℕ} (F : Bi P Q a b) : Bi P Q a b := fun x y => F x (fun j => y j * t)

def Tc (t : P) {a b : ℕ} (F : Bi P Q a b) : Bi P Q a b := fun x y => F x (fun j => t⁻¹ * y j * t)

def Hh (u : Q) {a b : ℕ} (F : Bi P Q (a + 1) b) : Bi P Q a b :=
  fun x y => PrismSpan.prism (fun q => q * u) (fun x' => F x' y) x

def Hv (t : P) {a b : ℕ} (F : Bi P Q a (b + 1)) : Bi P Q a b :=
  fun x y => PrismSpan.prism (fun p => p * t) (F x) y

def RuL (u : Q) (a b : ℕ) : Module.End ℝ (Bi P Q a b) where
  toFun := Ru u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def TcL (t : P) (a b : ℕ) : Module.End ℝ (Bi P Q a b) where
  toFun := Tc t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cat {a c : ℕ} (x : Fin a → Q) (z : Fin c → Q) (n : ℕ) : Fin n → Q := fun i =>
  if h : (i : ℕ) < a then x ⟨i, h⟩ else if h' : (i : ℕ) - a < c then z ⟨(i : ℕ) - a, h'⟩ else 1

def zz (pr : P →* Q) {n : ℕ} (b : (Fin n → Q) → ℝ) (a c : ℕ) : Bi P Q a c :=
  fun x y => b (cat x (fun j => pr (y j)) n)

def Wtop (pr : P →* Q) {n : ℕ} (b : (Fin n → Q) → ℝ) : Bi P Q 1 n := fun _ y => b (fun j => pr (y j))

def QC {n : ℕ} (b : (Fin (n + 1) → Q) → ℝ) : Prop :=
  (∀ (g : Q) x, b (fun i => g * x i) = b x) ∧ dc b = 0

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
