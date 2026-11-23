import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

def Sg2 (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (x : Mat k r) : ℝ :=
  Finset.univ.fold max 1 fun a : Fin (r + 1) => max (lA k r z x a) (lA k r z x a)⁻¹

def Dj (k r : ℕ) {j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) : ℝ :=
  ‖Dmin k r z z' γ ⟨j, by omega⟩‖

def Yj (k r : ℕ) {j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ x : Mat k r) : ℝ :=
  gramProj (Ppos k r z z' γ x) (fun a : Fin j => x⁻¹ *ᵥ (γ⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a)))) / Dj k r hj z z' γ

def XstJ (k r j : ℕ) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  Submodule.span ℂ (Set.range fun a : {a : Fin r // a.val < j} => bvec (esI k r a.1))

def XJ (k r j : ℕ) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  Submodule.span ℂ (Set.range fun a : {a : Fin r // a.val < j} => bvec (eI k r a.1))

def IsNormal0 (k r : ℕ) {j : ℕ} (hj : j ≤ r) (β : Fin r → ℕ) (c : ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) : Prop :=
  g ∈ GG k r ∧ ‖c‖ = 1 ∧ g *ᵥ z' = c • z ∧ Monotone β ∧
    (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) ∧
    (∀ a : Fin r, a.val < j → g⁻¹ *ᵥ bvec (eI k r a) ∈ XstJ k r j ∧ g *ᵥ bvec (eI k r a) ∈ XstJ k r j) ∧
    (∀ a : Fin r, j ≤ a.val → g *ᵥ bvec (eI k r a) = c • bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = c • bvec (esI k r a)) ∧
    BlockAnti (fun a : Fin j => β (Fin.castLE hj a)) ((Zr k r g).submatrix (Fin.castLE hj) (Fin.castLE hj))

abbrev PTop (k r j : ℕ) :=
  ({a : Fin r // j ≤ a.val} → Fin (k + 1) → ℂ) × ({p : UT r // j ≤ p.1.1.val} → ℂ) × ({a : Fin r // j ≤ a.val} → ℝ)

abbrev PSec (k r j : ℕ) :=
  ({a : Fin r // a.val < j} → Fin (k + 1) → ℂ) × ({p : UT r // p.1.1.val < j} → ℂ) × ({a : Fin r // a.val < j} → ℝ)

def pTop (k r j : ℕ) (q : PTop k r j) : Mat k r :=
  pOf k r (fun a => if h : j ≤ a.val then q.1 ⟨a, h⟩ else 0, fun p => if h : j ≤ p.1.1.val then q.2.1 ⟨p, h⟩ else 0,
    fun a => if h : j ≤ a.val then q.2.2 ⟨a, h⟩ else 0)

def pSec (k r j : ℕ) (q : PSec k r j) : Mat k r :=
  pOf k r (fun a => if h : a.val < j then q.1 ⟨a, h⟩ else 0, fun p => if h : p.1.1.val < j then q.2.1 ⟨p, h⟩ else 0,
    fun a => if h : a.val < j then q.2.2 ⟨a, h⟩ else 0)

def rEl (k r j : ℕ) (β : Fin r → ℕ) (q : (UTin β → ℂ) × PTop k r j) : Mat k r := uEmb k r (upperIn β q.1) * pTop k r j q.2

def sEl (k r j : ℕ) (β : Fin r → ℕ) (q : PSec k r j × (UToff β → ℂ)) : Mat k r := pSec k r j q.1 * uEmb k r (upperOff β q.2)

def lebR0 (k r j : ℕ) (β : Fin r → ℕ) : Measure (Mt k r) :=
  (volume : Measure ((UTin β → ℂ) × PTop k r j)).map fun q => Matrix.of.symm (rEl k r j β q)

def IsNormalFormStabilizerMeasure (k r : ℕ) {j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (s : ℝ) (μR : Measure (Mt k r)) : Prop :=
  inWb k r z ∧ inWb k r z' ∧ 0 < Tz k r z ∧
    ∃ n₁ ∈ Nset k r, ∃ n₂ ∈ Nset k r, ∃ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), IsNormal0 k r hj β c z z' g₀ ∧
      γ = n₁ * g₀ * n₂ ∧ μR = (ENNReal.ofReal s • lebR0 k r j β).map (conjM n₂⁻¹)

def Eset0 (k r : ℕ) {j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (R₀ y : ℝ) : Set (Mt k r) :=
  {x | Matrix.of x ∈ GG k r ∧ Sg2 k r z' (Matrix.of x) ≤ R₀ ∧ Sg2 k r z (γ * Matrix.of x) ≤ R₀ ∧
    y < Yj k r hj z z' γ (Matrix.of x) ∧ Yj k r hj z z' γ (Matrix.of x) ≤ 2 * y}

def fibVol0 (k r j : ℕ) (R₀ De y : ℝ) : ℝ :=
  (4 * r : ℝ) ^ (4 * r ^ 2) * (R₀ ^ (2 * r) * De) ^ (8 * r ^ 2) *
    (Real.pi * Real.exp 1 / ((k - 1 - j : ℕ) : ℝ)) ^ (j * (k - 1 - j)) * (2 * y) ^ (2 * (k - 1 - j))

def TailBd {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] (z : Fin (2 * r + k + 1) → ℂ) (νS : Measure (Mt k r))
    (Φ : Mat k r → Wp) (q : ℕ) (H₁ : ℝ) : Prop :=
  ∀ la : ℝ, 0 < la →
    ∫⁻ x, Set.indicator {x : Mt k r | ∃ a : Fin (r + 1), la * H₁ ≤ max (lA k r z (Matrix.of x) a) (lA k r z (Matrix.of x) a)⁻¹}
        (fun x => (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2) x ∂νS ≤
      ENNReal.ofReal (2 * (2 * r + 2 : ℝ) * la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ

def sgV (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (H₁ : ℝ) : ℝ :=
  Finset.univ.fold max 1 fun l : Fin (r + 1) => ‖Dmin k r z z' γ l.castSucc‖ / (2 * H₁) ^ (2 * r)

def degBd (k r j q : ℕ) (H₁ De D sg : ℝ) : ℝ :=
  16 * (4 * r + 4 : ℝ) * (4 * r : ℝ) ^ (4 * r ^ 2) * (2 * H₁) ^ (16 * r ^ 3 + 4 * r) * De ^ (8 * r ^ 2 + 2) *
    (8 * Real.pi * Real.exp 1 / ((k - 1 - j : ℕ) : ℝ)) ^ (j * (k - 1 - j)) * (D ^ (k - 1 - j))⁻¹ *
    sg ^ (-(((q : ℝ) - 16 * r ^ 3 - 4 * r - 1) / r))

example (k : ℕ) (z : Fin (2 * 0 + k + 1) → ℂ) (x : Mat k 0) : 1 ≤ Sg2 k 0 z x := by
  unfold Sg2; exact (Finset.le_fold_max _).2 (Or.inl le_rfl)

end GlobalTheory.Amp
