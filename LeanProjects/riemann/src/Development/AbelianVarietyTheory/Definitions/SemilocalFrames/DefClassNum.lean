import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HermitianLattices.StatementMass

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagMeas

open Formalism.MainNotions.S GlobalTheory.Count

def sphV (i : ℕ) : ℝ := ∏ l ∈ Finset.Icc 1 i, 2 * Real.pi ^ l / ((l - 1).factorial : ℝ)

def volU (i : ℕ) : ℝ := sphV i * 2 ^ (i * (i - 1) / 2)

def dimN (n : ℕ) {a : ℕ} (j : Fin a → ℕ) : ℕ :=
  4 * (∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k) + 2 * (∑ i, j i) * (n - 2 * ∑ i, j i) + ∑ i, j i ^ 2

def zetaE (E : Type) [Field E] [NumberField E] (l : ℕ) : ℝ := (dedekindZeta E (l : ℂ)).re

def kapBd (E : Type) [Field E] [NumberField E] [StarRing E] (p q : ℕ) {a : ℕ} (j : Fin a → ℕ) : ℝ :=
  Formalism.HermitianLatticesTheory.vInv E ^ (-((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * dimN (p + q) j / 2)) *
    (2 : ℝ) ^ (-((Formalism.HermitianLatticesTheory.fDeg E : ℝ) *
      (((p + q : ℕ) : ℝ) * (∑ i, j i : ℕ) - ((∑ i, j i : ℕ) : ℝ) ^ 2 + ((∑ i, j i : ℕ) : ℝ) / 2))) *
    (sphV p * sphV q / (sphV (p - ∑ i, j i) * sphV (q - ∑ i, j i) * ∏ i, sphV (j i))) ^ Formalism.HermitianLatticesTheory.fDeg E *
    dedekindZeta_residue E ^ a * (∏ i, ∏ l ∈ Finset.Icc 2 (j i), zetaE E l) /
    ∏ M ∈ Finset.Ioc (p + q - 2 * ∑ i, j i) (p + q), Formalism.HermitianLatticesTheory.lValEta E M

def simplexH (a : ℕ) : Set (Fin a → ℝ) := {τ | StrictMono τ ∧ ∀ i, 0 < τ i ∧ τ i < 1 / 2}

def dens (n f : ℕ) {a : ℕ} (j : Fin a → ℕ) (τ : Fin a → ℝ) : ℝ :=
  layerProd n f j τ id * ∏ i, 2 * (f : ℝ) * j i / τ i

def typeSet (I : AutInst) {a : ℕ} (j : Fin a → ℕ) (B : Set (Fin a → ℝ)) : Set I.GA :=
  {x | ∃ τ ∈ B, HasType I x j τ}

def covol {G : Type} [Mul G] [MeasurableSpace G] (Γ : Set G) (μ : Measure G) (A : Set G) : ENNReal :=
  ⨅ (D : Set G) (_ : MeasurableSet D) (_ : ∀ x ∈ A, ∃ γ ∈ Γ, γ * x ∈ D), μ D

def gaugeVol (I : AutInst) (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] : ENNReal :=
  ENNReal.ofReal (∏ v, c v) * covol I.GFset (I.muA μf) Set.univ / μf I.Kset

def SameField (I I' : AutInst) : Prop := ∃ e : I'.E ≃+* I.E, ∀ x, e (star x) = star (e x)

def HasSig (I : AutInst) (p q : ℕ) : Prop := ∀ v, I.pAt v = p ∧ I.qAt v = q

section Real

variable {n : ℕ} {ε : Fin n → Bool}

def IsGaugeSub (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (μ : Measure (Formalism.REAL.UJ ε)) : Prop :=
  μ Sᶜ = 0 ∧ (∀ s ∈ S, μ.map (fun g => s * g) = μ) ∧
    Filter.Tendsto
      (fun r : ℝ => μ {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} / ENNReal.ofReal (r ^ d))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)))

def IsIsoFlag (ε : Fin n → Bool) {a : ℕ} (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) : Prop :=
  W 0 = ⊥ ∧ Monotone W ∧
    (∀ i : Fin a, Module.finrank ℂ (W i.succ) = Module.finrank ℂ (W i.castSucc) + j i) ∧
    ∀ x ∈ W (Fin.last a), ∀ y ∈ W (Fin.last a), star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0

def flagN (ε : Fin n → Bool) {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) : Set (Formalism.REAL.UJ ε) :=
  {g | (∀ i : Fin a, ∀ y ∈ W i.succ, uMat g *ᵥ y - y ∈ W i.castSucc) ∧
    ∀ y : Fin n → ℂ, (∀ x ∈ W (Fin.last a), star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0) →
      uMat g *ᵥ y - y ∈ W (Fin.last a)}

def flagM (ε : Fin n → Bool) {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) : Set (Formalism.REAL.UJ ε) :=
  {g | ∀ i, ∀ y ∈ W i, uMat g *ᵥ y ∈ W i ∧ (uMat g)ᴴ *ᵥ y ∈ W i}

def maxK (ε : Fin n → Bool) : Set (Formalism.REAL.UJ ε) := {g | (uMat g)ᴴ * uMat g = 1}

open Classical in

def detOn (g : Matrix (Fin n) (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) : ℝ :=
  if h : ∀ y ∈ W, Matrix.toLin' g y ∈ W then ‖LinearMap.det ((Matrix.toLin' g).restrict h)‖ else 0

def locSize {a : ℕ} (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ))
    (g : Matrix (Fin n) (Fin n) ℂ) (i : Fin a) : ℝ :=
  (detOn g (W i.succ) / detOn g (W i.castSucc)) ^ (-(1 : ℝ) / j i)

end Real

section GenLin

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def MatInf : Type := InfinitePlace E → Fin j → Fin j → ℂ

instance : MeasurableSpace (MatInf E j) := inferInstanceAs (MeasurableSpace (InfinitePlace E → Fin j → Fin j → ℂ))

instance : Mul (MatInf E j) := ⟨fun x y w a b => (Matrix.of (x w) * Matrix.of (y w)) a b⟩

def detNorm (x : MatInf E j) : ℝ := ∏ w, ‖(Matrix.of (x w)).det‖ ^ 2

def haarGL : Measure (MatInf E j) :=
  Measure.withDensity (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ))
    fun x => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j)

def autGL (Λ : Submodule (𝓞 E) (Fin j → E)) : Set (MatInf E j) :=
  {x | ∃ γ : GL (Fin j) E, (∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ ↔ y ∈ Λ) ∧
    ∀ w a b, x w a b = w.embedding ((γ : Matrix (Fin j) (Fin j) E) a b)}

def glVol : ENNReal :=
  ∑' c : Quot (fun Λ Λ' : {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsLattice E Λ} =>
      ∃ γ : GL (Fin j) E, ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1),
    covol (autGL E j (Quot.out c).1) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1}

end GenLin

def defClassNum (E : Type) [Field E] [NumberField E] [StarRing E] (r : ℕ) : ENat :=
  ENat.card (Quot (fun X Y : {X : Matrix (Fin r) (Fin r) E × Submodule (𝓞 E) (Fin r → E) //
      X.1ᴴ = X.1 ∧ (∀ (φ : E →+* ℂ) (y : Fin r → E), y ≠ 0 → 0 < (φ (star y ⬝ᵥ (X.1 *ᵥ y))).re) ∧
      Submodule.IsLattice E X.2 ∧
      ∀ x, x ∈ X.2 ↔ ∀ y ∈ X.2, star y ⬝ᵥ (X.1 *ᵥ x) ∈ (algebraMap (𝓞 E) E).range} =>
    ∃ γ : GL (Fin r) E, (γ : Matrix (Fin r) (Fin r) E)ᴴ * Y.1.1 * (γ : Matrix (Fin r) (Fin r) E) = X.1.1 ∧
      ∀ y, (γ : Matrix (Fin r) (Fin r) E) *ᵥ y ∈ Y.1.2 ↔ y ∈ X.1.2))

end GlobalTheory.FlagMeas
