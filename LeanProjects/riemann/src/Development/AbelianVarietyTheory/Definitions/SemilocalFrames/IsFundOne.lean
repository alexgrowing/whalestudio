import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure

noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegVol
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def IsReal (H : HermSpace K V) (k r : ℕ) (σ : K →+* ℂ) (Φ : V → Fin (2 * r + k + 1) → ℂ) : Prop :=
  (∀ x y, Φ (x + y) = Φ x + Φ y) ∧ (∀ (c : K) x, Φ (c • x) = σ c • Φ x) ∧
    (∀ x y, herm (Hpk k r) (Φ x) (Φ y) = σ (H.B x y)) ∧ Submodule.span ℂ (Set.range Φ) = ⊤

def IsFrameOf {H : HermSpace K V} {r : ℕ} (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ)
    (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) : Prop :=
  IsReal H k r σ Φ ∧ inWb k r z ∧ inWb k r z' ∧ 0 < Tz k r z ∧ (∃ c : ℂ, IsNormal0 k r N.j_le β c z z' g) ∧
    (∀ a : Fin r, Φ (N.F.e a.castSucc) = ((ρ ^ (r - a.val) : ℝ) : ℂ) • bvec (eI k r a) ∧
      g *ᵥ Φ (N.F'.e a.castSucc) = ((ρ ^ (r - a.val) : ℝ) : ℂ) • bvec (eI k r a)) ∧
    (∀ b : Fin r, N.j ≤ b.val → Φ (N.ist b) = (((ρ ^ (r - b.val))⁻¹ : ℝ) : ℂ) • bvec (esI k r b)) ∧
    Φ N.F.z = z' ∧ g *ᵥ Φ N.F'.z = z

def IsPlaces {ι : Type} (σ : ι → (K →+* ℂ)) : Prop :=
  (∀ v a, σ v (star a) = starRingEnd ℂ (σ v a)) ∧ ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (σ v) = w

def realPts {ι : Type} {k r : ℕ} (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (Γ : Set (V ≃ₗ[K] V)) : Set (ι → Mt k r) :=
  {m | ∃ s ∈ Γ, ∀ v x, Matrix.of (m v) *ᵥ Φ v x = Φ v (s x)}

def mulP {ι : Type} {k r : ℕ} (m x : ι → Mt k r) : ι → Mt k r := fun v => lmulM (Matrix.of (m v)) (x v)

def IsFund {ι : Type} {k r : ℕ} (Γ R Ω : Set (ι → Mt k r)) : Prop :=
  MeasurableSet Ω ∧ ∀ x ∈ R, ∃! m, m ∈ Γ ∧ mulP m x ∈ Ω

def RP {ι : Type} (k r : ℕ) (g : ι → Mat k r) : Set (ι → Mt k r) := {x | ∀ v, Matrix.of (x v) ∈ Rset k r (g v)}

end GlobalTheory.DegVol
