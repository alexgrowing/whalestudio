import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers

open scoped ComplexOrder

namespace GlobalTheory.HSCore

section Lattice

variable {K : Type} [Field K] [NumberField K]

def diagHerm {κ : Type} [Fintype κ] [DecidableEq κ] (c : (K →+* ℂ) → κ → ℝ) (hc : ∀ σ p, 0 < c σ p) : HermFam K (κ → K) :=
  ofGram (Pi.basisFun K κ) (fun σ => Matrix.diagonal fun p => (((c σ p)⁻¹ ^ 2 : ℝ) : ℂ))
    fun σ => Matrix.PosDef.diagonal fun p => Complex.zero_lt_real.2 (pow_pos (inv_pos.2 (hc σ p)) 2)

def vecHt {n : ℕ} (a : Fin n → K) (c : (K →+* ℂ) → ℝ) : ℝ :=
  ((∑ᶠ v : FinitePlace K, Real.log (⨆ k, v (a k))) + ∑ τ : K →+* ℂ, Real.log (c τ)) / (Module.finrank ℚ K : ℝ)

def prodLat {n δ : ℕ} (j : ℕ) (w : Fin n → Fin δ → K) (Λ : Submodule (𝓞 K) (Fin δ → K)) : Submodule (𝓞 K) (Fin δ → K) :=
  Submodule.span (𝓞 K) {g | ∃ e : Fin j → Fin n, ∃ l ∈ Λ, g = (∏ t, w (e t)) * l}

end Lattice

def HermObject : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (nm : HermFam K V), nm.IsConjInv →
    ∀ (D T n δ : ℕ) (M : Submodule (𝓞 K) V) (U : ℕ → Submodule K V)
      (φ : ∀ a, U a →ₗ[K] (MonoDeg (Fin D) a × Fin δ → K))
      (w : Fin n → Fin δ → K) (Λ : Submodule (𝓞 K) (Fin δ → K))
      (c₁ c₂ : (K →+* ℂ) → Fin δ → ℝ) (r : (K →+* ℂ) → Fin D → ℝ) (h J g β lρ₁ lρ lΛD lΛT C : ℝ)
      (h₂ : ∀ σ p, 0 < c₂ σ p),
      1 ≤ D → D + 1 ≤ T → 1 ≤ δ → 0 ≤ g → 1 ≤ β → 0 ≤ lΛD → 0 ≤ lΛT → 4 ≤ C →
      0 ≤ lρ₁ → lρ₁ ≤ lρ → Real.log D ≤ lρ → 26 * Real.log 2 ≤ lρ → IsFull M → IsFull Λ →
      (∀ σ p, 0 < c₁ σ p) → (∀ σ i, 0 < r σ i) →
      (∀ σ p, c₁ ((starRingEnd ℂ).comp σ) p = c₁ σ p) → (∀ σ p, c₂ ((starRingEnd ℂ).comp σ) p = c₂ σ p) →
      (∀ σ i, r ((starRingEnd ℂ).comp σ) i = r σ i) →
      (∀ p, ∃ k, w k p ≠ 0) → (∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → δ < Ideal.absNorm P) →
      (∀ σ i, r σ i ≤ Real.exp lρ₁) →
      ((D : ℝ) + 1) * h + (∑ i, meanLog K fun σ => r σ i) - g ≤ (∑ p, vecHt (fun k => w k p) fun σ => c₁ σ p) / δ →
      (∑ p, vecHt (fun k => w k p) fun σ => c₁ σ p) / δ ≤ ((D : ℝ) + 1) * h + (∑ i, meanLog K fun σ => r σ i) →
      -((δ : ℝ) * J) - ((D : ℝ) + 3) * (∑ p, vecHt (fun k => w k p) fun σ => c₁ σ p) ≤ deg (diagHerm c₂ h₂) Λ →
      (∀ a < T - D, U (a + 1) ≤ U a ∧ ∀ x : U a, φ a x = 0 ↔ x.1 ∈ U (a + 1)) →
      (∀ a < T - D, ∀ α : MonoDeg (Fin D) a, ∀ γ ∈ prodLat (T - a) w Λ, ∃ f : U a, f.1 ∈ M ∧
        ∀ α' p, φ a f (α', p) = if α'.1 = α.1 then γ p else 0) →
      (∀ a < T - D, ∀ σ, ∀ x : U a, ∀ ε : ℝ, 0 < ε → ∃ y : U a, φ a y = 0 ∧
        nm.nrm σ (x.1 - y.1) ≤
          Real.sqrt (β ^ (T + D + 1) * (34 * cD D) * ((a + D - 1).choose (D - 1) : ℝ) * (∑ i, r σ i ^ 2) ^ D) *
            Real.sqrt (∑ α : MonoDeg (Fin D) a, (∏ i, r σ i ^ α.1 i) ^ 2 *
              ∑ p, ‖σ (φ a x (α, p))‖ ^ 2 / (c₂ σ p * c₁ σ p ^ (T - a)) ^ 2) + ε) →
      (∃ S : Set V, S ⊆ (M : Set V) ∧ S ⊆ (U (T - D) : Set V) ∧
        (∀ x ∈ S, ∀ σ, nm.nrm σ x ≤ Real.exp (((T : ℝ) - D) * (Real.log β / 2 + lρ₁) + lΛD)) ∧
        U (T - D) ≤ Submodule.span K S) →
      (∃ S : Set V, S ⊆ (M : Set V) ∧ (∀ x ∈ S, ∀ σ, nm.nrm σ x ≤ Real.exp lΛT) ∧ Submodule.span K S = ⊤) →
      0 < Module.finrank K V ∧ 0 ≤ 1 - ((T - 1).choose D : ℝ) * δ / (Module.finrank K V : ℝ) ∧
      (1 - (1 - ((T - 1).choose D : ℝ) * δ / (Module.finrank K V : ℝ))) *
          ((T : ℝ) * h - 3 * ((D : ℝ) + 1) * |h| - J - C * (D : ℝ) ^ 2 * (lρ + Real.log T)
            - ((T : ℝ) + D + 1) * Real.log β - ((T : ℝ) + (D : ℝ) ^ 2) * (g + 2))
        - (1 - ((T - 1).choose D : ℝ) * δ / (Module.finrank K V : ℝ)) *
          ((T : ℝ) * (Real.log 2 + lρ + Real.log β / 2) + lΛD + lΛT)
        ≤ deg nm M / (Module.finrank K V : ℝ)

section Geometry

variable {K : Type} [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K)

def filV (a : ℕ) : Submodule K (X.V X.T) := (Fil (X.ideal s) a (spaceV X s)).comap (X.V X.T).subtype

variable {X s}

def symV {hs : X.IsGood s} {δ : ℕ} (Co : Coord X.toGeo hs δ) (a : ℕ) :
    filV X s a →ₗ[K] (MonoDeg (Fin X.D) a × Fin δ → K) :=
  if h : a ≤ X.T then
    (LinearMap.pi fun q : MonoDeg (Fin X.D) a × Fin δ =>
      (LinearMap.proj q.2 : (Fin δ → K) →ₗ[K] K) ∘ₗ (Co.ev (X.T - a)).toLinearMap ∘ₗ LinearMap.proj q.1) ∘ₗ
      hs.sym (Nat.sub_add_cancel h) (spaceV X s) ∘ₗ (X.V X.T).subtype.restrict fun _ hx => hx
  else 0

def Coord.gen {G : Geo K} {s : Fin G.D → Fin G.N → K} {hs : G.IsGood s} {δ : ℕ} (Co : Coord G hs δ) (k : Fin G.n) (p : Fin δ) : K :=
  ∑ j, G.w j k * Co.y p j

def Coord.c₁ {G : Geo K} {s : Fin G.D → Fin G.N → K} {hs : G.IsGood s} {δ : ℕ} (Co : Coord G hs δ) (σ : K →+* ℂ) (p : Fin δ) : ℝ :=
  archSize (G.A σ) fun k => σ (Co.y p k)

def resCo {hs : X.IsGood s} {δ : ℕ} (Co : Coord X.toGeo hs δ) : Submodule (𝓞 K) (Fin δ → K) :=
  (X.resLat hs).map ((Co.ev 0).toLinearMap.restrictScalars (𝓞 K))

variable (X) in

structure Stable : Prop where
  nef : IsNef K X.LA
  big : IsBig K X.LA
  mulStable : X.MulStable
  mulBound : ∀ σ, X.MulBoundAt σ X.beta
  integralBound : X.IntegralBound (fun _ => X.beta) fun _ => 1
  shortD : X.ShortFamily X.D X.LamD
  shortT : X.ShortFamily X.T X.LamT

end Geometry

def RegSeq {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (F : Y.Modules) (t : List L.Sec) : Prop :=
  List.rec (motive := fun _ => Y.Modules → Prop) (fun _ => True)
    (fun a _ ih G => Mono (GlobalTheory.cutHom G hL a) ∧ ih (GlobalTheory.cut G hL a)) t F

theorem regSeq_cons {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (F : Y.Modules) (a : L.Sec) (r : List L.Sec) :
    RegSeq hL F (a :: r) ↔ Mono (GlobalTheory.cutHom F hL a) ∧ RegSeq hL (GlobalTheory.cut F hL a) r := Iff.rfl

def VanishFrom {Y : Scheme.{0}} (L : LB Y) (F : Y.Modules) (j₀ : ℤ) : Prop :=
  ∀ j : ℤ, j₀ ≤ j → ∀ q : ℕ, 0 < q → Subsingleton (coh (GlobalTheory.twistZ F L j) q)

example {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (F : Y.Modules) : RegSeq hL F [] := trivial

end GlobalTheory.HSCore
