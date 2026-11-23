import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfFlag

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag

namespace GlobalTheory.WholeFlag

def minorAt {K : Type} [CommRing K] {n g : ℕ} (H : Matrix (Fin n) (Fin g) K) (k : ℕ) (hk : k ≤ g) (σ : Fin k → Fin n) : K :=
  (Matrix.of fun r l : Fin k => H (σ r) (Fin.castLE hk l)).det

theorem minorAt_zero {K : Type} [CommRing K] {n g : ℕ} (H : Matrix (Fin n) (Fin g) K) (σ : Fin 0 → Fin n) :
    minorAt H 0 (Nat.zero_le g) σ = 1 :=
  Matrix.det_isEmpty

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def valMat (V : Cover Y) {g : ℕ} (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField) (T : Matrix (Fin g) (Fin g) Y.Fn)
    (z : Sp (AlgebraicClosure F) ⟶ V.G) : Matrix (Fin (g + g)) (Fin g) (AlgebraicClosure F) :=
  (H * (T.map V.φ)⁻¹).map (valAt z)

def HalfData {C : CxSt F} {g : ℕ} (A : Fin g → Adl C Y) (p : ℕ) : Prop :=
  ∃ (V : Cover Y) (W : Y.X.Opens) (ι : Type) (U : ι → V.X.Opens) (H : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField)
    (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn)
    (L : Fin g → LB V.X) (m : ℕ),
    IsUnit J.det ∧ genericPoint Y.X ∈ W ∧ 0 < m ∧
    (∀ x : V.X, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ a, x ∈ U a) ∧
    (∀ y, (T y).BlockTriangular id ∧ ∀ i, T y i i = (d y i : Y.Fn)) ∧
    (∀ i y, UnitAt y (genAt (A i).D y * d y i)) ∧
    (∀ i, NormsAt V (L i) p ⊤ (fun y => genAt (A i).D y ^ m) fun v e y => m * (A i).lg v e y) ∧
    (∀ a (z : V.G), V.j z ∈ U a → ∀ k l, RegAt z ((H a * ((T (V.π z)).map V.φ)⁻¹) k l)) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : Ext v) (y : AlgPt Y), below y.1 ∈ W →
      ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j →
      ∃ ν : ℕ → ℝ, (∀ k, k ≤ g → 0 < ν k) ∧
        (∀ i : Fin g, (A i).lg v e y = Real.log (e.w (valAt y.1 (genAt (A i).D (below y.1) * d (below y.1) i))) +
          Real.log (ν ((i : ℕ) + 1)) - Real.log (ν (i : ℕ))) ∧
        ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a →
          (∀ (k : ℕ) (hk : k ≤ g) (σ : Fin k → Fin (g + g)), e.w (minorAt (valMat V (H a) (T (below y.1)) z) k hk σ) ≤ ν k) ∧
          (∀ (k : ℕ) (hk : k ≤ g), ∃ σ : Fin k → Fin (g + g), e.w (minorAt (valMat V (H a) (T (below y.1)) z) k hk σ) = ν k) ∧
          (∀ u u' : Fin g → AlgebraicClosure F, (∀ r, e.w ((Matrix.mulVec (valMat V (H a) (T (below y.1)) z) u) r) ≤ 1) →
            (∀ r, e.w ((Matrix.mulVec (valMat V (H a) (T (below y.1)) z) u') r) ≤ 1) →
            e.w (dotProduct (Matrix.mulVec (valMat V (H a) (T (below y.1)) z) u)
              (Matrix.mulVec (J.map (Int.castRingHom (AlgebraicClosure F))) (Matrix.mulVec (valMat V (H a) (T (below y.1)) z) u'))) < 1) ∧
          ∀ b, ⊤ ≤ yt ⁻¹ᵁ U b → ∀ u : Fin g → AlgebraicClosure F,
            (∀ r, e.w ((Matrix.mulVec (valMat V (H a) (T (below y.1)) z) u) r) ≤ 1) →
            ∀ r, e.w ((Matrix.mulVec (valMat V (H b) (T (below y.1)) z) u) r - (Matrix.mulVec (valMat V (H a) (T (below y.1)) z) u) r) < 1

end GlobalTheory.WholeFlag

end
