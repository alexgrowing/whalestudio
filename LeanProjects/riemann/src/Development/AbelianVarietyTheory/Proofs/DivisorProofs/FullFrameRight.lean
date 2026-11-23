import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorAtZero
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MvPolynomial Formalism.BasicNotions.DV
open GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag
open GlobalTheory.Cartier GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.WholeFlag

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WholeFlag

open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def HalfDataC {C : CxSt F} {g : ℕ} (A : Fin g → Adl C Y) (p : ℕ) : Prop :=
  ∃ (V : Cover Y) (W : Y.X.Opens) (ι : Type) (U : ι → V.X.Opens) (H : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField)
    (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (d : Y.X → Fin g → Y.Fnˣ) (T : Y.X → Matrix (Fin g) (Fin g) Y.Fn)
    (L : Fin g → LB V.X) (m : ℕ),
    IsUnit J.det ∧ genericPoint Y.X ∈ W ∧ 0 < m ∧
    (∀ x : V.X, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ a, x ∈ U a) ∧
    (∀ i (x : V.X), ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ c, x ∈ (L i).U c) ∧
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

namespace GlobalTheory.WholeFlag.Glue

variable {K : Type} [Field K] {g : ℕ}

def cramerCol (H : Matrix (Fin (g + g)) (Fin g) K) (σ : ∀ k : ℕ, Fin k → Fin (g + g)) : Matrix (Fin (g + g)) (Fin g) K :=
  Matrix.of fun r k => minorAt H ((k : ℕ) + 1) k.2 (Fin.snoc (σ k) r) / minorAt H ((k : ℕ) + 1) k.2 (σ ((k : ℕ) + 1))

def rowSel {R : Type} [Semiring R] (τ : Fin g → Fin (g + g)) : Matrix (Fin g) (Fin (g + g)) R :=
  Matrix.of fun l r => if τ l = r then 1 else 0

def leftInv {R : Type} [CommRing R] (U : Matrix (Fin (g + g)) (Fin g) R) (τ : Fin g → Fin (g + g)) :
    Matrix (Fin g) (Fin (g + g)) R :=
  (rowSel τ * U : Matrix (Fin g) (Fin g) R)⁻¹ * rowSel τ

def antiDiag (R : Type) [Semiring R] (g : ℕ) : Matrix (Fin g) (Fin g) R :=
  Matrix.of fun i k => if (i : ℕ) + k = g - 1 then 1 else 0

def fullFrame {R : Type} [CommRing R] (U : Matrix (Fin (g + g)) (Fin g) R) (J : Matrix (Fin (g + g)) (Fin (g + g)) R)
    (Lft : Matrix (Fin g) (Fin (g + g)) R) : Matrix (Fin (g + g)) (Fin (g + g)) R :=
  Matrix.of fun r c => Fin.addCases (fun k => U r k) (fun k => (J⁻¹ * Lft.transpose * antiDiag R g) r k) c

@[simp] theorem fullFrame_left {R : Type} [CommRing R] (U : Matrix (Fin (g + g)) (Fin g) R)
    (J : Matrix (Fin (g + g)) (Fin (g + g)) R) (Lft : Matrix (Fin g) (Fin (g + g)) R) (r : Fin (g + g)) (k : Fin g) :
    fullFrame U J Lft r (Fin.castAdd g k) = U r k := by
  simp [fullFrame]

@[simp] theorem fullFrame_right {R : Type} [CommRing R] (U : Matrix (Fin (g + g)) (Fin g) R)
    (J : Matrix (Fin (g + g)) (Fin (g + g)) R) (Lft : Matrix (Fin g) (Fin (g + g)) R) (r : Fin (g + g)) (k : Fin g) :
    fullFrame U J Lft r (Fin.natAdd g k) = (J⁻¹ * Lft.transpose * antiDiag R g) r k := by
  unfold fullFrame
  rw [Matrix.of_apply, Fin.addCases_right]

end GlobalTheory.WholeFlag.Glue

end
