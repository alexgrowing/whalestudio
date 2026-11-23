import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.PieceGood
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic.Whittaker
open Classical in
section
end

namespace PositivityTheory.RgUd.TP.Desc.Piece

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

def pe {d : ℕ} (c : Fin d → Matrix (Fin N) (Fin N) k) (x : Matrix (Fin N) (Fin N) k) : Matrix (Fin N) (Fin N) k :=
  ∑ l, c l * x ^ (l : ℕ)

def re {d r : ℕ} (γ : Fin d → Fin r → k) (s : Fin r → Matrix (Fin N) (Fin N) k) (ε : Matrix (Fin N) (Fin N) k) :
    Matrix (Fin N) (Fin N) k :=
  ∑ l, ∑ j, γ l j • (s j * ε ^ (l : ℕ))

open Classical in

structure SData (Z : Subalgebra k (Matrix (Fin N) (Fin N) k)) (χ : k[X]) (q : ℕ) where
  r : ℕ
  d : ℕ
  a : Fin r → Fin d → Matrix (Fin N) (Fin N) k
  ha : ∀ j l, a j l ∈ Z
  b : Fin d → Matrix (Fin N) (Fin N) k
  hb : ∀ l, b l ∈ Z
  c : Fin r → Fin r → Fin r → k
  u : Fin r → k
  a0 : ℕ
  z : Fin a0 → Matrix (Fin N) (Fin N) k
  hz : Z.toSubmodule = Submodule.span k (Set.range z)
  γ : Fin a0 → Fin d → Fin r → k
  β : Fin d → Fin r → k
  m : ℕ
  κ : Fin m → Fin r → k
  dd : Fin m → ℕ
  K : Fin m → Submodule k (Fin r → k)
  spec : ∀ x ∈ Bz Z, aeval x χ = 0 →
    let s := fun j => pe (a j) x
    let ε := pe b x
    (∀ j j', s j * s j' = ∑ t, c j j' t • s t) ∧ ∑ j, u j • s j = 1 ∧ (∀ j j', s j * s j' = s j' * s j) ∧
      (∀ j, s j * ε = ε * s j) ∧ ε ^ q = 0 ∧ (∀ y ∈ Submodule.span k (Set.range s), IsNilpotent y → y = 0) ∧
      (∀ i, z i = re (γ i) s ε) ∧ x = re β s ε ∧
      (∀ t, IsIdempotentElem (∑ j, κ t j • s j)) ∧ (∑ t, ∑ j, κ t j • s j) = 1 ∧
      (∀ t t', t ≠ t' → (∑ j, κ t j • s j) * (∑ j, κ t' j • s j) = 0) ∧
      (∀ t, ∀ y ∈ Submodule.span k (Set.range s), IsIdempotentElem y → y * (∑ j, κ t j • s j) = y →
        y = 0 ∨ y = ∑ j, κ t j • s j) ∧
      (∀ t, Module.finrank k (Submodule.span k (Set.range fun j => (∑ j', κ t j' • s j') * s j)) =
        if (∑ j, κ t j • s j) = 0 then 0 else dd t) ∧
      ∀ v : Fin r → k, (∑ j, v j • s j = 0 ↔ ∀ t, (∑ j, κ t j • s j) ≠ 0 → v ∈ K t)

def Sx {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q) (x : Matrix (Fin N) (Fin N) k) :
    Subalgebra k (Matrix (Fin N) (Fin N) k) :=
  Algebra.adjoin k (Set.range fun j => pe (D.a j) x)

def typ {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q) (x : Matrix (Fin N) (Fin N) k) :
    Fin D.m → ℕ :=
  fun t => (∑ j, D.κ t j • pe (D.a j) x).rank

def piece {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q) (τ : Fin D.m → ℕ) :
    Set (Matrix (Fin N) (Fin N) k) :=
  {x | x ∈ Bz Z ∧ aeval x χ = 0 ∧ typ D x = τ}

variable (k)

def Sect : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] [CharP k p] (N q : ℕ) (Z : Subalgebra k (Matrix (Fin N) (Fin N) k)), CR Z →
    (∃ c : ℕ, q = p ^ c) → HasRoots Z q → NilBound Z q → ∀ χ : k[X], χ.Monic → χ.natDegree = N → Nonempty (SData Z χ q)

def PieceTop : Prop :=
  ∀ (N q : ℕ) (Z : Subalgebra k (Matrix (Fin N) (Fin N) k)), CR Z → ∀ (χ : k[X]) (D : SData Z χ q) τ,
    IsClosed (piece D τ) ∧ (∀ g ∈ Gz Z, ∀ x ∈ piece D τ, g.val * x * g⁻¹.val ∈ piece D τ) ∧
      ∀ x ∈ piece D τ, CR (Sx D x)

def Dich : Prop :=
  ∀ (N q : ℕ) (Z : Subalgebra k (Matrix (Fin N) (Fin N) k)), CR Z → ∀ (χ : k[X]) (D : SData Z χ q) τ,
    ∀ x₀ ∈ piece D τ, mu (Sx D x₀) < mu Z ∨ ∃ c ∈ Z, IsNilpotent (x₀ - c)

def MuConst : Prop :=
  ∀ (N q : ℕ) (Z : Subalgebra k (Matrix (Fin N) (Fin N) k)), CR Z → ∀ (χ : k[X]) (D : SData Z χ q) τ,
    ∀ x ∈ piece D τ, ∀ x' ∈ piece D τ, mu (Sx D x) = mu (Sx D x')

def Transfer : Prop :=
  PositivityTheory.PfBern.Frob.FrobeniusReciprocity → ∀ (p : ℕ) [Fact p.Prime] [CharP k p], PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k) →
    ∀ (N q : ℕ) (Z : Subalgebra k (Matrix (Fin N) (Fin N) k)), CR Z → ∀ (χ : k[X]) (D : SData Z χ q) τ,
      ∀ x₀ ∈ piece D τ, Van (Sx D x₀) → FibVan Z (piece D τ)

end PositivityTheory.RgUd.TP.Desc.Piece
