import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ArInt

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {ι : Type} [Fintype ι]

def zp (L : HermLB p) (n : ℤ) : HermLB p := (L.pow n.toNat).tens (L.pow (-n).toNat).dual

def comb (L : ι → HermLB p) (n : ι → ℤ) : HermLB p :=
  (Finset.univ : Finset ι).toList.foldr (fun i M => (zp (L i) (n i)).tens M) (HermLB.triv p)

def lin (n : ι → ℝ) : MvPolynomial ι ℝ := ∑ i, C (n i) * MvPolynomial.X i

def fnB (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) (hu : ∀ σ y, CxPts.CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) : HermLB p where
  B := LB.triv X
  isLB := LB.isLB_triv X
  φ σ := Weight.ofFun (u σ)
  cInf σ := fun _ y _ => hu σ y
  conj := hc

def chInt (L : HermLB p) (D : ℕ) (f : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) : ℝ :=
  ∑ᶠ σ, (L.φ σ).chernInt D Set.univ (f σ)

def gdeg (L : HermLB p) (D : ℕ) : ℝ := chInt L D fun _ _ => 1

def IsArFun [IsIntegral X] (L : ι → HermLB p) (D : ℕ) (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) : Prop :=
  (∀ n : ι → ℤ, (comb L n).IsSelfInter (Φ (lin (fun i => (n i : ℝ)) ^ (D + 1)))) ∧
    ∀ (P : MvPolynomial ι ℝ) (d : ℕ), d ≠ D + 1 → P.IsHomogeneous d → Φ P = 0

def IsGeoFun (L : ι → HermLB p) (D : ℕ) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) : Prop :=
  (∀ n : ι → ℤ, Ψ (lin (fun i => (n i : ℝ)) ^ D) = gdeg (comb L n) D) ∧
    ∀ (P : MvPolynomial ι ℝ) (d : ℕ), d ≠ D → P.IsHomogeneous d → Ψ P = 0

def IsAlgPt (x : X) : Prop :=
  CharZero (X.residueField x) ∧ topologicalKrullDim (closure ({x} : Set X)) = 1

def IsPtHt (L : HermLB p) (x : X) (a : ℝ) : Prop :=
  ∃ h, L.IsArithHeight h ∧ h x = a * Nat.card (X.residueField x →+* ℂ)

def NefFib (L : HermLB p) : Prop :=
  ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type)
    [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection κ (L.B.pull i) 1

def arVol (L : HermLB p) (D : ℕ) : EReal :=
  limsup (fun m : ℕ => ENNReal.log ((L.pow m).smallSec.encard : ENNReal) *
    ((((D + 1).factorial : ℝ) / (m : ℝ) ^ (D + 1) : ℝ) : EReal)) atTop

theorem nefFib_of_isNef {L : HermLB p} {D : ℕ} (h : L.IsNef D) : NefFib L := h.vertical

end GlobalTheory.ArInt
