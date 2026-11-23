import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.ChernCoord

def gradedSubring (σ : Type) : Subring (Polynomial (MvPolynomial σ ℂ)) where
  carrier := {p | ∀ k, (p.coeff k).IsHomogeneous k}
  mul_mem' := by
    intro p q hp hq k
    rw [Polynomial.coeff_mul]
    refine IsHomogeneous.sum _ _ _ fun x hx => ?_
    have h : x.1 + x.2 = k := by simpa using hx
    rw [← h]
    exact (hp x.1).mul (hq x.2)
  one_mem' := by
    intro k
    rw [Polynomial.coeff_one]
    split_ifs with h
    · subst h; exact isHomogeneous_one _ _
    · exact isHomogeneous_zero _ _ _
  add_mem' := by
    intro p q hp hq k
    rw [Polynomial.coeff_add]
    exact (hp k).add (hq k)
  zero_mem' := by
    intro k
    rw [Polynomial.coeff_zero]
    exact isHomogeneous_zero _ _ _
  neg_mem' := by
    intro p hp k
    rw [Polynomial.coeff_neg]
    exact (hp k).neg

theorem C_mul_X_mem {σ : Type} {a : MvPolynomial σ ℂ} (ha : a.IsHomogeneous 1) :
    Polynomial.C a * Polynomial.X ∈ gradedSubring σ := by
  intro k
  rw [Polynomial.coeff_C_mul_X]
  split_ifs with h
  · subst h; exact ha
  · exact isHomogeneous_zero _ _ _

theorem charpolyRev_mem {σ r : Type} [Fintype r] [DecidableEq r] (M : Matrix r r (MvPolynomial σ ℂ))
    (hM : ∀ i j, (M i j).IsHomogeneous 1) : M.charpolyRev ∈ gradedSubring σ := by
  let N : Matrix r r (gradedSubring σ) := Matrix.of fun i j =>
    ⟨(1 : Matrix r r (Polynomial (MvPolynomial σ ℂ))) i j - Polynomial.X * Polynomial.C (M i j), by
      refine Subring.sub_mem _ ?_ ?_
      · rw [Matrix.one_apply]; split_ifs
        · exact Subring.one_mem _
        · exact Subring.zero_mem _
      · rw [mul_comm]; exact C_mul_X_mem (hM i j)⟩
  have : M.charpolyRev = (gradedSubring σ).subtype N.det := by
    rw [RingHom.map_det, Matrix.charpolyRev]
    congr 1
  rw [this]
  exact Subtype.property _

end GlobalTheory.ChernCoord

namespace GlobalTheory.ChernCoord

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

theorem chernPoly_isHomogeneous (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ) :
    (chernPoly G v k).IsHomogeneous k := by
  refine charpolyRev_mem (-curvPoly G v) (fun i j => ?_) k
  simp only [Matrix.neg_apply, curvPoly, Matrix.of_apply]
  refine IsHomogeneous.neg (IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ => ?_)
  exact isHomogeneous_C_mul_X _ _

end GlobalTheory.ChernCoord
