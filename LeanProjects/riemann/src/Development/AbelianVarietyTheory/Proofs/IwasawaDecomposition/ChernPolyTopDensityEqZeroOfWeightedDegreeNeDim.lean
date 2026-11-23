import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric.ChernDegree

def gradedCoeff (σ : Type) : Subring (Polynomial (MvPolynomial σ ℂ)) where
  carrier := {p | ∀ k, (p.coeff k).IsHomogeneous k}
  mul_mem' := by
    intro p q hp hq k
    rw [Polynomial.coeff_mul]
    refine IsHomogeneous.sum _ _ _ fun x hx => ?_
    have := (hp x.1).mul (hq x.2)
    rwa [Finset.HasAntidiagonal.mem_antidiagonal.1 hx] at this
  one_mem' := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simpa using isHomogeneous_one σ ℂ
    · rw [Polynomial.coeff_one, if_neg (by omega)]; exact isHomogeneous_zero _ _ _
  add_mem' := by
    intro p q hp hq k
    rw [Polynomial.coeff_add]; exact (hp k).add (hq k)
  zero_mem' := by
    intro k
    rw [Polynomial.coeff_zero]; exact isHomogeneous_zero _ _ _
  neg_mem' := by
    intro p hp k
    rw [Polynomial.coeff_neg]; exact (hp k).neg

theorem charpolyRev_coeff_isHomogeneous {σ r : Type} [Fintype r] [DecidableEq r]
    (M : Matrix r r (MvPolynomial σ ℂ)) (hM : ∀ i j, (M i j).IsHomogeneous 1) (k : ℕ) :
    ((Matrix.charpolyRev M).coeff k).IsHomogeneous k := by
  have hent : ∀ i j, (1 - (Polynomial.X : Polynomial (MvPolynomial σ ℂ)) • M.map Polynomial.C) i j ∈ gradedCoeff σ := by
    intro i j
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    refine Subring.sub_mem _ ?_ ?_
    · rw [Matrix.one_apply]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    · intro l
      rw [mul_comm, Polynomial.coeff_C_mul_X]
      split_ifs with h
      · subst h; exact hM i j
      · exact isHomogeneous_zero _ _ _
  have hdet : Matrix.charpolyRev M ∈ gradedCoeff σ := by
    rw [Matrix.charpolyRev, Matrix.det_apply']
    refine Subring.sum_mem _ fun s _ => Subring.mul_mem _ (intCast_mem _ _) ?_
    exact Subring.prod_mem _ fun i _ => hent _ _
  exact hdet k

theorem chernPoly_isHomogeneous {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]
    (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ) :
    (chernPoly G v k).IsHomogeneous k := by
  refine charpolyRev_coeff_isHomogeneous _ (fun i j => ?_) k
  rw [Matrix.neg_apply, curvPoly, Matrix.of_apply]
  exact (IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _ fun b _ =>
    isHomogeneous_C_mul_X _ _).neg

theorem aeval_isWeightedHomogeneous {σ τ : Type} {w : σ → ℕ} {w' : τ → ℕ}
    {φ : MvPolynomial σ ℝ} {m : ℕ} (hφ : IsWeightedHomogeneous w φ m)
    (g : σ → MvPolynomial τ ℂ) (hg : ∀ i, IsWeightedHomogeneous w' (g i) (w i)) :
    IsWeightedHomogeneous w' (aeval g φ) m := by
  rw [φ.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [aeval_monomial]
  have hdeg : (Finsupp.weight w) d = m := hφ (mem_support_iff.mp hd)
  have h1 : IsWeightedHomogeneous w' (d.prod fun i k => g i ^ k) (∑ i ∈ d.support, d i • w i) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ => (hg i).pow (d i)
  have h2 : (∑ i ∈ d.support, d i • w i) = m := by
    rw [← hdeg, Finsupp.weight_apply, Finsupp.sum]
  rw [h2] at h1
  have h3 := (isWeightedHomogeneous_C w' (algebraMap ℝ ℂ (coeff d φ))).mul h1
  rw [zero_add] at h3
  rw [MvPolynomial.algebraMap_apply]
  exact h3

theorem topCoeff_eq_zero {n d : ℕ} {P : MvPolynomial (Fin n × Fin n) ℂ} (hP : P.IsHomogeneous d) (hd : d ≠ n) :
    topCoeff P = 0 := by
  unfold topCoeff
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [hP.coeff_eq_zero, mul_zero]
  intro h
  apply hd
  rw [← h, Finsupp.degree_eq_weight_one, map_sum]
  simp [Finsupp.weight_single]

end GlobalTheory.GoodMetric.ChernDegree

open GlobalTheory.GoodMetric.ChernDegree in

theorem GlobalTheory.GoodMetric.chernTop_eq_zero_of_weightedHomogeneous (n : ℕ) (ι : Type) (m : ι → ℕ)
    (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (Q : MvPolynomial (ι × ℕ) ℝ) (d : ℕ)
    (hQ : MvPolynomial.IsWeightedHomogeneous (Prod.snd : ι × ℕ → ℕ) Q d) (hd : d ≠ n) :
    chernTop Q G v = 0 := by
  have h : (aeval (fun x : ι × ℕ => chernPoly (fun u => G u x.1) v x.2) Q).IsHomogeneous d :=
    aeval_isWeightedHomogeneous hQ _ fun x => chernPoly_isHomogeneous _ _ _
  rw [chernTop, topCoeff_eq_zero h hd, Complex.zero_re, mul_zero]

example : ∀ (n : ℕ) (ι : Type) (m : ι → ℕ) (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (Q : MvPolynomial (ι × ℕ) ℝ) (d : ℕ), MvPolynomial.IsWeightedHomogeneous (Prod.snd : ι × ℕ → ℕ) Q d → d ≠ n → chernTop Q G v = 0 :=
  GlobalTheory.GoodMetric.chernTop_eq_zero_of_weightedHomogeneous
