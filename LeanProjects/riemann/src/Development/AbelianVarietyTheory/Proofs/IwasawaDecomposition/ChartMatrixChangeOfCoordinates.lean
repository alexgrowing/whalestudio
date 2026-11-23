import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernReg.MatCompat

open Complex

variable {d : ℕ}

theorem vecMul_dotProduct_star (B : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) :
    (x ᵥ* B) ⬝ᵥ star x = ∑ k, ∑ l, B k l * x k * starRingEnd ℂ (x l) := by
  simp only [dotProduct, vecMul, Finset.sum_mul, Pi.star_apply, Complex.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem polMat_diag {q : (Fin d → ℂ) → ℝ} {b : Matrix (Fin d) (Fin d) ℂ}
    (hq : q = fun ξ => (∑ k, ∑ l, b k l * ξ k * starRingEnd ℂ (ξ l)).re / Real.pi) (x : Fin d → ℂ) :
    (x ᵥ* polMat q) ⬝ᵥ star x = (q x : ℂ) := by
  set B : Matrix (Fin d) (Fin d) ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ) • (b + bᴴ) with hBdef
  have hB : B.IsHermitian := by
    rw [hBdef, IsHermitian, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, Complex.star_def,
      conj_ofReal, add_comm]
  have key (ξ : Fin d → ℂ) : ∑ k, ∑ l, B k l * ξ k * starRingEnd ℂ (ξ l) =
      (((∑ k, ∑ l, b k l * ξ k * starRingEnd ℂ (ξ l)).re / Real.pi : ℝ) : ℂ) := by
    have h1 : ∑ k, ∑ l, (bᴴ) k l * ξ k * starRingEnd ℂ (ξ l) =
        starRingEnd ℂ (∑ k, ∑ l, b k l * ξ k * starRingEnd ℂ (ξ l)) := by
      simp only [map_sum, map_mul, Complex.conj_conj, conjTranspose_apply, Complex.star_def]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have h2 : ∑ k, ∑ l, B k l * ξ k * starRingEnd ℂ (ξ l) = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∑ k, ∑ l, b k l * ξ k * starRingEnd ℂ (ξ l) + ∑ k, ∑ l, (bᴴ) k l * ξ k * starRingEnd ℂ (ξ l)) := by
      simp only [hBdef, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [h2, h1, add_conj]
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    push_cast
    field_simp
  have hqB : q = fun ξ => (∑ k, ∑ l, B k l * ξ k * starRingEnd ℂ (ξ l)).re := by
    rw [hq]
    funext ξ
    rw [key, ofReal_re]
  rw [hqB, polMat_form hB, vecMul_dotProduct_star, key, ← hqB, hq]

theorem eq_zero_of_diag {E : Type} [AddCommGroup E] [Module ℂ E] (f : E → E → ℂ)
    (hadd : ∀ x y z, f (x + y) z = f x z + f y z) (hsmul : ∀ (c : ℂ) x z, f (c • x) z = c * f x z)
    (hadd' : ∀ x y z, f x (y + z) = f x y + f x z) (hsmul' : ∀ (c : ℂ) x z, f x (c • z) = starRingEnd ℂ c * f x z)
    (h0 : ∀ x, f x x = 0) (ξ ζ : E) : f ξ ζ = 0 := by
  have e (c : ℂ) : starRingEnd ℂ c * f ξ ζ + c * f ζ ξ = 0 := by
    have := h0 (ξ + c • ζ)
    rw [hadd, hadd', hadd', hsmul', hsmul, hsmul, hsmul', h0 ξ, h0 ζ] at this
    linear_combination this
  have e1 := e 1
  have eI := e I
  rw [map_one] at e1
  rw [conj_I] at eI
  linear_combination (1 / 2 : ℂ) * e1 + (I / 2) * eI + ((f ξ ζ - f ζ ξ) / 2) * I_mul_I

end GlobalTheory.ChernReg.MatCompat

namespace GlobalTheory.ChernReg.MatCompat

theorem matIn_trans (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) (R : AnRead p σ d)
    (a : ChartForm p σ d) : IsKaehlerForm R a → ∀ c c' : AlgChart p σ d, ∀ v ∈ c.e.target, c.e.symm v ∈ c'.e.source →
    ∀ ξ ζ : ReciprocityTheory.L2DbarEstimates.V d, (ξ.ofLp ᵥ* matIn a c v) ⬝ᵥ star ζ.ofLp =
      ((fderiv ℂ (c'.e ∘ c.e.symm) v ξ).ofLp ᵥ* matIn a c' ((c'.e ∘ c.e.symm) v)) ⬝ᵥ
        star (fderiv ℂ (c'.e ∘ c.e.symm) v ζ).ofLp := by
  intro ha c c' v hv hy' ξ ζ
  have hy : c.e.symm v ∈ c.e.source := c.e.map_target hv
  set J := fderiv ℂ (c'.e ∘ c.e.symm) v with hJ
  have hM' : matIn a c' ((c'.e ∘ c.e.symm) v) = polMat (a c' (c.e.symm v)) := by
    rw [matIn, Function.comp_apply, c'.e.left_inv hy']
  have hM : matIn a c v = polMat (a c (c.e.symm v)) := rfl
  rw [hM', hM]
  have hd (x : Fin d → ℂ) : c.dtrans c' (c.e.symm v) x = (J (WithLp.toLp 2 x)).ofLp := by
    unfold AlgChart.dtrans
    rw [c.e.right_inv hv]
  obtain ⟨b, hb⟩ := exists_eq_sum ha hy
  obtain ⟨b', hb'⟩ := exists_eq_sum ha hy'
  let f : (Fin d → ℂ) → (Fin d → ℂ) → ℂ := fun x z =>
    (x ᵥ* polMat (a c (c.e.symm v))) ⬝ᵥ star z -
      ((J (WithLp.toLp 2 x)).ofLp ᵥ* polMat (a c' (c.e.symm v))) ⬝ᵥ star (J (WithLp.toLp 2 z)).ofLp
  have h := eq_zero_of_diag f
    (fun x y z => by
      simp only [f, WithLp.toLp_add, map_add, WithLp.ofLp_add, add_vecMul, add_dotProduct]; ring)
    (fun c x z => by
      simp only [f, WithLp.toLp_smul, map_smul, WithLp.ofLp_smul, smul_vecMul, smul_dotProduct,
        smul_eq_mul]; ring)
    (fun x y z => by
      simp only [f, WithLp.toLp_add, map_add, WithLp.ofLp_add, star_add, dotProduct_add]; ring)
    (fun c x z => by
      simp only [f, WithLp.toLp_smul, map_smul, WithLp.ofLp_smul, star_smul, dotProduct_smul, smul_eq_mul,
        Complex.star_def]; ring)
    (fun x => by
      simp only [f]
      rw [polMat_diag hb, polMat_diag hb', ← hd, ← ha.trans hy hy' x, sub_self])
    ξ.ofLp ζ.ofLp
  simpa only [f, WithLp.toLp_ofLp, sub_eq_zero] using h

end GlobalTheory.ChernReg.MatCompat
