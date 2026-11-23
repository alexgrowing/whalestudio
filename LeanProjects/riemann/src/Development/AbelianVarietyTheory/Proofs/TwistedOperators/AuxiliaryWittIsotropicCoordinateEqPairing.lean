import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.AscFin

theorem coeff_monic_poly_sum {K R : Type} [CommRing K] [CommRing R] (φ : K →+* R) {n : ℕ} (u s : K) (h : s * u = 1)
    (b : Fin n → K) (G : Matrix (Fin n) (Fin n) K) (x : Fin n → R) :
    φ u * ∑ l, φ (∑ k, (s * b k) * G k l) * x l = ∑ k, ∑ l, φ (b k) * φ (G k l) * x l := by
  have hus : φ u * φ s = 1 := by rw [← map_mul, mul_comm, h, map_one]
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  linear_combination (φ (b k) * φ (G k l) * x l) * hus

private theorem cT_sig_eq_conjTranspose' {D : D7} {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M = Mᴴ := rfl

private theorem cA_incA_apply_eq_incA_star {D : D7} (e : D.host.E) : cA D (incA D e) = incA D (star e) := rfl

theorem incA_neg_xi0_pow_mul_pX_mulVec_eq_sum : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), c = 2 * ρ → IsAuxiliaryVectorWittDec a d → ∀ (i : Fin ρ) (hi : 2 * ρ - 1 - i.1 < c) (x : Fin B.rank → AE D), incA D ((-D.host.xi0) ^ (i.1 + 1)) * (d.pX *ᵥ x) i = ∑ k, ∑ l, cA D (incA D (a.a k ⟨2 * ρ - 1 - i.1, hi⟩)) * incA D (B.gram k l) * x l := by
  intro D A B B₀ c ρ a d hc hA i hi x
  obtain ⟨h2, he, s, he'⟩ := hA
  have hle : ρ ≤ c := by omega
  have hj : ∀ hle : ρ ≤ c, (Fin.castLE hle i).rev = (⟨2 * ρ - 1 - i.1, hi⟩ : Fin c) := fun hle => by
    ext
    simp only [Fin.val_rev, Fin.coe_castLE]
    omega
  have g1 := congrFun (congrFun a.gram ⟨2 * ρ - 1 - i.1, hi⟩) (Fin.castLE hle i)
  have g2 := congrFun (congrFun d.e'e i) i
  rw [he, he'] at g2
  simp only [antiDiagonalSignGramMatrix, cT_sig_eq_conjTranspose', Matrix.mul_apply, Matrix.conjTranspose_apply, colsOf, star_mul', Matrix.one_apply_eq, hj,
    Fin.coe_castLE] at g1 g2
  rw [if_pos (by omega), if_neg (fun h => by have := congrArg Fin.val h; simp only [Fin.coe_castLE] at this; omega)] at g1
  have g3 : ∑ l, (∑ k, star (s i) * star (a.a k ⟨2 * ρ - 1 - i.1, hi⟩) * HSpace.gram B k l) *
      ((-D.host.xi0) ^ (i.1 + 1) * a.a l (Fin.castLE hle i)) =
      star (s i) * (-D.host.xi0) ^ (i.1 + 1) *
        ∑ l, (∑ k, star (a.a k ⟨2 * ρ - 1 - i.1, hi⟩) * HSpace.gram B k l) * a.a l (Fin.castLE hle i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [mul_assoc (star (s i)), ← Finset.mul_sum]
    ring
  have key : star (s i) * (-D.host.xi0) ^ (i.1 + 1) = 1 := by
    linear_combination g2 - g3 - (star (s i) * (-D.host.xi0) ^ (i.1 + 1)) * g1
  simp only [HypDec.pX, HypDec.qX, GlobalTheory.MixModel.rat, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, he', colsOf, star_mul', hj, cA_incA_apply_eq_incA_star]
  exact coeff_monic_poly_sum (incA D) _ _ key (fun k => star (a.a k ⟨2 * ρ - 1 - i.1, hi⟩)) (HSpace.gram B) x

end GlobalTheory.AscFin

end
