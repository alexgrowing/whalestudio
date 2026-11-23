import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CNormSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ExistsNatMulMemConeRingIntFin
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.HadZSt
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.BergmanSt
import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.MonomSt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder

theorem aeval_eq_sum_adt {D N : ℕ} {S : Type*} [CommRing S] (g : MvPolynomial (Fin (D + 1)) ℤ)
    (hg : g.IsHomogeneous N) (y : Fin (D + 1) → S) :
    aeval y g = ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N,
      ((coeff (Finsupp.equivFunOnFinite.symm a) g : ℤ) : S) * ∏ i, y i ^ a i := by
  classical
  rw [aeval_def, eval₂_eq']
  symm
  refine Finset.sum_bij_ne_zero (fun a _ _ => Finsupp.equivFunOnFinite.symm a) ?_ ?_ ?_ ?_
  · intro a _ ha
    rw [MvPolynomial.mem_support_iff]
    intro h
    apply ha
    simp [h]
  · intro a _ _ b _ _ h
    exact Finsupp.equivFunOnFinite.symm.injective h
  · intro d hd hne
    refine ⟨Finsupp.equivFunOnFinite d, ?_, ?_, ?_⟩
    · rw [Finset.Nat.mem_antidiagonalTuple]
      have h := hg (MvPolynomial.mem_support_iff.1 hd)
      rw [Finsupp.weight_apply] at h
      simpa [Finsupp.sum_fintype] using h
    · simpa using hne
    · simp
  · intro a _ _
    simp

theorem integral_sphProb_le {D : ℕ} (F : (Fin (D + 1) → ℂ) → ℝ) (hF0 : ∀ w, 0 ≤ F w) {B : ℝ}
    (hB : ∀ w, sqN w = 1 → F w ≤ B) : ∫ w, F w ∂(sphProb (D + 1)) ≤ B := by
  have hae : ∀ᵐ w ∂(sphProb (D + 1)), sqN w = 1 := by
    rw [ae_iff]
    exact sphProb_compl_sphere D
  calc ∫ w, F w ∂(sphProb (D + 1)) ≤ ∫ _w, B ∂(sphProb (D + 1)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall hF0) (integrable_const B)
          (hae.mono fun w hw => hB w hw)
    _ = B := by simp

def secTraceHom {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} [Fintype κ] {D : ℕ} (x : κ → Ω)
    (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e) (n : ℕ) : sec ℤ x n →+ Ω :=
  AddMonoidHom.mk' (fun s => secTrace x e n s) fun s t => secTrace_add x e h n s.2 t.2

def adtEnum (D N : ℕ) (i : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card) : Fin (D + 1) → ℕ :=
  ((Finset.Nat.antidiagonalTuple (D + 1) N).equivFin.symm i).1

theorem sum_adtEnum {M : Type*} [AddCommMonoid M] (D N : ℕ) (f : (Fin (D + 1) → ℕ) → M) :
    ∑ i, f (adtEnum D N i) = ∑ a ∈ Finset.Nat.antidiagonalTuple (D + 1) N, f a := by
  exact (Fintype.sum_equiv (Finset.Nat.antidiagonalTuple (D + 1) N).equivFin.symm _
    (fun x => f x.1) fun _ => rfl).trans (Finset.sum_coe_sort _ f)

def monoDiag (D N δ : ℕ) : Matrix (Fin (δ * (Finset.Nat.antidiagonalTuple (D + 1) N).card))
    (Fin (δ * (Finset.Nat.antidiagonalTuple (D + 1) N).card)) ℂ :=
  Matrix.diagonal fun p => ((monoNormSq (adtEnum D N (finProdFinEquiv.symm p).2) : ℝ) : ℂ)

theorem monoDiag_posDef (D N δ : ℕ) : (monoDiag D N δ).PosDef := by
  rw [monoDiag, Matrix.posDef_diagonal_iff]
  intro p
  have h : 0 < monoNormSq (adtEnum D N (finProdFinEquiv.symm p).2) := by
    unfold monoNormSq
    positivity
  exact_mod_cast h

theorem neg_log_det_monoDiag (D N δ : ℕ) :
    -(1 / 2) * Real.log (monoDiag D N δ).det.re = δ * chiP D N := by
  have hpos : ∀ a : Fin (D + 1) → ℕ, 0 < monoNormSq a := fun a => by
    unfold monoNormSq
    positivity
  have hdet : (monoDiag D N δ).det.re =
      ∏ p : Fin (δ * (Finset.Nat.antidiagonalTuple (D + 1) N).card),
        monoNormSq (adtEnum D N (finProdFinEquiv.symm p).2) := by
    rw [monoDiag, Matrix.det_diagonal, ← Complex.ofReal_prod, Complex.ofReal_re]
  rw [hdet, Real.log_prod fun p _ => (hpos _).ne']
  rw [← finProdFinEquiv.sum_comp (fun p => Real.log (monoNormSq (adtEnum D N (finProdFinEquiv.symm p).2)))]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    sum_adtEnum D N (fun a => Real.log (monoNormSq a)), chiP]
  ring

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
