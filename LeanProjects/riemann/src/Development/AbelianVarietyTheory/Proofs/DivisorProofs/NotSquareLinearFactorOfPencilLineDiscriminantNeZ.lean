import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedLatticeZeroCycleHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLine

set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

namespace GlobalTheory.PencilDisc

def lineSubst {K : Type} [Field K] {N : ℕ} (a b : Fin N → K) : MvPolynomial (Fin 1 × Fin N) K →ₐ[K] Polynomial K :=
  aeval fun p : Fin 1 × Fin N => Polynomial.C (a p.2) + Polynomial.C (b p.2) * Polynomial.X

theorem line_eq_lineSubst {F K : Type} [Field F] [Field K] [Algebra F K] {D N : ℕ}
    (s : Fin D → Fin N → K) (a b : Fin N → K) (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    line s a b f = lineSubst a b (spec s f) := by
  simp only [line, spec]
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [aeval_C, lineSubst]
    rw [IsScalarTower.algebraMap_apply F K (MvPolynomial (Fin 1 × Fin N) K),
      IsScalarTower.algebraMap_apply F K (Polynomial K), AlgHom.commutes]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n ih =>
    simp only [map_mul, ih, aeval_X]
    congr 1
    obtain ⟨i, j⟩ := n
    induction i using Fin.lastCases <;> simp [join, lineSubst]

theorem eval_spec {F K : Type} [Field F] [Field K] [Algebra F K] {D N : ℕ}
    (s : Fin D → Fin N → K) (b : Fin N → K) (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    eval (fun p : Fin 1 × Fin N => b p.2) (spec s f) = aeval (join s b) f := by
  simp only [spec]
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [aeval_C]
    rw [IsScalarTower.algebraMap_apply F K (MvPolynomial (Fin 1 × Fin N) K)]
    simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n ih =>
    simp only [map_mul, ih, aeval_X]
    congr 1
    obtain ⟨i, j⟩ := n
    induction i using Fin.lastCases <;> simp [join]

theorem lineSubst_lin {K : Type} [Field K] {N : ℕ} (a b y : Fin N → K) :
    lineSubst a b (lin y) = Polynomial.C (∑ j, a j * y j) + Polynomial.C (∑ j, b j * y j) * Polynomial.X := by
  simp only [lin, lineSubst, map_sum, map_mul, aeval_X, aeval_C, Polynomial.algebraMap_eq, add_mul,
    Finset.sum_add_distrib, Polynomial.C_mul, Finset.sum_mul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem eval_lin {K : Type} [Field K] {N : ℕ} (b y : Fin N → K) :
    eval (fun p : Fin 1 × Fin N => b p.2) (lin y) = ∑ j, b j * y j := by
  simp [lin]

theorem coeff_ne_zero_of_resultant_ne_zero {K : Type} [Field K] {δ : ℕ} (hδ : 1 ≤ δ) (P : Polynomial K)
    (hP : P.natDegree ≤ δ) (h : Polynomial.resultant P (Polynomial.derivative P) δ (δ - 1) ≠ 0) : P.coeff δ ≠ 0 := by
  by_contra hc
  apply h
  have hlt : P.natDegree < δ := by
    rcases hP.lt_or_eq with h1 | h1
    · exact h1
    exfalso
    by_cases hP0 : P = 0
    · rw [hP0, Polynomial.natDegree_zero] at h1
      omega
    exact hP0 (Polynomial.leadingCoeff_eq_zero.mp (by rw [Polynomial.leadingCoeff, h1]; exact hc))
  rcases Nat.lt_or_ge δ 2 with h2 | h2
  · obtain rfl : δ = 1 := by omega
    have hd : Polynomial.derivative P = 0 := by
      rw [Polynomial.eq_C_of_natDegree_eq_zero (by omega : P.natDegree = 0), Polynomial.derivative_C]
    simp [hd]
  · apply Polynomial.resultant_eq_zero_of_lt_lt _ _ _ _ hlt
    calc (Polynomial.derivative P).natDegree ≤ P.natDegree - 1 := Polynomial.natDegree_derivative_le P
      _ < δ - 1 := by omega

theorem noSquare_spec_of_disc_ne_zero : ∀ (F K : Type) [Field F] [Field K] [Algebra F K] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F) (s : Fin D → Fin N → K) (a b : Fin N → K), 1 ≤ δ → (GlobalTheory.PencilDisc.line s a b f).natDegree ≤ δ → (GlobalTheory.PencilDisc.line s a b f).coeff δ = MvPolynomial.aeval (GlobalTheory.HSChoice.join s b) f → GlobalTheory.PencilDisc.disc δ s a b f ≠ 0 → GlobalTheory.HSChoice.NoSquare (GlobalTheory.HSChoice.spec s f) := by
  intro F K _ _ _ D N δ f s a b hδ hdeg hcoeff hdisc
  have hres : (line s a b f).resultant (Polynomial.derivative (line s a b f)) δ (δ - 1) ≠ 0 := hdisc
  have hc : (line s a b f).coeff δ ≠ 0 := coeff_ne_zero_of_resultant_ne_zero hδ _ hdeg hres
  have hspec0 : eval (fun p : Fin 1 × Fin N => b p.2) (spec s f) ≠ 0 := by
    rw [eval_spec, ← hcoeff]
    exact hc
  refine ⟨fun h0 => hspec0 (by rw [h0, map_zero]), fun y _ hdvd => ?_⟩
  obtain ⟨q, hq⟩ := hdvd
  by_cases hβ : ∑ j, b j * y j = 0
  · apply hspec0
    rw [hq, map_mul, map_pow, eval_lin, hβ]
    simp
  · have hnat : (line s a b f).natDegree = δ :=
      Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg hc
    have hP0 : line s a b f ≠ 0 := fun h0 => hc (by rw [h0, Polynomial.coeff_zero])
    have hcop : IsCoprime (line s a b f) (Polynomial.derivative (line s a b f)) := by
      by_contra hnc
      apply hres
      have hd' : (Polynomial.derivative (line s a b f)).natDegree ≤ δ - 1 := by
        rw [← hnat]
        exact Polynomial.natDegree_derivative_le _
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hd'
      rw [hk, Polynomial.resultant_add_right_deg _ _ _ _ _ le_rfl, ← hnat,
        Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl hP0, hnc⟩, mul_zero]
    have hQ : line s a b f = lineSubst a b (lin y) * lineSubst a b (lin y) * lineSubst a b q := by
      rw [line_eq_lineSubst, hq, map_mul, map_pow, sq]
    have h1 : lineSubst a b (lin y) ∣ line s a b f :=
      ⟨lineSubst a b (lin y) * lineSubst a b q, by rw [hQ]; ring⟩
    have h2 : lineSubst a b (lin y) ∣ Polynomial.derivative (line s a b f) := by
      refine ⟨Polynomial.derivative (lineSubst a b (lin y)) * lineSubst a b q +
        Polynomial.derivative (lineSubst a b (lin y)) * lineSubst a b q +
        lineSubst a b (lin y) * Polynomial.derivative (lineSubst a b q), ?_⟩
      rw [hQ, Polynomial.derivative_mul, Polynomial.derivative_mul]
      ring
    have hu := hcop.isUnit_of_dvd' h1 h2
    rw [lineSubst_lin] at hu
    have hdeg0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [add_comm, Polynomial.natDegree_linear hβ] at hdeg0
    exact one_ne_zero hdeg0

end GlobalTheory.PencilDisc
