import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff

namespace GlobalTheory.LapSplit

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem Eop_conjugate (τ : E →+* ℂ) (i j : Fin a) :
    Eop (ComplexEmbedding.conjugate τ) i j =
      (1 / 2 : ℂ) • (lieS E a i j (atEmb τ 1) + Complex.I • lieS E a i j (atEmb τ Complex.I)) := by
  have h : atEmb τ (starRingEnd ℂ Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq τ (starRingEnd ℂ Complex.I)]
    conv_rhs => rw [atEmb_eq τ Complex.I]
    simp
  simp only [Eop, atEmb_conj, map_one, h, map_neg, smul_neg, sub_neg_eq_add]

theorem sum_sum_eq_zero_of_swap {A : Type} [AddCommGroup A] [Module ℂ A] (f : Fin a → Fin a → A)
    (hf : ∀ i j, f i j + f j i = 0) : ∑ i, ∑ j, f i j = 0 := by
  have h2 : (2 : ℂ) • ∑ i, ∑ j, f i j = 0 := by
    rw [two_smul]
    conv_lhs => enter [2]; rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => by rw [← Finset.sum_add_distrib]; exact Finset.sum_eq_zero fun j _ => hf i j
  have := congrArg (fun x => (1 / 2 : ℂ) • x) h2
  simpa [smul_smul] using this

theorem lap_summand (τ : E →+* ℂ) :
    ∑ i : Fin a, ∑ j : Fin a, ((lieS E a i j (atEmb τ 1)) ^ 2 + (lieS E a i j (atEmb τ Complex.I)) ^ 2) =
      (2 : ℂ) • ∑ i : Fin a, ∑ j : Fin a, (1 / 4 : ℂ) •
        ((lieS E a i j (atEmb τ 1) - lieS E a j i (atEmb τ 1)) ^ 2 +
          (lieS E a i j (atEmb τ Complex.I) + lieS E a j i (atEmb τ Complex.I)) ^ 2) +
      (2 : ℂ) • Formalism.REAL.Cas (Eop (a := a) τ) + (2 : ℂ) • Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate τ)) := by
  rw [← sub_eq_zero]
  simp only [Formalism.REAL.Cas, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply sum_sum_eq_zero_of_swap
  intro i j
  simp only [Eop_conjugate]
  simp only [Eop]
  set R1 := lieS E a i j (atEmb τ 1)
  set R2 := lieS E a j i (atEmb τ 1)
  set I1 := lieS E a i j (atEmb τ Complex.I)
  set I2 := lieS E a j i (atEmb τ Complex.I)
  simp only [sq, smul_add, smul_sub, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring_nf

end GlobalTheory.LapSplit

namespace GlobalTheory.LapSplit

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem sum_cas_conjugate :
    ∑ τ : E →+* ℂ, Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate τ)) =
      ∑ τ : E →+* ℂ, Formalism.REAL.Cas (Eop (a := a) τ) := by
  let e : (E →+* ℂ) ≃ (E →+* ℂ) :=
    ⟨ComplexEmbedding.conjugate, ComplexEmbedding.conjugate, fun σ => star_star σ, fun σ => star_star σ⟩
  exact Equiv.sum_comp e (fun τ => Formalism.REAL.Cas (Eop (a := a) τ))

end GlobalTheory.LapSplit

namespace GlobalTheory.HCAlpha

theorem lapOp_eq_casKOp_add_cas (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) :
    lapOp E a = (2 : ℂ) • casKOp E a + ∑ τ : E →+* ℂ, (4 : ℂ) • Formalism.REAL.Cas (Eop (a := a) τ) := by
  have h4 : ∀ τ : E →+* ℂ, (4 : ℂ) • Formalism.REAL.Cas (Eop (a := a) τ) =
      (2 : ℂ) • Formalism.REAL.Cas (Eop (a := a) τ) + (2 : ℂ) • Formalism.REAL.Cas (Eop (a := a) τ) := fun τ => by
    rw [← add_smul]; norm_num
  unfold lapOp casKOp
  rw [Finset.sum_congr rfl fun τ _ => GlobalTheory.LapSplit.lap_summand (a := a) τ]
  simp only [ Finset.sum_add_distrib, h4, ← Finset.smul_sum,
    GlobalTheory.LapSplit.sum_cas_conjugate]
  abel

end GlobalTheory.HCAlpha
