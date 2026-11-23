import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterComponentDegreeLowerBound
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.FockLowWt

open MvPolynomial Formalism.BasicNotions.TH

theorem monomial_mem_eig {P Q R S : ℕ} (α : Ln P Q R S →₀ ℕ)
    (h1 : ∀ (i : Fin P) (c : Fin S), α (Sum.inl i, Sum.inr c) = 0)
    (h2 : ∀ (j : Fin Q) (c : Fin R), α (Sum.inr j, Sum.inl c) = 0) (r : Fin R) (s : Fin S) :
    (monomial α 1 : Pol P Q R S) ∈
      Module.End.eigenspace (fockAct2 P Q R S (Eab (.inl r) (.inl r)))
          (((P : ℂ) - Q) / 2 + ((∑ i : Fin P, α (Sum.inl i, Sum.inl r) : ℕ) : ℂ)) ⊓
        Module.End.eigenspace (fockAct2 P Q R S (Eab (.inr s) (.inr s)))
          (-(((P : ℂ) - Q) / 2) + ((∑ j : Fin Q, α (Sum.inr j, Sum.inr s) : ℕ) : ℂ)) := by
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, cartan2]
    congr 1
    simp only [Fintype.sum_sum_type, lineSign, h2, one_mul, neg_one_mul, Nat.cast_zero, zero_add,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  · rw [Module.End.mem_eigenspace_iff, cartan2]
    congr 1
    simp only [Fintype.sum_sum_type, lineSign, h1, one_mul, neg_one_mul, Nat.cast_zero, zero_add,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring

theorem support_unmixed {P Q R S : ℕ} (x : ℚ) (k k' : ℕ) (hk : x - cPair R S = k)
    (hk' : x + cPair R S = k') (f : Pol P Q R S) (hf : f ∈ GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k'))
    (α : Ln P Q R S →₀ ℕ) (hα : coeff α f ≠ 0) :
    (∀ (i : Fin P) (c : Fin S), α (Sum.inl i, Sum.inr c) = 0) ∧
      ∀ (j : Fin Q) (c : Fin R), α (Sum.inr j, Sum.inl c) = 0 := by
  rw [GlobalTheory.KFixIrr.mem_lowOne, GlobalTheory.KFixIrr.mem_chiOne] at hf
  obtain ⟨hf, hdeg⟩ := hf
  have hval : ∀ a : Ix P Q, GlobalTheory.FockLowDeg.cartanVal a α = (x : ℂ) := by
    intro a
    have h := congrArg (coeff α) (hf _ (GlobalTheory.FockLowDeg.isKC_Eab_diag a))
    rw [GlobalTheory.FockLowDeg.coeff_cartan, GlobalTheory.FockLowDeg.trace_Eab_diag, mul_one, coeff_smul,
      smul_eq_mul] at h
    exact mul_right_cancel₀ hα h
  have hkC : (x : ℂ) - ((R : ℂ) - S) / 2 = k := by
    have := congrArg (fun t : ℚ => (t : ℂ)) hk
    simpa [cPair] using this
  have hk'C : (x : ℂ) + ((R : ℂ) - S) / 2 = k' := by
    have := congrArg (fun t : ℚ => (t : ℂ)) hk'
    simpa [cPair] using this
  have hP : ∀ i : Fin P, ∑ c : Fin R, α (Sum.inl i, Sum.inl c) =
      ∑ c : Fin S, α (Sum.inl i, Sum.inr c) + k := by
    intro i
    have h := hval (Sum.inl i)
    simp only [GlobalTheory.FockLowDeg.cartanVal, Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h
    have e : ((∑ c : Fin R, α (Sum.inl i, Sum.inl c) : ℕ) : ℂ) =
        ((∑ c : Fin S, α (Sum.inl i, Sum.inr c) + k : ℕ) : ℂ) := by
      push_cast
      linear_combination h + hkC
    exact Nat.cast_injective e
  have hQ : ∀ j : Fin Q, ∑ c : Fin S, α (Sum.inr j, Sum.inr c) =
      ∑ c : Fin R, α (Sum.inr j, Sum.inl c) + k' := by
    intro j
    have h := hval (Sum.inr j)
    simp only [GlobalTheory.FockLowDeg.cartanVal, Fintype.sum_sum_type, lineSign, one_mul, neg_one_mul,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h
    have e : ((∑ c : Fin S, α (Sum.inr j, Sum.inr c) : ℕ) : ℂ) =
        ((∑ c : Fin R, α (Sum.inr j, Sum.inl c) + k' : ℕ) : ℂ) := by
      push_cast
      linear_combination h + hk'C
    exact Nat.cast_injective e
  have hle := le_trans (MvPolynomial.le_totalDegree (mem_support_iff.mpr hα)) hdeg
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type, Fintype.sum_sum_type] at hle
  simp only [Fintype.sum_sum_type] at hle
  have e1 : ∑ i : Fin P, (∑ c : Fin R, α (Sum.inl i, Sum.inl c) + ∑ c : Fin S, α (Sum.inl i, Sum.inr c)) =
      P * k + 2 * ∑ i : Fin P, ∑ c : Fin S, α (Sum.inl i, Sum.inr c) := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [hP i])]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  have e2 : ∑ j : Fin Q, (∑ c : Fin R, α (Sum.inr j, Sum.inl c) + ∑ c : Fin S, α (Sum.inr j, Sum.inr c)) =
      Q * k' + 2 * ∑ j : Fin Q, ∑ c : Fin R, α (Sum.inr j, Sum.inl c) := by
    rw [Finset.sum_congr rfl (fun j _ => by rw [hQ j])]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  rw [e1, e2] at hle
  have z1 : ∑ i : Fin P, ∑ c : Fin S, α (Sum.inl i, Sum.inr c) = 0 := by omega
  have z2 : ∑ j : Fin Q, ∑ c : Fin R, α (Sum.inr j, Sum.inl c) = 0 := by omega
  rw [Finset.sum_eq_zero_iff] at z1 z2
  refine ⟨fun i c => ?_, fun j c => ?_⟩
  · exact (Finset.sum_eq_zero_iff.mp (z1 i (Finset.mem_univ _))) c (Finset.mem_univ _)
  · exact (Finset.sum_eq_zero_iff.mp (z2 j (Finset.mem_univ _))) c (Finset.mem_univ _)

theorem lowOne_le_wt : ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), x - Formalism.BasicNotions.TH.cPair R S = k →
    x + Formalism.BasicNotions.TH.cPair R S = k' →
    ∀ (r : Fin R) (s : Fin S), GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k') ≤ ⨆ n : ℕ × ℕ,
      Module.End.eigenspace (Formalism.BasicNotions.TH.fockAct2 P Q R S (Formalism.BasicNotions.TH.Eab (.inl r) (.inl r)))
          (((P : ℂ) - Q) / 2 + n.1) ⊓
      Module.End.eigenspace (Formalism.BasicNotions.TH.fockAct2 P Q R S (Formalism.BasicNotions.TH.Eab (.inr s) (.inr s)))
          (-(((P : ℂ) - Q) / 2) + n.2) := by
  intro P Q R S x k k' hk hk' r s f hf
  rw [← MvPolynomial.support_sum_monomial_coeff f]
  refine Submodule.sum_mem _ fun α hα => ?_
  obtain ⟨h1, h2⟩ := support_unmixed x k k' hk hk' f hf α (mem_support_iff.mp hα)
  have e : (monomial α (coeff α f) : Pol P Q R S) = coeff α f • monomial α 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e]
  refine Submodule.smul_mem _ _ ?_
  exact Submodule.mem_iSup_of_mem
    ((∑ i : Fin P, α (Sum.inl i, Sum.inl r)), (∑ j : Fin Q, α (Sum.inr j, Sum.inr s)))
    (monomial_mem_eig α h1 h2 r s)

end GlobalTheory.FockLowWt

end
