import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Cartan
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab

open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLp

theorem cartan_decomposition (g : ℕ) [Fact g.Prime] (n : ℕ) (h : GL (Fin n) ℚ_[g]) :
    ∃ (k k' : GL (Fin n) ℤ_[g]) (a : Fin n → ℤ), Antitone a ∧ (h : Matrix (Fin n) (Fin n) ℚ_[g]) =
      (inc g n k : Matrix (Fin n) (Fin n) ℚ_[g]) * Matrix.diagonal (fun i => (g : ℚ_[g]) ^ a i) *
        (inc g n k' : Matrix (Fin n) (Fin n) ℚ_[g]) := by
  have hP : IsPrincipalIdealRing (PadicInt.subring g) :=
    inferInstanceAs (IsPrincipalIdealRing ℤ_[g])
  have hg0 : (g : ℚ_[g]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero
  obtain ⟨c, hc0, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ_[g])
    (fun ij : Fin n × Fin n => (h : Matrix (Fin n) (Fin n) ℚ_[g]) ij.1 ij.2) |>.imp
      (fun c hc => And.intro (nonZeroDivisors.coe_ne_zero c) hc)
  choose G hG using hc
  obtain ⟨a, ha, k₁, ⟨k, rfl⟩, k₂, ⟨k', rfl⟩, e⟩ :=
    Formalism.UG.P.cartan_decomp_gen (PadicInt.subring g) (NormedField.valuation (K := ℚ_[g]))
      (fun x => by
        rw [PadicInt.mem_subring_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]; rfl)
      (g : ℚ_[g]) hg0
      (fun x hx => ⟨x.valuation, by
        apply NNReal.coe_injective
        rw [NormedField.valuation_apply, NormedField.valuation_apply, NNReal.coe_zpow, coe_nnnorm,
          coe_nnnorm, Padic.norm_eq_zpow_neg_valuation hx, Padic.norm_p, inv_zpow']⟩)
      h (c : ℤ_[g]) hc0 ⟨Matrix.of fun i j => G (i, j), by
        ext i j
        exact hG (i, j)⟩
  exact ⟨k, k', a, ha, e⟩

end GlobalTheory.GLp
