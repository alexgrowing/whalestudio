import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.SqSplit

theorem natCast_sub_eq_neg {p n : ℕ} (h : n ≤ p) : ((p - n : ℕ) : ZMod p) = -((n : ℕ) : ZMod p) := by
  rw [Nat.cast_sub h, ZMod.natCast_self, zero_sub]

theorem neg_one_not_isSquare {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3) : ¬ IsSquare (-1 : ZMod p) := by
  rw [ZMod.exists_sq_eq_neg_one_iff]; omega

theorem ringChar_ne_two {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; omega

theorem isSquare_neg_of_not {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3) {a : ZMod p} (ha : a ≠ 0)
    (hs : ¬ IsSquare a) : IsSquare (-a) := by
  have hc := ringChar_ne_two h3
  have h1 : quadraticChar (ZMod p) a = -1 := (quadraticChar_neg_one_iff_not_isSquare).2 hs
  have h2 : quadraticChar (ZMod p) (-1) = -1 :=
    (quadraticChar_neg_one_iff_not_isSquare).2 (neg_one_not_isSquare h3)
  have hna : -a ≠ 0 := neg_ne_zero.2 ha
  rw [← quadraticChar_one_iff_isSquare hna, neg_eq_neg_one_mul, map_mul, h1, h2]; norm_num

theorem not_both {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3) {a : ZMod p} (ha : a ≠ 0)
    (h1 : IsSquare a) (h2 : IsSquare (-a)) : False := by
  apply neg_one_not_isSquare h3
  have : (-1 : ZMod p) = -a * a⁻¹ := by rw [neg_mul, mul_inv_cancel₀ ha]
  rw [this]; exact h2.mul h1.inv

end GlobalTheory.SqSplit

open GlobalTheory.SqSplit in
theorem GlobalTheory.sq_sum_equiv_Ico : ∀ (p : ℕ), p.Prime → p % 4 = 3 → ∃ e : Sq p ⊕ Sq p ≃ (Finset.Ico 1 p : Finset ℕ), ∀ k : Sq p, ((e (Sum.inl k) : ℕ) = (k.1 : ℕ)) ∧ ((e (Sum.inr k) : ℕ) = p - (k.1 : ℕ)) := by
  intro p hp h3
  haveI : Fact p.Prime := ⟨hp⟩
  have pos : ∀ k : Sq p, 1 ≤ (k.1 : ℕ) := by
    intro k
    rcases Nat.eq_zero_or_pos (k.1 : ℕ) with h | h
    · exact absurd (by rw [h]; simp) k.2.1
    · exact h
  let f : Sq p ⊕ Sq p → (Finset.Ico 1 p : Finset ℕ) := Sum.elim
    (fun k => ⟨(k.1 : ℕ), Finset.mem_Ico.2 ⟨pos k, k.1.2⟩⟩)
    (fun k => ⟨p - (k.1 : ℕ), Finset.mem_Ico.2 ⟨by have := k.1.2; omega, by have := pos k; omega⟩⟩)
  have hf : Function.Bijective f := by
    constructor
    · rintro (a | a) (b | b) hab <;> simp only [f, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at hab
      · exact congrArg Sum.inl (Subtype.ext (Fin.ext hab))
      · exfalso
        have hb := b.1.2
        have e1 : ((a.1 : ℕ) : ZMod p) = -((b.1 : ℕ) : ZMod p) := by
          rw [hab, natCast_sub_eq_neg hb.le]
        exact not_both h3 b.2.1 b.2.2 (e1 ▸ a.2.2)
      · exfalso
        have ha := a.1.2
        have e1 : ((b.1 : ℕ) : ZMod p) = -((a.1 : ℕ) : ZMod p) := by
          rw [← hab, natCast_sub_eq_neg ha.le]
        exact not_both h3 a.2.1 a.2.2 (e1 ▸ b.2.2)
      · have ha := a.1.2; have hb := b.1.2
        exact congrArg Sum.inr (Subtype.ext (Fin.ext (by omega)))
    · rintro ⟨n, hn⟩
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hn
      have hn0 : ((n : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd; exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
      by_cases hs : IsSquare ((n : ℕ) : ZMod p)
      · exact ⟨Sum.inl ⟨⟨n, h2⟩, hn0, hs⟩, rfl⟩
      · have hm : ((p - n : ℕ) : ZMod p) = -((n : ℕ) : ZMod p) := natCast_sub_eq_neg h2.le
        refine ⟨Sum.inr ⟨⟨p - n, by omega⟩, ?_, ?_⟩, ?_⟩
        · simp only; rw [hm]; exact neg_ne_zero.2 hn0
        · simp only; rw [hm]; exact isSquare_neg_of_not h3 hn0 hs
        · simp only [f, Sum.elim_inr]; apply Subtype.ext; simp only; omega
  exact ⟨Equiv.ofBijective f hf, fun k => ⟨rfl, rfl⟩⟩
