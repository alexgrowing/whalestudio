import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL.ConvCancel

theorem finite_pairs {F : Type} [Field F] (P : F[X]) (hP : P ≠ 0) :
    {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}.Finite := by
  classical
  have hfin : {g : F[X] | g.Monic ∧ g ∣ P}.Finite := by
    have h := Polynomial.fintypeSubtypeMonicDvd P hP
    exact @Finite.of_fintype _ h
  refine (hfin.prod hfin).subset ?_
  rintro ⟨D, E⟩ ⟨hD, hE, h⟩
  exact ⟨⟨hD, Dvd.intro _ h⟩, ⟨hE, Dvd.intro_left _ h⟩⟩

theorem conv_cancel : ∀ (F : Type) [Field F] (a b m : F[X] → ℂ), m 1 = 1 →
    (∀ P : F[X], P.Monic → conv a m P = conv b m P) → ∀ P : F[X], P.Monic → a P = b P := by
  intro F _ a b m hm h P
  classical
  induction hn : P.natDegree using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    intro hP
    have hfin := finite_pairs P hP.ne_zero
    have h1 := h P hP
    unfold conv at h1
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin] at h1
    have hmem : ((P, 1) : F[X] × F[X]) ∈ hfin.toFinset := by
      simp [hP]
    rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ _ hmem] at h1
    have h2 : ∑ x ∈ hfin.toFinset.erase (P, 1), a x.1 * m x.2
        = ∑ x ∈ hfin.toFinset.erase (P, 1), b x.1 * m x.2 := by
      refine Finset.sum_congr rfl ?_
      rintro ⟨D, E⟩ hx
      rw [Finset.mem_erase, Set.Finite.mem_toFinset] at hx
      obtain ⟨hne, hD, hE, hDE⟩ := hx
      simp only at hD hE hDE ⊢
      have hE1 : E ≠ 1 := by
        rintro rfl
        apply hne
        rw [← hDE, mul_one]
      have hdeg : D.natDegree < n := by
        rw [← hn, ← hDE, hD.natDegree_mul hE]
        have : E.natDegree ≠ 0 := fun h0 => hE1 (hE.natDegree_eq_zero.mp h0)
        omega
      rw [ih _ hdeg D rfl hD]
    rw [h2] at h1
    simpa [hm] using h1

end GlobalTheory.CuspGL.ConvCancel
