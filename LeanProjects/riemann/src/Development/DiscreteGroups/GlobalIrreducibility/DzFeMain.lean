import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.RhoInvMulSelf
import Development.DiscreteGroups.GlobalIrreducibility.DzFeCard

noncomputable section

set_option linter.unusedSimpArgs false

open GlobalTheory.GLq GlobalTheory.Whittaker GlobalTheory.SmGL Matrix
open scoped Classical

namespace DiscreteGroups.sglob.DzFe

theorem fe : FunctionalEquationAtIndex := by
  intro g _ m ψ₀ hψ τ hτ γ hγ l hl j hj v hA hB
  have hm : 0 < m := by omega
  have hg : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero
  have hg1 : (g : ℂ) - 1 ≠ 0 := by
    have : g ≠ 1 := (Fact.out : g.Prime).ne_one
    exact sub_ne_zero.2 (by exact_mod_cast this)
  set K : ℕ := Fintype.card ({i : JIdx m j // i ≠ j0 m j} → ZMod g) with hK
  have hK0 : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hcardJ : (g : ℂ) ^ Fintype.card (JIdx m j) = (K : ℂ) * g := by
    have := sum_split (g := g) (m := m) j (fun _ => (1 : ℂ))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_fun, ZMod.card,
      Nat.cast_pow] at this
    rw [hK, Fintype.card_fun, ZMod.card, Nat.cast_pow]
    exact this
  set X : ℂ := l (τ.ρ (cyc g (m + 1))⁻¹ v) with hX
  have hL : ∑ N : SIdx m → ZMod g, ∑ b : JIdx m j → ZMod g,
      (ψ₀ (-superDiag (umGL N)) : ℂ) * l (sv ψ₀ τ (Um N * Hm (bcol b)) v) =
      (g : ℂ) ^ Fintype.card (SIdx m) * ((K : ℂ) * (((g : ℂ) - 1) * (γ * l v))) := by
    rw [Finset.sum_congr rfl (fun N _ => Finset.sum_congr rfl (fun b _ => lhs_term ψ₀ τ hγ hτ hm l hl v hA N b))]
    have hb : ∑ b : JIdx m j → ZMod g, (if b (j0 m j) = 0 then (0 : ℂ) else γ * l v) =
        (K : ℂ) * (((g : ℂ) - 1) * (γ * l v)) := by
      have hs := sum_split (g := g) (m := m) j (fun s => if s = 0 then (0 : ℂ) else γ * l v)
      rw [hs]
      congr 1
      have h2 : ∑ s : ZMod g, (if s = 0 then (0 : ℂ) else γ * l v) =
          ∑ _s : ZMod g, γ * l v - ∑ s : ZMod g, (if s = 0 then γ * l v else 0) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun s _ => by split_ifs <;> ring)
      rw [h2, Finset.sum_const, Finset.card_univ, ZMod.card, Finset.sum_ite_eq' Finset.univ (0 : ZMod g),
        if_pos (Finset.mem_univ _), nsmul_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun N _ => hb), Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card,
      nsmul_eq_mul]
    push_cast
    ring
  have e1 : ∀ (N : SIdx m → ZMod g) (b : JIdx m j → ZMod g),
      (ψ₀ (-superDiag (umGL N)) : ℂ) * l (sv ψ₀ τ (Um N * Hm (bcol b)) v) =
      ∑ y : Gn g (m + 1), (ψ₀ (-superDiag (umGL N)) : ℂ) *
        (ψ₀ (trace (Um N * Hm (bcol b) * (y : Mt g (m + 1)))) : ℂ) * l (τ.ρ y⁻¹ v) := by
    intro N b
    simp only [sv, map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun y _ => by ring)
  have hR : ∑ N : SIdx m → ZMod g, ∑ b : JIdx m j → ZMod g,
      (ψ₀ (-superDiag (umGL N)) : ℂ) * l (sv ψ₀ τ (Um N * Hm (bcol b)) v) =
      (g : ℂ) ^ Fintype.card (JIdx m j) * (g : ℂ) ^ Fintype.card (SIdx m) *
        ((Fintype.card ((SIdx m → ZMod g) × (ZMod g)ˣ × (WIdx m j → ZMod g)) : ℂ) * X) := by
    calc _ = ∑ N : SIdx m → ZMod g, ∑ b : JIdx m j → ZMod g, ∑ y : Gn g (m + 1),
          (ψ₀ (-superDiag (umGL N)) : ℂ) * (ψ₀ (trace (Um N * Hm (bcol b) * (y : Mt g (m + 1)))) : ℂ) *
            l (τ.ρ y⁻¹ v) := Finset.sum_congr rfl (fun N _ => Finset.sum_congr rfl (fun b _ => e1 N b))
      _ = ∑ N : SIdx m → ZMod g, ∑ y : Gn g (m + 1), ∑ b : JIdx m j → ZMod g,
          (ψ₀ (-superDiag (umGL N)) : ℂ) * (ψ₀ (trace (Um N * Hm (bcol b) * (y : Mt g (m + 1)))) : ℂ) *
            l (τ.ρ y⁻¹ v) := Finset.sum_congr rfl (fun N _ => Finset.sum_comm)
      _ = ∑ y : Gn g (m + 1), ∑ N : SIdx m → ZMod g, ∑ b : JIdx m j → ZMod g,
          (ψ₀ (-superDiag (umGL N)) : ℂ) * (ψ₀ (trace (Um N * Hm (bcol b) * (y : Mt g (m + 1)))) : ℂ) *
            l (τ.ρ y⁻¹ v) := Finset.sum_comm
      _ = ∑ y : Gn g (m + 1), (∑ N : SIdx m → ZMod g, ∑ b : JIdx m j → ZMod g,
          (ψ₀ (-superDiag (umGL N)) : ℂ) * (ψ₀ (trace (Um N * Hm (bcol b) * (y : Mt g (m + 1)))) : ℂ)) *
            l (τ.ρ y⁻¹ v) := Finset.sum_congr rfl (fun y _ => by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl (fun N _ => by rw [Finset.sum_mul]))
      _ = ∑ y : Gn g (m + 1), (if IsY j (y : Mt g (m + 1)) then
          (g : ℂ) ^ Fintype.card (JIdx m j) * (g : ℂ) ^ Fintype.card (SIdx m) *
            (ψ₀ (trace (y : Mt g (m + 1)) - (y : Mt g (m + 1)) 0 0) : ℂ) else 0) * l (τ.ρ y⁻¹ v) :=
          Finset.sum_congr rfl (fun y _ => by rw [kern ψ₀ hψ j])
      _ = (g : ℂ) ^ Fintype.card (JIdx m j) * (g : ℂ) ^ Fintype.card (SIdx m) *
          ∑ y : Gn g (m + 1), (if IsY j (y : Mt g (m + 1)) then
            (ψ₀ (trace (y : Mt g (m + 1)) - (y : Mt g (m + 1)) 0 0) : ℂ) * l (τ.ρ y⁻¹ v) else 0) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun y _ => by split_ifs <;> ring)
      _ = _ := by rw [rhs_sum ψ₀ τ hj l hl v hB]
  have e := hL.symm.trans hR
  have hg1le : 1 ≤ g := (Fact.out : g.Prime).one_le
  rw [hcardJ, card_P, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_sub hg1le,
    Nat.cast_one] at e
  have hne : (g : ℂ) ^ Fintype.card (SIdx m) * (K : ℂ) * ((g : ℂ) - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hg) hK0) hg1
  have key : γ * l v = (g : ℂ) * (g : ℂ) ^ Fintype.card (SIdx m) * (g : ℂ) ^ Fintype.card (WIdx m j) * X :=
    mul_left_cancel₀ hne (by linear_combination e)
  have hexp : (m + 1) * m / 2 + m - j = Fintype.card (SIdx m) + Fintype.card (WIdx m j) + 1 := by
    rw [card_SIdx, card_WIdx]
    generalize (m + 1) * m / 2 = A
    omega
  rw [hexp, pow_add, pow_add, pow_one, key]
  ring

end DiscreteGroups.sglob.DzFe
