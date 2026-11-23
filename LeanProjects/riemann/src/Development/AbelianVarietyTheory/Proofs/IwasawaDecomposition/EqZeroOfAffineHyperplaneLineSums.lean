import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.FiniteRadon

open Classical in

theorem card_annihilator_mul (k W : Type) [Field k] [Fintype k] [AddCommGroup W] [Module k W]
    [Fintype (Module.Dual k W)] (y : W) (hy : y ≠ 0) :
    Fintype.card k * (Finset.univ.filter (fun g : Module.Dual k W => g y = 0)).card
      = Fintype.card (Module.Dual k W) := by
  let ev : Module.Dual k W →ₗ[k] k := Module.Dual.eval k W y
  have hev : ∀ g, ev g = g y := fun g => rfl
  have hs : Function.Surjective ev := by
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k hy
    intro t
    exact ⟨t • f, by simp [hev, hf]⟩
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker ev)
  have h2 : Nat.card (Module.Dual k W ⧸ LinearMap.ker ev) = Nat.card k :=
    Nat.card_congr (ev.quotKerEquivOfSurjective hs).toEquiv
  have h3 : Nat.card (LinearMap.ker ev)
      = (Finset.univ.filter (fun g : Module.Dual k W => g y = 0)).card := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun g => by simp [LinearMap.mem_ker, hev]))
  rw [← h3, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h1, h2, mul_comm]

theorem eq_zero_of_hyperplane_sums (k W M : Type) [Field k] [Fintype k] [DecidableEq k]
    [AddCommGroup W] [Module k W] [Finite W] [AddCommGroup M] [Module ℂ M] (ψ : W → M)
    (_h0 : ψ 0 = 0)
    (h1 : ∀ g : Module.Dual k W, g ≠ 0 → ∑ᶠ x ∈ {x | g x = 1}, ψ x = 0)
    (h2 : ∀ x, ∑ a : kˣ, ψ ((a : k) • x) = 0) (x0 : W) : ψ x0 = 0 := by
  classical
  haveI : Fintype W := Fintype.ofFinite W
  haveI : Finite (Module.Dual k W) :=
    Finite.of_injective (fun g : Module.Dual k W => (g : W → k)) DFunLike.coe_injective
  haveI : Fintype (Module.Dual k W) := Fintype.ofFinite _
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have hcancel : ∀ (n : ℕ) (m : M), n ≠ 0 → n • m = 0 → m = 0 := by
    intro n m hn h
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [← Nat.cast_smul_eq_nsmul ℂ] at h
    rw [← one_smul ℂ m, ← inv_mul_cancel₀ hn', mul_smul, h, smul_zero]
  have A : ∀ (g : Module.Dual k W) (t : k), ∑ x, (if g x = t then ψ x else 0) = 0 := by
    intro g t
    by_cases ht : t = 0
    · subst ht
      apply hcancel (Fintype.card kˣ) _ Fintype.card_ne_zero
      have e : ∀ a : kˣ, ∑ x, (if g x = 0 then ψ x else 0)
          = ∑ x, (if g x = 0 then ψ ((a : k) • x) else 0) := by
        intro a
        rw [← Equiv.sum_comp (MulAction.toPerm a)]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp [MulAction.toPerm, Units.smul_def]
      rw [← Finset.card_univ, ← Finset.sum_const, Finset.sum_congr rfl (fun a _ => e a),
        Finset.sum_comm]
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hx : g x = 0
      · simp only [hx, if_true]; exact h2 x
      · simp [hx]
    · by_cases hg : g = 0
      · subst hg
        refine Finset.sum_eq_zero fun x _ => ?_
        simp [Ne.symm ht]
      · have h := h1 (t⁻¹ • g) (smul_ne_zero (inv_ne_zero ht) hg)
        rw [finsum_mem_def, finsum_eq_sum_of_fintype] at h
        refine Eq.trans ?_ h
        refine Finset.sum_congr rfl fun x _ => ?_
        have : (t⁻¹ • g) x = 1 ↔ g x = t := by
          simp only [LinearMap.smul_apply, smul_eq_mul]
          rw [inv_mul_eq_one₀ ht, eq_comm]
        simp only [Set.indicator_apply, Set.mem_setOf_eq, this]
  have T : ∑ x, ψ x = 0 := by simpa using A 0 0
  have B : ∑ x, (Finset.univ.filter (fun g : Module.Dual k W => g (x - x0) = 0)).card • ψ x
      = 0 := by
    have : ∑ g : Module.Dual k W, ∑ x, (if g x = g x0 then ψ x else 0) = 0 :=
      Finset.sum_eq_zero fun g _ => A g _
    rw [Finset.sum_comm] at this
    rw [← this]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const]
    simp only [map_sub, sub_eq_zero]
  set N := Fintype.card (Module.Dual k W) with hN
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card k = r + 1 := ⟨Fintype.card k - 1, by omega⟩
  have C : ∀ x, Fintype.card k •
      ((Finset.univ.filter (fun g : Module.Dual k W => g (x - x0) = 0)).card • ψ x)
      = N • ψ x + (if x = x0 then (r * N) • ψ x0 else 0) := by
    intro x
    rw [← mul_smul]
    by_cases hx : x = x0
    · subst hx
      simp only [sub_self, map_zero, Finset.filter_true, Finset.card_univ, if_true, hr]
      rw [← add_smul]; congr 1; ring
    · have := card_annihilator_mul k W (x - x0) (sub_ne_zero.mpr hx)
      rw [if_neg hx, add_zero, hN, ← this]
      congr!
  have D := congrArg (fun m => Fintype.card k • m) B
  simp only [Finset.smul_sum, C] at D
  simp only [smul_zero, Finset.sum_add_distrib, ← Finset.smul_sum, T,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_add] at D
  exact hcancel _ _ (Nat.mul_ne_zero (show r ≠ 0 by omega) Fintype.card_ne_zero) D

end GlobalTheory.FiniteRadon
