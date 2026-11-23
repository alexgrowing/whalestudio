import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemSpanIffSpanS

open Module

noncomputable section

namespace Formalism.L2.SG.Pf.TemperedBoundGL3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

section

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem form_sums {J : Type} [Fintype J] {b : J → V} (ho : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (c d : J → K) :
    h (∑ i, c i • b i) (∑ i, d i • b i) = ∑ i, star (c i) * d i * h (b i) (b i) := by
  rw [map_sum h, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smulₛₗ₂, G3.form_sum_orth ho d i, starRingEnd_apply, smul_eq_mul, mul_assoc]

theorem sum_filter_smul {J : Type} [Fintype J] (p : J → Prop) [DecidablePred p] (x : J → K)
    (b : J → V) :
    ∑ i ∈ Finset.univ.filter p, x i • b i = ∑ i, (if p i then x i else 0) • b i := by
  simp only [Finset.sum_filter, ite_smul, zero_smul]

private theorem unit_mul_lemma {a b : K} (ha : IsUnitIn S a) (hb : IsUnitIn S b) :
    IsUnitIn S (a * b) := by
  obtain ⟨ha0, haS, haI⟩ := ha
  obtain ⟨hb0, hbS, hbI⟩ := hb
  refine (⟨mul_ne_zero ha0 hb0, S.mul_mem haS hbS, ?_⟩ : a * b ≠ 0 ∧ a * b ∈ S ∧ (a * b)⁻¹ ∈ S)
  rw [mul_inv]
  exact S.mul_mem haI hbI

private theorem unit_add_dv_lemma_2 (hπ : IsUnif S π) {u d : K} (hu : IsUnitIn S u) (hd : Dv S π d) :
    IsUnitIn S (u + d) := by
  have hu' : u ≠ 0 ∧ u ∈ S ∧ u⁻¹ ∈ S := hu
  have hd' : d * π⁻¹ ∈ S := hd
  have e : u * (1 + π * (u⁻¹ * (d * π⁻¹))) = u + d := by
    rw [mul_add, mul_one, mul_left_comm u π, mul_inv_cancel_left₀ hu'.1, mul_left_comm π d,
      mul_inv_cancel₀ hπ.3, mul_one]
  rw [← e]
  exact unit_mul_lemma hu (hπ.5 _ (S.mul_mem hu'.2.2 hd'))

theorem rebaseAt_of (hS : IsHermSemilocal S) (hπ : IsUnif S π)
    (hUP : ∀ (J : Type) [Fintype J] [DecidableEq J] (b : J → V) (e : J → ℕ) (i₀ : J),
      (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
      ∀ x : J → K, (∀ i, x i ∈ S) →
      IsUnitIn S (h (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i)
        (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i) * (π ^ e i₀)⁻¹) →
      ∃ c : J → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧
        (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧
        c i₀ = ∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i ∧
        (∀ k, e k ≠ e i₀ → c k = b k) ∧
        Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
        ∀ v, v ∈ G3.spanS S c ↔ v ∈ G3.spanS S b)
    (hAB : ∀ (J : Type) [Fintype J] [DecidableEq J] (e : J → ℕ) (i₀ : J) (x : J → K),
      (∀ i, x i ∈ S) → ∀ T : Finset J, i₀ ∉ T → (∀ j ∈ T, e i₀ < e j) → ∀ b : J → V,
      (∀ i j, i ≠ j → h (b i) (b j) = 0) → (∀ i, IsUnitIn S (h (b i) (b i) * (π ^ e i)⁻¹)) →
      ∃ c : J → V, (∀ i j, i ≠ j → h (c i) (c j) = 0) ∧
        (∀ i, IsUnitIn S (h (c i) (c i) * (π ^ e i)⁻¹)) ∧
        c i₀ = b i₀ + ∑ j ∈ T, x j • b j ∧ (∀ k, k ≠ i₀ → k ∉ T → c k = b k) ∧
        Submodule.span K (Set.range c) = Submodule.span K (Set.range b) ∧
        ∀ v, v ∈ G3.spanS S c ↔ v ∈ G3.spanS S b) :
    G3.RebaseAt S π h := by
  intro J _ _ b e i₀ ho hu hmin X hX hXu
  obtain ⟨x, hxS, rfl⟩ := hX
  have hπ0 : π ≠ 0 := hπ.3
  have hterm : ∀ i, e i ≠ e i₀ →
      Dv S π (star (x i) * x i * h (b i) (b i) * (π ^ e i₀)⁻¹) := by
    intro i hi
    have hlt : e i₀ < e i := lt_of_le_of_ne (hmin i) (Ne.symm hi)
    have hP : π ^ e i ≠ 0 := pow_ne_zero _ hπ0
    have hw : h (b i) (b i) * (π ^ e i)⁻¹ ∈ S := (show _ ∧ _ ∧ _ from hu i).2.1
    have hs : star (x i) * x i * (h (b i) (b i) * (π ^ e i)⁻¹) ∈ S :=
      S.mul_mem (S.mul_mem (hS.1 _ (hxS i)) (hxS i)) hw
    have hk : Dv S π (π ^ e i * (π ^ e i₀)⁻¹) := by
      rw [← pow_sub₀ π hπ0 (hmin i)]
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hlt
      show π ^ (e i - e i₀) * π⁻¹ ∈ S
      rw [hm, show e i₀ + m + 1 - e i₀ = m + 1 by omega, pow_succ, mul_inv_cancel_right₀ hπ0]
      exact S.pow_mem hπ.1 m
    have e1 : star (x i) * x i * h (b i) (b i) * (π ^ e i₀)⁻¹ =
        star (x i) * x i * (h (b i) (b i) * (π ^ e i)⁻¹) * (π ^ e i * (π ^ e i₀)⁻¹) := by
      rw [mul_assoc _ (_ * _⁻¹), mul_assoc (h (b i) (b i)), inv_mul_cancel_left₀ hP, ← mul_assoc]
    rw [e1]
    exact Dv.mul_left hk hs
  have hD : Dv S π (h (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i)
      (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i) * (π ^ e i₀)⁻¹ -
      h (∑ i, x i • b i) (∑ i, x i • b i) * (π ^ e i₀)⁻¹) := by
    rw [sum_filter_smul, form_sums ho, form_sums ho, ← sub_mul, ← Finset.sum_sub_distrib,
      Finset.sum_mul]
    refine Finset.sum_induction _ (Dv S π) (fun _ _ ha hb => Dv.add ha hb) ?_ fun i _ => ?_
    · show (0 : K) * π⁻¹ ∈ S
      rw [zero_mul]
      exact S.zero_mem
    · by_cases hi : e i = e i₀
      · rw [if_pos hi, sub_self, zero_mul]
        show (0 : K) * π⁻¹ ∈ S
        rw [zero_mul]
        exact S.zero_mem
      · rw [if_neg hi, star_zero, zero_mul, zero_mul, zero_sub, neg_mul]
        exact Dv.neg (hterm i hi)
  have hYu : IsUnitIn S (h (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i)
      (∑ i ∈ Finset.univ.filter (fun i => e i = e i₀), x i • b i) * (π ^ e i₀)⁻¹) := by
    have e2 : ∀ p q : K, p + (q - p) = q := fun p q => by ring
    have := unit_add_dv_lemma_2 hπ hXu hD
    rwa [e2] at this
  obtain ⟨c, hco, hcu, hci0, hck, hspan, hspanS⟩ := hUP J b e i₀ ho hu x hxS hYu
  have hi₀T : i₀ ∉ Finset.univ.filter (fun j => ¬ e j = e i₀) := fun hm =>
    (Finset.mem_filter.mp hm).2 rfl
  have hTlt : ∀ j ∈ Finset.univ.filter (fun j => ¬ e j = e i₀), e i₀ < e j := fun j hj =>
    lt_of_le_of_ne (hmin j) (Ne.symm (Finset.mem_filter.mp hj).2)
  obtain ⟨c', hco', hcu', hc'i0, hc'k, hspan', hspanS'⟩ :=
    hAB J e i₀ x hxS _ hi₀T hTlt c hco hcu
  have hT' : ∑ j ∈ Finset.univ.filter (fun j => ¬ e j = e i₀), x j • c j =
      ∑ j ∈ Finset.univ.filter (fun j => ¬ e j = e i₀), x j • b j :=
    Finset.sum_congr rfl fun j hj => by rw [hck j (Finset.mem_filter.mp hj).2]
  refine ⟨c', hco', hcu', ?_, hspan'.trans hspan, fun v => (hspanS' v).trans (hspanS v)⟩
  rw [hc'i0, hci0, hT', Finset.sum_filter_add_sum_filter_not]

end

end Formalism.L2.SG.Pf.TemperedBoundGL3
