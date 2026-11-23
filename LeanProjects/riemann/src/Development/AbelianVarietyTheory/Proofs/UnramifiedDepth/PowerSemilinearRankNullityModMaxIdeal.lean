import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.SemilinearNullity

variable {C : Type} [Field C] {V : VF C}

theorem mm_zero : V.MM (0 : C) := by simp [VF.MM]

theorem mm_int_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  unfold VF.MM; rw [V.v.map_mul]
  have ha' : (0 : WithTop ℝ) ≤ V.v a := ha
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left ha')

theorem mm_sub {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a - b) := by
  rw [sub_eq_add_neg]
  refine V.v.map_lt_add ha ?_
  rw [V.v.map_neg]; exact hb

theorem ge_of_pow {a : C} {n : ℕ} (hn : n ≠ 0) (h : V.Ge 0 (a ^ n)) : V.Ge 0 a := by
  have h' : (0 : WithTop ℝ) ≤ V.v (a ^ n) := h
  show (0 : WithTop ℝ) ≤ V.v a
  rw [V.v.map_pow] at h'
  by_contra hc
  exact absurd (nsmul_neg (not_le.mp hc) hn) (not_lt.mpr h')

theorem ge_inv {a : C} (h : ¬ V.MM a) : V.Ge 0 a⁻¹ := by
  have h0 : a ≠ 0 := by rintro rfl; exact h mm_zero
  show (0 : WithTop ℝ) ≤ V.v a⁻¹
  have e : V.v a⁻¹ + V.v a = 0 := by rw [← V.v.map_mul, inv_mul_cancel₀ h0, V.v.map_one]
  have h1 : V.v a ≤ 0 := not_lt.mp h
  calc (0 : WithTop ℝ) = V.v a⁻¹ + V.v a := e.symm
    _ ≤ V.v a⁻¹ := add_le_of_nonpos_right h1

def IndepOn (V : VF C) {m : ℕ} {σ : Type} (Y : Fin m → σ → C) (T : Finset (Fin m)) : Prop :=
  ∀ c : Fin m → C, (∀ δ, V.Ge 0 (c δ)) → (∀ δ, δ ∉ T → c δ = 0) →
    (∀ s, V.MM (∑ δ, c δ * Y δ s)) → ∀ δ, V.MM (c δ)

theorem IndepOn.indepMod {m : ℕ} {σ : Type} {Y : Fin m → σ → C} {T : Finset (Fin m)}
    (h : IndepOn V Y T) {N : ℕ} (f : Fin N ↪ Fin m) (hf : ∀ ν, f ν ∈ T) :
    IndepMod V (fun ν => Y (f ν)) := by
  intro c hc hs ν
  have key := h (fun δ => ∑ ν, if f ν = δ then c ν else 0) (fun δ => VF.Ge.sum fun ν _ => by
      split_ifs
      · exact hc ν
      · exact VF.Ge.zero 0)
    (fun δ hδ => Finset.sum_eq_zero fun ν _ => if_neg (by rintro rfl; exact hδ (hf ν)))
    (fun s => by
      convert hs s using 1
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ν _ => ?_
      simp) (f ν)
  simpa using key

theorem exists_relation {m : ℕ} {σ : Type} {Y : Fin m → σ → C} (hY : ∀ δ x, V.Ge 0 (Y δ x))
    {T : Finset (Fin m)} (hT : IndepOn V Y T) {δ : Fin m}
    (hn : ¬ IndepOn V Y (insert δ T)) :
    ∃ r : Fin m → C, (∀ ε, V.Ge 0 (r ε)) ∧ r δ = 1 ∧ (∀ ε, ε ∉ T → ε ≠ δ → r ε = 0) ∧
      ∀ s, V.MM (∑ ε, r ε * Y ε s) := by
  unfold IndepOn at hn
  push Not at hn
  obtain ⟨c, hc, hc0, hs, ε₀, hε₀⟩ := hn
  have hcd : ¬ V.MM (c δ) := by
    intro hm
    have key := hT (fun ε => if ε = δ then 0 else c ε) (fun ε => by
        split_ifs
        · exact VF.Ge.zero 0
        · exact hc ε)
      (fun ε hε => by
        split_ifs with h
        · rfl
        · exact hc0 ε (by simp [h, hε]))
      (fun s => by
        have h1 : V.MM (Y δ s * c δ) := mm_int_mul (hY δ s) hm
        convert mm_sub (hs s) h1 using 1
        rw [eq_sub_iff_add_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ δ),
          ← Finset.add_sum_erase _ (fun ε => c ε * Y ε s) (Finset.mem_univ δ)]
        rw [Finset.sum_congr rfl (g := fun ε => c ε * Y ε s)
          (fun ε hε => by rw [if_neg (Finset.ne_of_mem_erase hε)])]
        simp only [if_true]
        ring) ε₀
    by_cases h : ε₀ = δ
    · exact hε₀ (h ▸ hm)
    · exact hε₀ (by simpa [h] using key)
  have h0 : c δ ≠ 0 := by intro h; exact hcd (h ▸ mm_zero)
  refine ⟨fun ε => (c δ)⁻¹ * c ε, fun ε => (ge_inv hcd).mul_int (hc ε), inv_mul_cancel₀ h0,
    fun ε h1 h2 => ?_, fun s => ?_⟩
  · simp only [hc0 ε (by simp [h1, h2]), mul_zero]
  · convert mm_int_mul (ge_inv hcd) (hs s) using 1
    simp only [Finset.mul_sum, mul_assoc]

theorem rank_nullity : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (σ : Type) (m k Q : ℕ), 1 ≤ Q → ∀ Y : Fin m → σ → C, (∀ δ x, V.Ge 0 (Y δ x)) → (∀ (N : ℕ) (x : Fin N → Fin m → C), (∀ ν δ, V.Ge 0 (x ν δ)) → IndepMod V x → (∀ ν s, V.MM (∑ δ, x ν δ ^ Q * Y δ s)) → N ≤ k) → ∃ (m' : ℕ) (cc : Fin m' ↪ Fin m), m ≤ m' + k ∧ IndepMod V (fun ν => Y (cc ν)) := by
  intro C _ _ V σ m k Q hQ Y hY hk
  have hQ0 : Q ≠ 0 := by omega
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun T : Finset (Fin m) => IndepOn V Y T) Finset.card
    ⟨∅, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro c _ h0 _ δ
      rw [h0 δ (by simp)]
      exact mm_zero⟩
  have hT' : IndepOn V Y T := (Finset.mem_filter.1 hT).2
  have hn : ∀ δ, δ ∉ T → ¬ IndepOn V Y (insert δ T) := fun δ hδ h => by
    have := hmax _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    rw [Finset.card_insert_of_notMem hδ] at this
    omega
  have hrt : ∀ a : C, ∃ z : C, z ^ Q = a ∧ (a = 1 → z = 1) ∧ (a = 0 → z = 0) := by
    intro a
    by_cases h : a = 1
    · exact ⟨1, by simp [h], fun _ => rfl, fun h0 => absurd (h.symm.trans h0) one_ne_zero⟩
    · obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq a (Nat.pos_of_ne_zero hQ0)
      exact ⟨z, hz, fun h1 => absurd h1 h, fun h0 => pow_eq_zero_iff hQ0 |>.mp (hz.trans h0)⟩
  choose rt hrt hrt1 hrt0 using hrt
  let e : Fin Tᶜ.card ↪ Fin m := (Tᶜ.orderEmbOfFin rfl).toEmbedding
  have he : ∀ ν, e ν ∉ T := fun ν => Finset.mem_compl.1 (Finset.orderEmbOfFin_mem _ rfl ν)
  choose r hr hr1 hr0 hrs using fun ν => exists_relation hY hT' (hn _ (he ν))
  have hle := hk Tᶜ.card (fun ν δ => rt (r ν δ))
    (fun ν δ => ge_of_pow hQ0 (by rw [hrt]; exact hr ν δ))
    (fun c _ hs ν => by
      have h1 : V.MM (∑ b, c b * rt (r b (e ν))) := hs (e ν)
      rw [Finset.sum_eq_single ν (fun b _ hb => by
        rw [hrt0 _ (hr0 b _ (he ν) (fun h => hb (e.injective h).symm)), mul_zero])
        (fun h => absurd (Finset.mem_univ _) h), hrt1 _ (hr1 ν), mul_one] at h1
      exact h1)
    (fun ν s => by simp only [hrt]; exact hrs ν s)
  refine ⟨T.card, (T.orderEmbOfFin rfl).toEmbedding, ?_,
    hT'.indepMod _ fun ν => Finset.orderEmbOfFin_mem _ rfl ν⟩
  rw [Finset.card_compl, Fintype.card_fin] at hle
  omega

end GlobalTheory.SemilinearNullity
