import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairGluing.ConjTransposeMemLam

noncomputable section
open NumberField Matrix

namespace PI.SqPairW

open Formalism.L2.PairingIndexBounds.Eq.SqG

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}

theorem ringInt_smul (β : 𝓞 E) (w : Fin N → E) : β • w = (β : E) • w := by
  ext i
  rfl

theorem exists_nat_smul_mem {L : Submodule (𝓞 E) (Fin N → E)}
    (hL : Submodule.span E (L : Set (Fin N → E)) = ⊤) (v : Fin N → E) :
    ∃ k : ℕ, 0 < k ∧ (k : ℤ) • v ∈ L := by
  let T : Submodule E (Fin N → E) :=
    { carrier := {v | ∃ k : ℕ, 0 < k ∧ (k : ℤ) • v ∈ L}
      add_mem' := by
        rintro a b ⟨k1, hk1, ha⟩ ⟨k2, hk2, hb⟩
        refine ⟨k1 * k2, Nat.mul_pos hk1 hk2, ?_⟩
        have e1 : ((k1 * k2 : ℕ) : ℤ) • (a + b) = (k2 : ℤ) • ((k1 : ℤ) • a) + (k1 : ℤ) • ((k2 : ℤ) • b) := by
          push_cast
          module
        rw [e1]
        exact L.add_mem (L.toAddSubgroup.zsmul_mem ha _) (L.toAddSubgroup.zsmul_mem hb _)
      zero_mem' := ⟨1, one_pos, by simp⟩
      smul_mem' := by
        rintro c v ⟨k2, hk2, hv⟩
        obtain ⟨k1, hk1, β, hβ⟩ := exists_nat_mul_int c
        refine ⟨k1 * k2, Nat.mul_pos hk1 hk2, ?_⟩
        have e1 : ((k1 * k2 : ℕ) : ℤ) • (c • v) = β • ((k2 : ℤ) • v) := by
          rw [ringInt_smul, hβ, ← Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul E, smul_smul,
            smul_smul]
          push_cast
          congr 1
          ring
        rw [e1]
        exact L.smul_mem β hv }
  have hLT : L ≤ T.restrictScalars (𝓞 E) := fun v hv => ⟨1, one_pos, by simpa using hv⟩
  have hT : T = ⊤ := by
    rw [eq_top_iff, ← hL, Submodule.span_le]
    exact fun v hv => hLT hv
  have hv : v ∈ T := hT ▸ Submodule.mem_top
  exact hv

theorem exists_den_le {L' L'' : Submodule (𝓞 E) (Fin N → E)} (hfg : L'.FG)
    (hspan : Submodule.span E (L'' : Set (Fin N → E)) = ⊤) :
    ∃ D : ℕ, 0 < D ∧ ∀ w ∈ L', (D : ℤ) • w ∈ L'' := by
  obtain ⟨s, rfl⟩ := hfg
  have hk : ∀ x : s, ∃ k : ℕ, 0 < k ∧ (k : ℤ) • (x : Fin N → E) ∈ L'' :=
    fun x => exists_nat_smul_mem hspan x
  choose k hk0 hkL using hk
  refine ⟨∏ x, k x, Finset.prod_pos (fun x _ => hk0 x), ?_⟩
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm⟩ : k ⟨x, hx⟩ ∣ ∏ y, k y := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
    rw [hm, Nat.cast_mul, mul_comm, mul_smul]
    exact zsmul_mem (hkL ⟨x, hx⟩) _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [smul_comm]
    exact L''.smul_mem c hx

theorem exists_den {L' L'' : Submodule (𝓞 E) (Fin N → E)} (hL' : IsSDG E N L') (hL'' : IsSDG E N L'')
    {n : 𝓞 E} (hn : n ≠ 0) :
    ∃ D : ℕ, 0 < D ∧ ∀ w, (w ∈ L' ∨ w ∈ L'') → (D : ℤ) • w ∈ yg L' L'' n := by
  obtain ⟨D1, hD1, h1⟩ := exists_den_le hL'.1 hL''.2.1
  obtain ⟨D2, hD2, h2⟩ := exists_den_le hL''.1 hL'.2.1
  have hnE : (n : E) ≠ 0 := by exact_mod_cast hn
  obtain ⟨k, hk, β, hβ⟩ := exists_nat_mul_int (n : E)⁻¹
  have hkY : ∀ u, u ∈ L' → u ∈ L'' → (k : ℤ) • u ∈ yg L' L'' n := by
    intro u hu hu'
    refine ⟨β • u, L'.smul_mem β hu, L''.smul_mem β hu', ?_⟩
    rw [ringInt_smul, smul_smul, hβ, ← Int.cast_smul_eq_zsmul E]
    congr 1
    field_simp
    push_cast
    ring
  refine ⟨k * D1 * D2, Nat.mul_pos (Nat.mul_pos hk hD1) hD2, ?_⟩
  rintro w (hw | hw)
  · have hu : (D1 : ℤ) • w ∈ L'' := h1 w hw
    have hu' : (D1 : ℤ) • w ∈ L' := L'.toAddSubgroup.zsmul_mem hw _
    have e1 : ((k * D1 * D2 : ℕ) : ℤ) • w = (k : ℤ) • ((D2 : ℤ) • ((D1 : ℤ) • w)) := by
      push_cast
      module
    rw [e1]
    exact hkY _ (L'.toAddSubgroup.zsmul_mem hu' _) (L''.toAddSubgroup.zsmul_mem hu _)
  · have hu : (D2 : ℤ) • w ∈ L' := h2 w hw
    have hu' : (D2 : ℤ) • w ∈ L'' := L''.toAddSubgroup.zsmul_mem hw _
    have e1 : ((k * D1 * D2 : ℕ) : ℤ) • w = (k : ℤ) • ((D1 : ℤ) • ((D2 : ℤ) • w)) := by
      push_cast
      module
    rw [e1]
    exact hkY _ (L'.toAddSubgroup.zsmul_mem hu _) (L''.toAddSubgroup.zsmul_mem hu' _)

end PI.SqPairW
