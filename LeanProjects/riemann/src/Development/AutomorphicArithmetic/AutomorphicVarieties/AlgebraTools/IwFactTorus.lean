import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMemIwC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.AlgebraTools

open GlobalTheory.IwahoriTraceProof

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem unipO_le (C : Subgroup 𝓀[k]ˣ) : unipO k n ≤ iwC k n C := le_sup_of_le_left le_sup_right

private theorem KOne_le (C : Subgroup 𝓀[k]ˣ) : KOne k (Fin n) ≤ iwC k n C := le_sup_of_le_left le_sup_left

private theorem iwC_le (C : Subgroup 𝓀[k]ˣ) : iwC k n C ≤ iwahori k (Fin n) :=
  fun g hg => (((memIwC k n C).1 g).1 hg).1

private theorem inf_U (C : Subgroup 𝓀[k]ˣ) : unipB k (Fin n) ⊓ iwC k n C = unipO k n :=
  le_antisymm (inf_le_inf_left _ ((iwC_le C).trans (iwahori_le_KO k _))) (le_inf inf_le_left (unipO_le C))

private theorem inf_L (C : Subgroup 𝓀[k]ˣ) :
    unipBLower k (Fin n) ⊓ iwC k n C = unipBLower k (Fin n) ⊓ KOne k (Fin n) := by
  refine le_antisymm (fun c hc => ⟨hc.1, GlobalTheory.StepData.mem_KOne.2 fun i j => ?_⟩) (inf_le_inf_left _ (KOne_le C))
  obtain ⟨h2, h3⟩ := mem_unipBLower.1 hc.1
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h2 i j h, one_apply_ne h.ne]
  · simp [h3 i]
  · simpa [one_apply_ne h.ne'] using (mem_iwahori.1 (iwC_le C hc.2)).2 i j h

private theorem dom_le {t : Fin n → kˣ} (ht : Dom t) {i j : Fin n} (h : i ≤ j) :
    valuation k ((t i * (t j)⁻¹ : kˣ) : k) ≤ 1 := by
  rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
  exact mul_inv_le_one_of_le₀ (ht i j h) zero_le

private theorem dom_U {t : Fin n → kˣ} (ht : Dom t) :
    ∀ u ∈ unipO k n, diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ ∈ unipO k n := by
  have key : ∀ u ∈ unipO k n, GlobalTheory.StepData.IntM
      (diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹).val := fun u hu i j => by
    rw [← map_inv, diag_mul_mul_diag]
    rcases lt_or_ge j i with h | h
    · rw [((mem_unipB k).1 hu.1).1 i j h, mul_zero]
      exact zero_mem _
    · exact mul_mem (dom_le ht h) (GlobalTheory.StepData.intM_of_mem_KO hu.2 i j)
  intro u hu
  refine ⟨conj_mem_unipB _ hu.1, GlobalTheory.StepData.mem_KO.2 ⟨key u hu, ?_⟩⟩
  convert key _ (inv_mem hu) using 2
  group

private theorem dom_L {t : Fin n → kˣ} (ht : Dom t) :
    ∀ u ∈ unipBLower k (Fin n) ⊓ KOne k (Fin n),
      (diagT k (Fin n) t)⁻¹ * u * diagT k (Fin n) t ∈ KOne k (Fin n) := by
  intro u hu
  have h1 := conj_mem_unipBLower t⁻¹ hu.1
  rw [map_inv, inv_inv] at h1
  refine GlobalTheory.StepData.mem_KOne.2 fun i j => ?_
  rcases lt_trichotomy i j with h | rfl | h
  · simp only [Matrix.sub_apply, (mem_unipBLower.1 h1).1 i j h, one_apply_ne h.ne, sub_self, map_zero, zero_lt_one]
  · simp only [Matrix.sub_apply, (mem_unipBLower.1 h1).2 i, one_apply_eq, sub_self, map_zero, zero_lt_one]
  · have h2 := GlobalTheory.StepData.mem_KOne.1 hu.2 i j
    rw [Matrix.sub_apply, one_apply_ne h.ne', sub_zero] at h2 ⊢
    rw [← map_inv, diag_mul_mul_diag, mul_comm (_ : kˣ), map_mul]
    exact (mul_le_of_le_one_left' (dom_le ht h.le)).trans_lt h2

private noncomputable def torFact (C : Subgroup 𝓀[k]ˣ) : LeviFact (iwC k n C) where
  Uf := unipB k (Fin n)
  Mf := (diagT k (Fin n)).range
  Lf := unipBLower k (Fin n)
  M_U := by
    rintro _ ⟨t, rfl⟩ u hu
    exact conj_mem_unipB t hu
  M_L := by
    rintro _ ⟨t, rfl⟩ u hu
    exact conj_mem_unipBLower t hu
  uniq := by
    rintro u hu _ ⟨t, rfl⟩ l hl e
    have e' : u⁻¹ = diagT k (Fin n) t * l := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, e])
    obtain ⟨a1, a2⟩ := (mem_unipB k).1 (inv_mem hu)
    obtain ⟨b1, b2⟩ := mem_unipBLower.1 hl
    have ent : ∀ i j, (u⁻¹).val i j = (t i : k) * l.val i j := fun i j => by
      rw [e', Units.val_mul, val_diagT, diagonal_mul]
    constructor
    · rw [← inv_eq_one]
      ext i j
      rcases lt_trichotomy i j with h | rfl | h
      · rw [ent, b1 i j h, mul_zero, Units.val_one, one_apply_ne h.ne]
      · rw [a2, Units.val_one, one_apply_eq]
      · rw [a1 i j h, Units.val_one, one_apply_ne h.ne']
    · have : t = 1 := funext fun i => Units.ext (by
        have := ent i i
        rw [a2, b2, mul_one] at this
        exact this.symm)
      rw [this, map_one]
  fact g hg := by
    obtain ⟨u, hu, d, -, c, hc, rfl⟩ := iwahori_factorisation (iwC_le C hg)
    have h1 : u ∈ iwC k n C := unipO_le C hu
    have h2 : c ∈ iwC k n C := KOne_le C hc.2
    refine ⟨u, ⟨hu.1, h1⟩, _, ⟨⟨d, rfl⟩, ?_⟩, c, ⟨hc.1, h2⟩, rfl⟩
    have := mul_mem (inv_mem h1) (mul_mem hg (inv_mem h2))
    rwa [mul_inv_cancel_right, inv_mul_cancel_left] at this

end

end UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.factTorus :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ), ∃ F : LeviFact (iwC k n C), F.Uf = unipB k (Fin n) ∧ F.Mf = (diagT k (Fin n)).range ∧ F.Lf = unipBLower k (Fin n) ∧ F.Uf ⊓ iwC k n C = unipO k n ∧ F.Lf ⊓ iwC k n C = unipBLower k (Fin n) ⊓ KOne k (Fin n) ∧ ∀ t : Fin n → kˣ, F.NormJ (diagT k (Fin n) t) ∧ (Dom t → F.Pos (diagT k (Fin n) t)) := by
  intro k _ _ _ _ n C
  refine ⟨torFact C, rfl, rfl, rfl, inf_U C, inf_L C, fun t => ⟨?_, fun ht => ⟨⟨t, rfl⟩, fun u hu => ?_, fun l hl => ?_⟩⟩⟩
  · rintro _ ⟨⟨s, rfl⟩, hs⟩
    have e : diagT k (Fin n) t * diagT k (Fin n) s = diagT k (Fin n) s * diagT k (Fin n) t := by
      rw [← map_mul, mul_comm, map_mul]
    constructor
    · rwa [e, mul_inv_cancel_right]
    · rwa [mul_assoc, ← e, inv_mul_cancel_left]
  · exact unipO_le C (dom_U ht u (inf_U C ▸ hu))
  · exact KOne_le C (dom_L ht l (inf_L C ▸ hl))
