import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.Statement
import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SplitD
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

open ReciprocityTheory.ChartRestriction.DS.S7

open Matrix TensorProduct ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW

variable {n : ℕ} {ε : Fin n → Bool}

theorem sp_blk_surj' (ε : Fin n → Bool) (c : Bool) (a : Fin n) (h : ε a = c) : ∃ r, blk ε c r = a := by
  subst h
  exact sp_blk_surj ε a

theorem sp_tens_ne (Λ' : Fin n → ℝ) (T1 : KType (fun _ : Fin (cnt ε true) => true) (fun r => Λ' (blk ε true r)))
    (T2 : KType (fun _ : Fin (cnt ε false) => true) (fun r => Λ' (blk ε false r))) :
    (T1.w ⊗ₜ[ℂ] T2.w) ≠ 0 := by
  intro h
  have e := norm_tmul T1.w T2.w (𝕜 := ℂ)
  rw [h, norm_zero, T1.w_norm, T2.w_norm] at e
  norm_num at e

theorem sp_tens_hw (Λ' : Fin n → ℝ) (T1 : KType (fun _ : Fin (cnt ε true) => true) (fun r => Λ' (blk ε true r)))
    (T2 : KType (fun _ : Fin (cnt ε false) => true) (fun r => Λ' (blk ε false r))) :
    Formalism.REAL.KHighest ε (sp_rep T1 T2).units Λ' (T1.w ⊗ₜ[ℂ] T2.w) := by
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · cases hc : ε a
    · obtain ⟨r, rfl⟩ := sp_blk_surj' ε false a hc
      rw [sp_units_false, TensorProduct.map_tmul, LinearMap.id_apply]
      show T1.w ⊗ₜ (T2.dτ (single r r 1) T2.w) = _
      rw [T2.w_wt r, TensorProduct.tmul_smul]; rfl
    · obtain ⟨r, rfl⟩ := sp_blk_surj' ε true a hc
      rw [sp_units_true, TensorProduct.map_tmul, LinearMap.id_apply]
      show (T1.dτ (single r r 1) T1.w) ⊗ₜ T2.w = _
      rw [T1.w_wt r, ← TensorProduct.smul_tmul']; rfl
  · cases hc : ε a
    · obtain ⟨r, rfl⟩ := sp_blk_surj' ε false a hc
      obtain ⟨s, rfl⟩ := sp_blk_surj' ε false b (he ▸ hc)
      have hrs : r < s := (blk_strictMono ε false).lt_iff_lt.mp hab
      rw [sp_units_false, TensorProduct.map_tmul, LinearMap.id_apply]
      show T1.w ⊗ₜ (T2.dτ (single r s 1) T2.w) = 0
      rw [T2.w_hw r s hrs rfl, TensorProduct.tmul_zero]
    · obtain ⟨r, rfl⟩ := sp_blk_surj' ε true a hc
      obtain ⟨s, rfl⟩ := sp_blk_surj' ε true b (he ▸ hc)
      have hrs : r < s := (blk_strictMono ε true).lt_iff_lt.mp hab
      rw [sp_units_true, TensorProduct.map_tmul, LinearMap.id_apply]
      show (T1.dτ (single r s 1) T1.w) ⊗ₜ T2.w = 0
      rw [T1.w_hw r s hrs rfl, TensorProduct.zero_tmul]

theorem sp_tens_uniq {Λ1 : Fin (cnt ε true) → ℝ} {Λ2 : Fin (cnt ε false) → ℝ}
    (T1 : KType (fun _ : Fin (cnt ε true) => true) Λ1) (T2 : KType (fun _ : Fin (cnt ε false) => true) Λ2)
    (μ : Fin n → ℝ) (y : (sp_rep T1 T2).V) (hy : y ≠ 0)
    (h : Formalism.REAL.KHighest ε (sp_rep T1 T2).units μ y) : ∃ c : ℂ, y = c • (T1.w ⊗ₜ[ℂ] T2.w) := by
  obtain ⟨hwt, hr⟩ := h
  refine sp_ker T1 T2 y hy (fun r => μ (blk ε true r)) (fun r => μ (blk ε false r)) ?_ ?_ ?_ ?_
  · intro r; have e := hwt (blk ε true r); exact (sp_units_true T1 T2 r r y).symm.trans e
  · intro r s hrs
    have e := hr _ _ (blk_strictMono ε true hrs) (by rw [blk_mem ε true r, blk_mem ε true s])
    exact (sp_units_true T1 T2 r s y).symm.trans e
  · intro r; have e := hwt (blk ε false r); exact (sp_units_false T1 T2 r r y).symm.trans e
  · intro r s hrs
    have e := hr _ _ (blk_strictMono ε false hrs) (by rw [blk_mem ε false r, blk_mem ε false s])
    exact (sp_units_false T1 T2 r s y).symm.trans e

theorem sp_kChar (Λ' : Fin n → ℝ) (T : KType ε Λ')
    (T1 : KType (fun _ : Fin (cnt ε true) => true) (fun r => Λ' (blk ε true r)))
    (T2 : KType (fun _ : Fin (cnt ε false) => true) (fun r => Λ' (blk ε false r))) (k : KG ε) :
    kChar T k = kChar T1 (sp_proj ε true k) * kChar T2 (sp_proj ε false k) := by
  unfold kChar
  rw [sp_trace_of_rep T (sp_rep T1 T2) _ (sp_tens_ne Λ' T1 T2) (sp_tens_hw Λ' T1 T2)
    (fun μ y hy h => sp_tens_uniq T1 T2 μ y hy h) k, sp_rep_op]
  rw [show ((mapL (T1.op (sp_proj ε true k)) (T2.op (sp_proj ε false k)) : _ →L[ℂ] _) : _ →ₗ[ℂ] _) =
      TensorProduct.map (T1.op (sp_proj ε true k) : T1.V →ₗ[ℂ] T1.V)
        (T2.op (sp_proj ε false k) : T2.V →ₗ[ℂ] T2.V) from toLinearMap_mapL _ _]
  exact LinearMap.trace_tensorProduct' _ _

theorem kCharGT_of (hU : UCharStatement) : KCharGTStatement := by
  intro n ε Λ hdom T k t hk
  have hd : ∀ c, ∀ a b : Fin (cnt ε c), a < b → (fun _ => true) a = (fun _ => true) b →
      (((Λ ∘ blk ε c) b : ℤ) : ℝ) ≤ (((Λ ∘ blk ε c) a : ℤ) : ℝ) :=
    fun c a b hab _ => by exact_mod_cast antitone_blk hdom c hab.le
  obtain ⟨T1⟩ := kType_exists_of_dom (fun _ : Fin (cnt ε true) => true)
    (fun r => (((Λ ∘ blk ε true) r : ℤ) : ℝ)) (fun a => ⟨_, rfl⟩) (hd true)
  obtain ⟨T2⟩ := kType_exists_of_dom (fun _ : Fin (cnt ε false) => true)
    (fun r => (((Λ ∘ blk ε false) r : ℤ) : ℝ)) (fun a => ⟨_, rfl⟩) (hd false)
  rw [sp_kChar (fun a => (Λ a : ℝ)) T T1 T2 k,
    hU _ _ (antitone_blk hdom true) T1 (sp_proj ε true k) (t ∘ blk ε true)
      (by rw [sp_toMK_proj, hk, sp_sub_diag]),
    hU _ _ (antitone_blk hdom false) T2 (sp_proj ε false k) (t ∘ blk ε false)
      (by rw [sp_toMK_proj, hk, sp_sub_diag])]

end ReciprocityTheory.ChartRestriction.TR.Weyl
