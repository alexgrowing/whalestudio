import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

section Components

variable {S : Type} [AddCommGroup S] [Module ℂ S] {d : ℕ}

private def cmp (j : Fin d) : S ⊗[ℂ] (Fin d → ℂ) →ₗ[ℂ] S :=
  (TensorProduct.rid ℂ S).toLinearMap ∘ₗ (LinearMap.proj j : (Fin d → ℂ) →ₗ[ℂ] ℂ).lTensor S

private theorem cmp_tmul (j : Fin d) (φ : S) (v : Fin d → ℂ) : cmp j (φ ⊗ₜ[ℂ] v) = v j • φ := by
  simp [cmp]

private theorem sum_cmp (m : S ⊗[ℂ] (Fin d → ℂ)) :
    ∑ j, cmp j m ⊗ₜ[ℂ] (Pi.single j 1 : Fin d → ℂ) = m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
    simp only [cmp_tmul, TensorProduct.smul_tmul]
    rw [← TensorProduct.tmul_sum]
    congr 1
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]

private theorem cmp_sum (L : Module.End ℂ S) (c : ℂ) (j : Fin d) (m : S ⊗[ℂ] (Fin d → ℂ)) :
    cmp j ((L.rTensor (Fin d → ℂ) + (Matrix.toLin' (c • (1 : Matrix (Fin d) (Fin d) ℂ))).lTensor S) m) =
      L (cmp j m) + c • cmp j m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v => simp [cmp_tmul, smul_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, smul_add]; abel

end Components

private theorem cmp_apply {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a d : ℕ}
    (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) (g : GA E a) : (cmp j m).1 g = ev m g j := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v => simp [cmp_tmul, mul_comm]
  | add x y hx hy => simp [hx, hy]

theorem levelVal : LevelVal := by
  intro E _ _ _ a U Ξ m
  refine ⟨fun hm => ?_, fun hl hr h0 => ?_⟩
  · induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, v, hφ, rfl⟩ := hx
      refine ⟨fun γ g => ?_, fun u hu g => ?_⟩
      · rw [ev_tmul, ev_tmul, hφ.1]
      · have h : φ.1 (g * finGL E a u) = φ.1 g := congrFun (congrArg Subtype.val (hφ.2.1 u hu)) g
        rw [ev_tmul, ev_tmul, h]
    | zero => exact ⟨fun γ g => by simp, fun u _ g => by simp⟩
    | add x y _ _ hx hy =>
      exact ⟨fun γ g => by simp only [map_add, Pi.add_apply, hx.1 γ g, hy.1 γ g],
        fun u hu g => by simp only [map_add, Pi.add_apply, hx.2 u hu g, hy.2 u hu g]⟩
    | smul c x _ hx =>
      exact ⟨fun γ g => by simp only [map_smul, Pi.smul_apply, hx.1 γ g],
        fun u hu g => by simp only [map_smul, Pi.smul_apply, hx.2 u hu g]⟩
  · rw [← sum_cmp m]
    refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨cmp j m, _, ⟨fun γ g => ?_, fun u hu => ?_, fun c hc => ?_⟩, rfl⟩
    · rw [cmp_apply, cmp_apply, hl]
    · refine Subtype.ext (funext fun g => ?_)
      change (cmp j m).1 (g * finGL E a u) = (cmp j m).1 g
      rw [cmp_apply, cmp_apply, hr u hu]
    · have h := cmp_sum (lie E a (oneL E a)) c j m
      rw [← hc] at h
      have h1 : cmp j (smLie Ξ (oneL E a) m) = 0 := by rw [h0, map_zero]
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left (h.symm.trans h1)

end UpperTheory.V.Lit.Dr
