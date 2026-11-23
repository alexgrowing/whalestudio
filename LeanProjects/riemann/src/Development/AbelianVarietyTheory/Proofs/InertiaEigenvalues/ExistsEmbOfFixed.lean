import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.Letters

theorem exists_emb_of_fixed {F E L : Type} [Field F] [Field E] [Field L] [Algebra F E] [Algebra F L]
    [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : Function.Bijective σ)
    (hfix : ∀ x, σ x = x → ∃ c : F, algebraMap F E c = x) (e : E →ₐ[F] L) :
    ∃ emb : ZMod (Module.finrank F E) → (E →ₐ[F] L),
      Function.Bijective emb ∧ ∀ i, (emb (i + 1)).comp σ = emb i := by
  classical
  let g : E ≃ₐ[F] E := AlgEquiv.ofBijective σ hσ
  have hbot : IntermediateField.fixedField (Subgroup.zpowers g) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    exact IntermediateField.mem_bot.2 (hfix x (hx g (Subgroup.mem_zpowers g)))
  have hord : orderOf g = Module.finrank F E := by
    have h := IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers g)
    rw [hbot, IntermediateField.finrank_bot', Nat.card_zpowers] at h
    exact h.symm
  haveI : NeZero (Module.finrank F E) := ⟨Module.finrank_pos.ne'⟩
  let emb : ZMod (Module.finrank F E) → (E →ₐ[F] L) := fun i =>
    e.comp (g⁻¹ ^ i.val : E ≃ₐ[F] E).toAlgHom
  have hord' : orderOf g⁻¹ = Module.finrank F E := by rw [orderOf_inv, hord]
  have hinj : Function.Injective emb := by
    intro i j h
    have h1 : (g⁻¹ ^ i.val : E ≃ₐ[F] E) = g⁻¹ ^ j.val :=
      AlgEquiv.ext fun x => e.injective (DFunLike.congr_fun h x)
    rw [pow_eq_pow_iff_modEq, hord', ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val] at h1
    exact h1
  refine ⟨emb, ?_, fun i => ?_⟩
  · refine hinj.bijective_of_nat_card_le ?_
    rw [Nat.card_zmod]
    exact card_algHom_le_finrank F E L
  · have h1 : (g⁻¹ ^ (i + 1).val : E ≃ₐ[F] E) = g⁻¹ ^ (i.val + 1) := by
      rw [pow_eq_pow_iff_modEq, hord', ← ZMod.natCast_eq_natCast_iff]
      simp
    have h2 : (g⁻¹ ^ (i + 1).val : E ≃ₐ[F] E) * g = g⁻¹ ^ i.val := by
      rw [h1, pow_succ, inv_mul_cancel_right]
    exact AlgHom.ext fun x => congrArg e (DFunLike.congr_fun h2 x)

variable {l : ℕ} [Fact l.Prime]

theorem sigma_fixed (P : LocPrime l) (K : FinExt l) (x : ↥(K0 K)) (hx : (P.PD K).σ x = x) :
    ∃ c : ℚ_[l], algebraMap ℚ_[l] ↥(K0 K) c = x := by
  haveI : Nontrivial P.R.B := by
    refine ⟨⟨(P.PD K).t, 0, fun h => (P.PD K).not_mem_filtration_two ?_⟩⟩
    rw [h, map_zero]
    exact zero_mem _
  obtain ⟨c, hc⟩ := (P.PD K).fund (algebraMap ↥(K0 K) P.R.B x) (by rw [(P.PD K).φ_K₀, hx]) (by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 P.R.BdR,
      Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (P.PD K).one_mem)
  refine ⟨c, (algebraMap ↥(K0 K) P.R.B).injective ?_⟩
  rw [← IsScalarTower.algebraMap_apply, hc]

end GlobalTheory.HWL.Letters

namespace GlobalTheory.HWL

theorem exists_letters : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∃ emb : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1), Function.Bijective emb ∧ ∀ i, (emb (i + 1)).comp (P.PD K).σ = emb i := by
  intro l _ P K s LL h
  haveI := (P.PD K).finK₀
  have hle : K0 K ≤ LL.1 := fun x hx =>
    h.2.2.2 (Ks K s).val ⟨x, (le_sup_left : K0 K ≤ Ks K s) hx⟩
  exact Letters.exists_emb_of_fixed _ (P.PD K).σ_bij (Letters.sigma_fixed P K)
    (IntermediateField.inclusion hle)

end GlobalTheory.HWL
