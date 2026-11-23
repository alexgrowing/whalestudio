import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

open GlobalTheory.FinGL Formalism.L2.DIV Module

namespace GlobalTheory.FinGL.MackeyRadical

theorem exists_elem {F : Type} [Field F] {r : ℕ} {i j : Fin r} (h : i ≠ j) (t : F) :
    ∃ g : GL (Fin r) F, ∀ k l, (g : Matrix (Fin r) (Fin r) F) k l =
      (1 : Matrix (Fin r) (Fin r) F) k l + if i = k ∧ j = l then t else 0 := by
  refine ⟨⟨Matrix.transvection i j t, Matrix.transvection i j (-t), ?_, ?_⟩, fun k l => ?_⟩
  · rw [Matrix.transvection_mul_transvection_same _ _ h, add_neg_cancel, Matrix.transvection_zero]
  · rw [Matrix.transvection_mul_transvection_same _ _ h, neg_add_cancel, Matrix.transvection_zero]
  · simp [Matrix.transvection, Matrix.single]

theorem eig_eq_bot_of_radical : ∀ (F : Type) [Field F] (ψ : AddChar F ℂ) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → ∀ (j : ℕ) (w : Equiv.Perm (Fin r)) (x : GL (Fin r) F), (∀ (g : GL (Fin r) F) (a c : Fin r), ((x⁻¹ * g * x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) a c = (g : Matrix (Fin r) (Fin r) F) (w a) (w c)) → ψ ≠ 1 → ∀ a c : Fin r, cutEdge j a c → b (w a) < b (w c) → eig σ {p | x⁻¹ * (p : GL (Fin r) F) * x ∈ unip F r} (fun p => ψ (edgeSum (cutEdge j) (x⁻¹ * (p : GL (Fin r) F) * x))) = ⊥ := by
  intro F _ ψ r V _ _ b σ hσ j w x hx hψ a c hac hb
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push Not at h
    exact hψ (DFunLike.ext _ _ fun t => by simpa using h t)
  have hne : w a ≠ w c := fun h => by rw [h] at hb; exact lt_irrefl _ hb
  have hlt : a.val < c.val := by have := hac.1; omega
  obtain ⟨g, hg⟩ := exists_elem hne t
  have hgb : g ∈ blockTri (κ := F) b := by
    refine mem_blockTri.2 fun k l hkl => ?_
    have hkl' : k ≠ l := fun h => by rw [h] at hkl; exact lt_irrefl _ hkl
    rw [hg, Matrix.one_apply_ne hkl', if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_asymm hb hkl
  have h1 : σ ⟨g, hgb⟩ = 1 := by
    refine hσ.infl _ fun k l hkl => ?_
    show (g : Matrix (Fin r) (Fin r) F) k l = _
    rw [hg, if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact hb.ne hkl
  have hc : ∀ k l, ((x⁻¹ * g * x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) k l =
      (1 : Matrix (Fin r) (Fin r) F) k l + if a = k ∧ c = l then t else 0 := by
    intro k l
    rw [hx, hg]
    simp [Matrix.one_apply]
  have hu : x⁻¹ * g * x ∈ unip F r := by
    refine ⟨mem_blockTri.2 fun k l hkl => ?_, fun k => ?_⟩
    · have hkl' : k ≠ l := fun h => by rw [h] at hkl; exact lt_irrefl _ hkl
      rw [hc, Matrix.one_apply_ne hkl', if_neg, add_zero]
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hlt hkl
    · rw [hc, Matrix.one_apply_eq, if_neg, add_zero]
      rintro ⟨rfl, rfl⟩
      exact lt_irrefl _ hlt
  have hs : edgeSum (cutEdge j) (x⁻¹ * g * x) = t := by
    unfold edgeSum
    have key : ∀ k l : Fin r, (if cutEdge j k l then ((x⁻¹ * g * x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) k l else 0) =
        if l = c then (if k = a then t else 0) else 0 := by
      intro k l
      by_cases h : cutEdge j k l
      · have hkl : k ≠ l := fun e => by have := h.1; rw [e] at this; omega
        rw [if_pos h, hc, Matrix.one_apply_ne hkl, zero_add]
        by_cases h1 : l = c <;> by_cases h2 : k = a <;> simp [h1, h2, @eq_comm _ a k, @eq_comm _ c l]
      · rw [if_neg h]
        by_cases h1 : l = c <;> by_cases h2 : k = a <;> simp [h1, h2]
        subst h1 h2
        exact absurd hac h
    simp only [key]
    simp
  refine eq_bot_iff.2 fun v hv => ?_
  simp only [eig, Submodule.mem_iInf, LinearMap.mem_ker] at hv
  have := hv ⟨g, hgb⟩ hu
  simp only [h1, hs, LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply, LinearMap.id_apply] at this
  have h2 : (1 - ψ t) • v = 0 := by rw [sub_smul, one_smul]; exact this
  rcases smul_eq_zero.1 h2 with h | h
  · exact absurd (sub_eq_zero.1 h).symm ht
  · exact h

end GlobalTheory.FinGL.MackeyRadical
