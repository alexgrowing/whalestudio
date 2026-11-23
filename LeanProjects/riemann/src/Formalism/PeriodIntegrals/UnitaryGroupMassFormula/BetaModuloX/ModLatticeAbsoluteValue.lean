import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.MinkFix

noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.UnitaryGroupMassFormula.BetaModX

section MX

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem xsp_le_orth {T' : E} (F' : LFlag S r T') : Xsp F' ≤ orth S (Xsp F') := by
  intro v hv
  rw [mem_orth']
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    induction hv using Submodule.span_induction with
    | mem y' hy' =>
      obtain ⟨b, rfl⟩ := hy'
      exact F'.fl.e_iso a b
    | zero => simp
    | add y y' _ _ h1 h2 => simp [h1, h2]
    | smul c y _ h1 => simp [h1]
  | zero => simp
  | add y y' _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h1 => simp [h1]

theorem mod_lattice_absolute_value : ModXAbs := by
  intro E _ _ _ S r T' g F' Λ γ hτ hT hg hΛ hpos hA hXγ hz hcong v hv
  have hX : ∀ w, γ w ∈ Xsp F' ↔ w ∈ Xsp F' := by
    intro w
    constructor
    · intro h
      rw [← hXγ] at h
      obtain ⟨w', hw', he⟩ := h
      rw [← γ.injective he]
      exact hw'
    · intro h
      rw [← hXγ]
      exact ⟨w, h, rfl⟩
  have hiso : ∀ x y, S.hT (γ x) (γ y) = S.hT x y := hA.1
  have hU := orth_iff F' γ hiso hX
  obtain ⟨n, hn, hpow⟩ := γQ_finOrd F' hT hτ hpos Λ hΛ γ hA hU hX hz
  let φ : Qt F' →ₗ[E] Qt F' := (γQ F' γ hU hX : Qt F' →ₗ[E] Qt F')
  have hφL : ∀ x ∈ Lb F' Λ, φ x ∈ Lb F' Λ := by
    intro x hx
    have h := γQ_Lb F' Λ γ hU hX hA
    rw [← h]
    exact ⟨x, hx, rfl⟩
  have hk : ∀ (k : ℕ) (x : Qt F'), φ^[k] x = (γQ F' γ hU hX ^ k) x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', ih, pow_succ']
      rfl
  have hpow' : ∀ x, φ^[n] x = x := by
    intro x
    rw [hk, hpow]
    rfl
  have hgE : ((g : ℕ) : E) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  have hcongQ : ∀ x ∈ Lb F' Λ, ∃ y ∈ Lb F' Λ, φ x - x = g • y := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (mem_Lb F' Λ).1 hx
    have hw : (a : S.V) ∈ Lrep Λ F' := ⟨ha, a.2⟩
    obtain ⟨s, hs, ξ, hξ, hsξ⟩ := Submodule.mem_sup.1 (hcong a hw)
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hs
    obtain ⟨l, hl, rfl⟩ := hs
    have hξX : ξ ∈ Xsp F' := hξ.2
    have hgl : ((g : ℕ) : E) • l = γ a - a - ξ := by
      rw [← hsξ, ← algebraMap_smul E ((g : ℕ) : 𝓞 E) l, map_natCast]
      abel
    have hlU : l ∈ Uo F' := by
      have h1 : γ a - a - ξ ∈ Uo F' :=
        sub_mem (sub_mem ((hU a).2 a.2) a.2) (xsp_le_orth F' hξX)
      have : l = ((g : ℕ) : E)⁻¹ • (γ a - a - ξ) := by
        rw [← hgl, smul_smul, inv_mul_cancel₀ hgE, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ h1
    refine ⟨Submodule.Quotient.mk ⟨l, hlU⟩, (mem_Lb F' Λ).2 ⟨⟨l, hlU⟩, hl, rfl⟩, ?_⟩
    show γQ F' γ hU hX (Submodule.Quotient.mk a) - Submodule.Quotient.mk a =
      g • (Submodule.Quotient.mk ⟨l, hlU⟩ : Qt F')
    rw [γQ_mk, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    show ((γU F' γ hU a - a - g • (⟨l, hlU⟩ : Uo F') : Uo F') : S.V) ∈ Xsp F'
    have hco : ((γU F' γ hU a - a - g • (⟨l, hlU⟩ : Uo F') : Uo F') : S.V) = ξ := by
      have e2 : ((g • (⟨l, hlU⟩ : Uo F') : Uo F') : S.V) = g • l := by simp
      rw [Submodule.coe_sub, Submodule.coe_sub, e2, γU_coe]
      have e : (g • l : S.V) = ((g : ℕ) : E) • l := (Nat.cast_smul_eq_nsmul E g l).symm
      rw [e, hgl]
      abel
    rw [hco]
    exact hξX
  have hfix := mink_fix (Lb F' Λ) (Lb_lattice F' Λ hΛ).fg φ hφL n hn hpow' g hg hcongQ
  have hall : ∀ q, φ q = q := by
    have hle : Submodule.span E (Lb F' Λ : Set (Qt F')) ≤
        LinearMap.ker (φ - LinearMap.id : Qt F' →ₗ[E] Qt F') := by
      rw [Submodule.span_le]
      intro x hx
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hfix x hx, sub_self]
    intro q
    have hq : q ∈ LinearMap.ker (φ - LinearMap.id : Qt F' →ₗ[E] Qt F') :=
      hle (by rw [(Lb_lattice F' Λ hΛ).span_eq_top]; trivial)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hq
    exact hq
  have h := hall (Submodule.Quotient.mk ⟨v, hv⟩)
  change Submodule.Quotient.mk (γU F' γ hU ⟨v, hv⟩) = Submodule.Quotient.mk (p := Pk F') ⟨v, hv⟩ at h
  rw [Submodule.Quotient.eq] at h
  exact h

end MX

end PI.UnitaryGroupMassFormula.BetaModX
