import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.MemOrth

noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.UnitaryGroupMassFormula.BetaModX

section Q2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem hQ_symm {T' : E} (F' : LFlag S r T') (c : E) (hc : star c = c) : (hQ F' c).IsSymm := by
  have key : ∀ x y : Qt F', starRingEnd E (hQ F' c x y) = hQ F' c y x := by
    intro x y
    induction x using Submodule.Quotient.induction_on with
    | H a =>
    induction y using Submodule.Quotient.induction_on with
    | H b =>
    rw [hQ_mk, hQ_mk, hV_apply, hV_apply, map_add, map_mul, map_mul, S.herm.eq, S.herm.eq, S.herm.eq,
      starRingEnd_apply c, hc]
    ring
  first
    | exact key
    | exact ⟨key⟩

theorem hV_pos {T' : ℕ} (F' : LFlag S r ((T' : ℕ) : E)) (hT : 0 < T')
    (hτ : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a))
    (hpos : ∀ τ : E →+* ℂ, ∀ w ∈ orth S (Xplus F'), w ∉ Xsp F' → 0 < (τ (S.hT w w)).re)
    (a : S.V) (ha : a ∈ orth S (Xsp F')) (haX : a ∉ Xsp F') (τ : E →+* ℂ) :
    0 < (τ (hV F' (2 / ((T' : ℕ) : E)) a a)).re := by
  have ht : (T' : E) ≠ 0 := by exact_mod_cast hT.ne'
  have hst : star (T' : E) = T' := star_natCast T'
  have hzz : S.hT F'.fl.z F'.fl.z = -(T' : E) := F'.fl.z_norm
  set h := S.hT F'.fl.z a with hh
  set w := a + (h / T') • F'.fl.z with hw
  have hzw : S.hT F'.fl.z w = 0 := by
    rw [hw, map_add, map_smul, smul_eq_mul, hzz, ← hh]
    field_simp
    ring
  have hww : S.hT w w = S.hT a a + h * star h / T' := by
    rw [hw]
    simp only [map_add, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_smul,
      smul_eq_mul, starRingEnd_apply, hzz]
    rw [herm' F'.fl.z a, ← hh, star_div₀, hst]
    field_simp
    ring
  have hid : hV F' (2 / (T' : E)) a a = S.hT w w + star (h / T') * (h / T') * T' := by
    rw [hV_apply, hww, herm' F'.fl.z a, ← hh, star_div₀, hst]
    field_simp
    ring
  have hterm : (τ (star (h / T') * (h / T') * T')).re = Complex.normSq (τ (h / T')) * T' := by
    rw [map_mul, map_mul, hτ, ← Complex.normSq_eq_conj_mul_self, map_natCast, ← Complex.ofReal_natCast,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have hXo : F'.fl.z ∈ orth S (Xsp F') := mem_orth'.mpr (hXz F')
  have hwo : w ∈ orth S (Xsp F') := by
    rw [hw]
    exact add_mem ha (Submodule.smul_mem _ _ hXo)
  clear_value w h
  rw [hid, map_add, Complex.add_re, hterm]
  by_cases hwX : w ∈ Xsp F'
  · have h0 : S.hT w w = 0 := mem_orth'.mp hwo w hwX
    have hν : h / (T' : E) ≠ 0 := by
      intro h0'
      apply haX
      rw [h0', zero_smul, add_zero] at hw
      exact hw ▸ hwX
    rw [h0, map_zero, Complex.zero_re, zero_add]
    have hn : 0 < Complex.normSq (τ (h / T')) := Complex.normSq_pos.mpr ((map_ne_zero τ).mpr hν)
    exact mul_pos hn (by exact_mod_cast hT)
  · have hwp : w ∈ orth S (Xplus F') := by
      rw [mem_orth']
      intro x hx
      obtain ⟨x1, hx1, x2, hx2, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx2
      rw [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, hzw, smul_zero,
        add_zero]
      exact mem_orth'.mp hwo x1 hx1
    have h1 := hpos τ w hwp hwX
    have h2 : 0 ≤ Complex.normSq (τ (h / T')) * T' :=
      mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)
    linarith

theorem hQ_trace_pos {T' : ℕ} (F' : LFlag S r ((T' : ℕ) : E)) (hT : 0 < T')
    (hτ : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a))
    (hpos : ∀ τ : E →+* ℂ, ∀ w ∈ orth S (Xplus F'), w ∉ Xsp F' → 0 < (τ (S.hT w w)).re)
    (q : Qt F') (hq : q ≠ 0) : 0 < Algebra.trace ℚ E (hQ F' (2 / ((T' : ℕ) : E)) q q) := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hb : (b : S.V) ∉ Xsp F' := by
    intro hbX
    apply hq
    rw [Submodule.Quotient.mk_eq_zero]
    exact hbX
  rw [hQ_mk]
  have hp : ∀ σ : E →ₐ[ℚ] ℂ, 0 < (σ (hV F' (2 / ((T' : ℕ) : E)) b b)).re := fun σ =>
    hV_pos F' hT hτ hpos b b.2 hb σ.toRingHom
  have _ : Nonempty (E →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have hre := congrArg Complex.re
    (trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ) (x := hV F' (2 / ((T' : ℕ) : E)) b b))
  rw [Complex.re_sum] at hre
  have hsum := Finset.sum_pos (fun σ _ => hp σ) (Finset.univ_nonempty (α := E →ₐ[ℚ] ℂ))
  rw [← hre, eq_ratCast, Complex.ratCast_re, Rat.cast_pos] at hsum
  exact hsum

end Q2

end PI.UnitaryGroupMassFormula.BetaModX
