import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.HeckeExp

variable {D : D7}

open Classical in

theorem exists_idele_at {θ : InfF D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (w : ℂ) (hw : w ≠ 0) :
    ∃ x : (AE D)ˣ, finPart D (x : AE D) = 1 ∧ ∀ τ', θ τ' (infPart D (x : AE D)) = if τ' = τ then w else 1 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  have key : ∀ w : ℂ, ∃ x : AE D, finPart D x = 1 ∧ ∀ τ', θ τ' (infPart D x) = if τ' = τ then w else 1 := fun w =>
    ⟨1 + σ fun τ' => (if τ' = τ then w else 1) - 1,
      by rw [RingHom.map_add, hσ.fin, RingHom.map_one, add_zero], fun τ' => by
      rw [RingHom.map_add, RingHom.map_add, hσ.comp, RingHom.map_one, RingHom.map_one]; ring⟩
  obtain ⟨x, hx1, hx2⟩ := key w
  obtain ⟨y, hy1, hy2⟩ := key w⁻¹
  have hxy : x * y = 1 := by
    rw [← sub_eq_zero]
    refine hσ.ext _ (by rw [RingHom.map_sub, RingHom.map_mul, hx1, hy1, RingHom.map_one, one_mul, sub_self]) fun τ' => ?_
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, hx2, hy2, RingHom.map_one, RingHom.map_one,
      sub_eq_zero]
    split_ifs
    · exact mul_inv_cancel₀ hw
    · exact one_mul 1
  have hyx : y * x = 1 := (mul_comm y x).trans hxy
  refine ⟨⟨x, y, hxy, hyx⟩, ?_, ?_⟩
  · rw [Units.val_mk]; exact hx1
  · rw [Units.val_mk]; exact hx2

theorem arg_ne_zero (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (x : (AE D)ˣ) :
    θ (infPart D (x : AE D)) / (‖θ (infPart D (x : AE D))‖ : ℂ) ≠ 0 := by
  have h : θ (infPart D (x : AE D)) ≠ 0 := ((x.isUnit.map (infPart D)).map θ).ne_zero
  exact div_ne_zero h (by exact_mod_cast norm_ne_zero_iff.2 h)

theorem eq_of_zpow_eq {n m : ℤ} (h : ∀ w : ℂ, ‖w‖ = 1 → w ^ n = w ^ m) : n = m := by
  by_contra hne
  have hd : ((n - m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hne
  have h1 := h (Complex.exp ((Real.pi / ((n - m : ℤ) : ℝ) : ℝ) * Complex.I)) (Complex.norm_exp_ofReal_mul_I _)
  have h2 : Complex.exp ((Real.pi / ((n - m : ℤ) : ℝ) : ℝ) * Complex.I) ^ (n - m) = 1 := by
    rw [zpow_sub₀ (Complex.exp_ne_zero _), h1, div_self (zpow_ne_zero _ (Complex.exp_ne_zero _))]
  have hd' : ((n - m : ℤ) : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hne
  have e : ((n - m : ℤ) : ℂ) * (((Real.pi / ((n - m : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
    rw [Complex.ofReal_div, Complex.ofReal_intCast]; field_simp
  rw [← Complex.exp_int_mul, e, Complex.exp_pi_mul_I] at h2
  norm_num at h2

theorem hasInfExp_unique {χ : IdC D} {τ : D.what₂.Tau} {a a' : ℚ} (h : HasInfExp D χ τ a) (h' : HasInfExp D χ τ a') :
    a = a' := by
  obtain ⟨n, hn, ⟨θ, hθ⟩, h1⟩ := h
  obtain ⟨m, hm, -, h2⟩ := h'
  have e : n = m := eq_of_zpow_eq fun w hw => by
    obtain ⟨x, hx1, hx2⟩ := exists_idele_at hθ τ w (by rintro rfl; simp at hw)
    have ho : ∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1 := fun τ' hτ => by rw [hx2, if_neg hτ]
    have e1 := h1 θ hθ x hx1 ho
    have e2 := h2 θ hθ x hx1 ho
    rw [hx2, if_pos rfl, hw, Complex.ofReal_one, div_one] at e1 e2
    exact e1.symm.trans e2
  subst e
  linarith

theorem hasInfExp_mul {χ χ' : IdC D} {τ : D.what₂.Tau} {a a' : ℚ} (h : HasInfExp D χ τ a) (h' : HasInfExp D χ' τ a') :
    HasInfExp D (χ * χ') τ (a + a') := by
  obtain ⟨n, hn, h0, h1⟩ := h
  obtain ⟨m, hm, -, h2⟩ := h'
  refine ⟨n + m, by push_cast; rw [hn, hm]; ring, h0, fun θ hθ x hx hτ => ?_⟩
  rw [MonoidHom.mul_apply, Circle.coe_mul, h1 θ hθ x hx hτ, h2 θ hθ x hx hτ, zpow_add₀ (arg_ne_zero _ x)]

theorem hasInfExp_inv {χ : IdC D} {τ : D.what₂.Tau} {a : ℚ} (h : HasInfExp D χ τ a) : HasInfExp D χ⁻¹ τ (-a) := by
  obtain ⟨n, hn, h0, h1⟩ := h
  refine ⟨-n, by push_cast; rw [hn]; ring, h0, fun θ hθ x hx hτ => ?_⟩
  rw [MonoidHom.inv_apply, Circle.coe_inv, h1 θ hθ x hx hτ, _root_.zpow_neg]

def hcSubgroup (D : D7) : Subgroup (IdC D) where
  carrier := {χ | IsHC D χ}
  one_mem' := isHC_one D
  mul_mem' := fun {χ χ'} h h' =>
    ⟨⟨h.1.1.mul h'.1.1, fun x => by rw [MonoidHom.mul_apply, h.1.2, h'.1.2, one_mul]⟩, fun τ =>
      (h.2 τ).elim fun _ ha => (h'.2 τ).elim fun _ ha' => ⟨_, hasInfExp_mul ha ha'⟩⟩
  inv_mem' := fun {χ} h =>
    ⟨⟨h.1.1.inv, fun x => by rw [MonoidHom.inv_apply, h.1.2, inv_one]⟩, fun τ =>
      (h.2 τ).elim fun _ ha => ⟨_, hasInfExp_inv ha⟩⟩

theorem hecke_exp_laws : ∀ D : D7, (∃ C : Subgroup (IdC D), ∀ χ, χ ∈ C ↔ IsHC D χ) ∧
    (∀ (χ : IdC D) τ a a', HasInfExp D χ τ a → HasInfExp D χ τ a' → a = a') ∧
    ∀ (χ χ' : IdC D) τ a a', HasInfExp D χ τ a → HasInfExp D χ' τ a' → HasInfExp D (χ * χ') τ (a + a') :=
  fun D => ⟨⟨hcSubgroup D, fun _ => Iff.rfl⟩, fun _ _ _ _ => hasInfExp_unique, fun _ _ _ _ _ => hasInfExp_mul⟩

end GlobalTheory.Mem.HeckeExp

end
