import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

section Numbers

variable {E : Type*} [Field E] [NumberField E]

def scaledIdeal (I : AddSubgroup E) (hI : ∀ a : 𝓞 E, ∀ x ∈ I, (a : E) * x ∈ I) (b : E) :
    Ideal (𝓞 E) where
  carrier := {y | b⁻¹ * (y : E) ∈ I}
  add_mem' := by
    intro y z hy hz
    simp only [Set.mem_ofPred_eq] at *
    have h := I.add_mem hy hz
    convert h using 1
    push_cast
    ring
  zero_mem' := by simp [I.zero_mem]
  smul_mem' := by
    intro a y hy
    simp only [Set.mem_ofPred_eq, smul_eq_mul] at *
    have h := hI a _ hy
    convert h using 1
    push_cast
    ring

theorem mem_scaledIdeal {I : AddSubgroup E} {hI : ∀ a : 𝓞 E, ∀ x ∈ I, (a : E) * x ∈ I} {b : E}
    {y : 𝓞 E} : y ∈ scaledIdeal I hI b ↔ b⁻¹ * (y : E) ∈ I := Iff.rfl

end Numbers

theorem IdealClassesFinite.proof (E) [Field E] [NumberField E] : IdealClassesFinite.Statement E := by
  classical
  let rep : ClassGroup (𝓞 E) → nonZeroDivisors (Ideal (𝓞 E)) := fun c => (ClassGroup.mk0_surjective c).choose
  have hrep : ∀ c, ClassGroup.mk0 (rep c) = c := fun c => (ClassGroup.mk0_surjective c).choose_spec
  let J : ClassGroup (𝓞 E) → AddSubgroup E := fun c =>
    ((rep c : Ideal (𝓞 E)).toAddSubgroup).map (algebraMap (𝓞 E) E).toAddMonoidHom
  refine ⟨Set.range J, Set.finite_range J, ?_⟩
  intro I hfg hne hI
  obtain ⟨S, hS⟩ := hfg
  obtain ⟨⟨b, hb0⟩, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 E)) (S : Finset E)
  have hbne : (b : E) ≠ 0 := by
    have : b ≠ 0 := nonZeroDivisors.ne_zero hb0
    exact_mod_cast this
  have hint : ∀ x ∈ I, ∃ w : 𝓞 E, (w : E) = b * x := by
    intro x hx
    rw [← hS] at hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨w, hw⟩ := hb x hx
      exact ⟨w, by rw [Algebra.smul_def] at hw; exact hw⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨w, hw⟩ := hx
      obtain ⟨v, hv⟩ := hy
      exact ⟨w + v, by push_cast; linear_combination hw + hv⟩
    | neg x _ hx =>
      obtain ⟨w, hw⟩ := hx
      exact ⟨-w, by push_cast; linear_combination -hw⟩
  let 𝔞 := scaledIdeal I hI (b : E)
  have hmem : ∀ z ∈ I, ∀ w : 𝓞 E, (w : E) = b * z → w ∈ 𝔞 := by
    intro z hz w hw
    rw [mem_scaledIdeal, hw, ← mul_assoc, inv_mul_cancel₀ hbne, one_mul]
    exact hz
  have h𝔞 : 𝔞 ∈ nonZeroDivisors (Ideal (𝓞 E)) := by
    apply mem_nonZeroDivisors_of_ne_zero
    obtain ⟨z, hz, hz0⟩ := (AddSubgroup.bot_or_exists_ne_zero I).resolve_left hne
    obtain ⟨w, hw⟩ := hint z hz
    intro h0
    have hw𝔞 : w ∈ 𝔞 := hmem z hz w hw
    rw [h0, Submodule.zero_eq_bot, Ideal.mem_bot] at hw𝔞
    rw [hw𝔞] at hw
    push_cast at hw
    exact hz0 ((mul_eq_zero.1 hw.symm).resolve_left hbne)
  set c := ClassGroup.mk0 ⟨𝔞, h𝔞⟩
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 (hrep c).symm
  have hxE : (x : E) ≠ 0 := by exact_mod_cast hx
  have hyE : (y : E) ≠ 0 := by exact_mod_cast hy
  refine ⟨J c, ⟨c, rfl⟩, (y : E) / ((x : E) * b), div_ne_zero hyE (mul_ne_zero hxE hbne), ?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw⟩ := hint z hz
    have hxw : x * w ∈ Ideal.span {y} * (rep c : Ideal (𝓞 E)) :=
      hxy ▸ Ideal.mem_span_singleton_mul.2 ⟨w, hmem z hz w hw, rfl⟩
    obtain ⟨v, hv, hvw⟩ := Ideal.mem_span_singleton_mul.1 hxw
    have hvw' : (y : E) * v = x * (b * z) := by
      rw [← hw]; exact_mod_cast hvw
    refine AddSubgroup.mem_map.2 ⟨(v : E), AddSubgroup.mem_map.2 ⟨v, hv, rfl⟩, ?_⟩
    simp only [AddMonoidHom.coe_mulLeft]
    field_simp
    linear_combination hvw'
  · intro hz
    obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.1 hz
    obtain ⟨v, hv, rfl⟩ := AddSubgroup.mem_map.1 hu
    have hyv : y * v ∈ Ideal.span {x} * 𝔞 :=
      hxy.symm ▸ Ideal.mem_span_singleton_mul.2 ⟨v, hv, rfl⟩
    obtain ⟨w, hw, hwv⟩ := Ideal.mem_span_singleton_mul.1 hyv
    have hwv' : (x : E) * w = y * v := by exact_mod_cast hwv
    rw [mem_scaledIdeal] at hw
    convert hw using 1
    simp only [AddMonoidHom.coe_mulLeft, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe]
    field_simp
    linear_combination -hwv'

end GroundTheory.Heights₂.Heights.FiniteCovolume
