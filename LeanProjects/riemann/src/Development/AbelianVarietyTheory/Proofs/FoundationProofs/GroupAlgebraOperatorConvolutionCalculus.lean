import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial

noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

section
variable {G : Type} [Group G] [Fintype G]

theorem convCalc_assoc (a b c : G → ℂ) : conv (conv a b) c = conv a (conv b c) := by
  funext x
  simp only [conv, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft z)]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [mul_assoc]

theorem convCalc_sub_left (a b c : G → ℂ) : conv (a - b) c = conv a c - conv b c := by
  funext x
  simp [conv, sub_mul, Finset.sum_sub_distrib]

theorem convCalc_sub_right (a b c : G → ℂ) : conv c (a - b) = conv c a - conv c b := by
  funext x
  simp [conv, mul_sub, Finset.sum_sub_distrib]

theorem convCalc_dirac_left (a : G → ℂ) : conv dirac a = a := by
  funext x
  simp [conv, dirac]

theorem convCalc_dirac_right (a : G → ℂ) : conv a dirac = a := by
  funext x
  simp [conv, dirac, inv_mul_eq_one]

theorem convCalc_star (a b : G → ℂ) (ha : ∀ x, a x⁻¹ = (starRingEnd ℂ) (a x))
    (hb : ∀ x, b x⁻¹ = (starRingEnd ℂ) (b x)) (x : G) :
    conv a b x⁻¹ = (starRingEnd ℂ) (conv b a x) := by
  simp only [conv, map_sum, map_mul, ← ha, ← hb]
  rw [← Equiv.sum_comp (Equiv.mulLeft x⁻¹)]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [mul_comm, mul_assoc]

theorem convCalc_isProj_conv (a b : G → ℂ) (ha : IsProj a) (hb : IsProj b) (h : conv a b = conv b a) :
    IsProj (conv a b) := by
  refine ⟨?_, fun x => ?_⟩
  · rw [convCalc_assoc, ← convCalc_assoc b a b, ← h, convCalc_assoc a b b, hb.1, ← convCalc_assoc, ha.1]
  · rw [convCalc_star a b ha.2 hb.2, h]

theorem convCalc_isProj_compl (a : G → ℂ) (ha : IsProj a) : IsProj (dirac - a) := by
  refine ⟨?_, fun x => ?_⟩
  · rw [convCalc_sub_left, convCalc_sub_right, convCalc_sub_right, convCalc_dirac_left, convCalc_dirac_left,
      convCalc_dirac_right, ha.1]
    simp
  · simp only [Pi.sub_apply, map_sub, ha.2, dirac, inv_eq_one]
    split_ifs <;> simp

variable {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)

theorem convCalc_op_conv (a b : G → ℂ) : op ρ (conv a b) = op ρ a * op ρ b := by
  simp only [op, conv, Finset.sum_smul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft y)]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp [smul_smul, mul_comm]

theorem convCalc_op_sub (a b : G → ℂ) : op ρ (a - b) = op ρ a - op ρ b := by
  simp [op, sub_smul, Finset.sum_sub_distrib]

theorem convCalc_op_add (a b : G → ℂ) : op ρ (a + b) = op ρ a + op ρ b := by
  simp [op, add_smul, Finset.sum_add_distrib]

theorem convCalc_op_dirac : op ρ dirac = 1 := by
  simp [op, dirac]

theorem convCalc_rk [FiniteDimensional ℂ M] (e : G → ℂ) (he : conv e e = e) :
    (rk ρ e : ℂ) = ∑ γ, e γ * LinearMap.trace ℂ M (ρ γ) := by
  have h1 : op ρ e * op ρ e = op ρ e := by rw [← convCalc_op_conv, he]
  have hp : LinearMap.IsProj (LinearMap.range (op ρ e)) (op ρ e) :=
    ⟨fun x => LinearMap.mem_range_self _ x, by
      rintro x ⟨y, rfl⟩
      exact LinearMap.congr_fun h1 y⟩
  rw [rk, ← hp.trace]
  simp [op, map_sum]

end

theorem convCalc : ∀ (G : Type) [Group G] [Fintype G] (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ G M), (∀ a b : G → ℂ, op ρ (conv a b) = op ρ a * op ρ b ∧ op ρ (a - b) = op ρ a - op ρ b ∧ op ρ (a + b) = op ρ a + op ρ b) ∧ op ρ dirac = 1 ∧ (∀ a b c : G → ℂ, conv (conv a b) c = conv a (conv b c) ∧ conv (a - b) c = conv a c - conv b c ∧ conv c (a - b) = conv c a - conv c b) ∧ (∀ a : G → ℂ, conv dirac a = a ∧ conv a dirac = a) ∧ (∀ a b : G → ℂ, IsProj a → IsProj b → conv a b = conv b a → IsProj (conv a b)) ∧ (∀ a : G → ℂ, IsProj a → IsProj (dirac - a)) ∧ ∀ e : G → ℂ, conv e e = e → (rk ρ e : ℂ) = ∑ γ, e γ * LinearMap.trace ℂ M (ρ γ) := by
  intro G _ _ M _ _ _ ρ
  exact ⟨fun a b => ⟨convCalc_op_conv ρ a b, convCalc_op_sub ρ a b, convCalc_op_add ρ a b⟩, convCalc_op_dirac ρ,
    fun a b c => ⟨convCalc_assoc a b c, convCalc_sub_left a b c, convCalc_sub_right a b c⟩,
    fun a => ⟨convCalc_dirac_left a, convCalc_dirac_right a⟩, convCalc_isProj_conv, convCalc_isProj_compl,
    convCalc_rk ρ⟩

end GlobalTheory.BadShare
