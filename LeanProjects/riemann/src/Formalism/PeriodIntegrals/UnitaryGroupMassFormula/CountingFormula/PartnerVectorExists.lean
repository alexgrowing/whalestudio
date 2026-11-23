import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.UnimodOneGenus

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem hT_sub_sum_left {r : ℕ} (x w : S.V) (c : Fin r → E) (y : Fin r → S.V) :
    S.hT (x - ∑ d, c d • y d) w = S.hT x w - ∑ d, star (c d) * S.hT (y d) w := by
  first
  | simp [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
  | simp [map_sub, map_sum, LinearMap.sub_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]

theorem hT_sub_sum_right {r : ℕ} (x w : S.V) (c : Fin r → E) (y : Fin r → S.V) :
    S.hT w (x - ∑ d, c d • y d) = S.hT w x - ∑ d, c d * S.hT w (y d) := by
  simp [map_sub, map_sum, map_smul, smul_eq_mul]

theorem coord_surj {r : ℕ} {T : E} (F0 : FlagG S r T) :
    Function.Surjective (LinearMap.pi (fun a => S.hT (F0.e a)) : S.V →ₗ[E] (Fin r → E)) := by
  classical
  by_contra hns
  have hlt : LinearMap.range (LinearMap.pi (fun a => S.hT (F0.e a)) : S.V →ₗ[E] (Fin r → E)) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    exact hns (LinearMap.range_eq_top.mp h)
  obtain ⟨ψ, hψne, hψ⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  have key : ∀ x : S.V, ∑ a, ψ (Pi.single a 1) * S.hT (F0.e a) x = 0 := by
    intro x
    have hx := hψ (LinearMap.mem_range_self (LinearMap.pi (fun a => S.hT (F0.e a)) : S.V →ₗ[E] (Fin r → E)) x)
    rw [LinearMap.mem_ker] at hx
    have hdec : (LinearMap.pi (fun a => S.hT (F0.e a)) : S.V →ₗ[E] (Fin r → E)) x
        = ∑ a, S.hT (F0.e a) x • (Pi.single a 1 : Fin r → E) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hdec, map_sum] at hx
    simpa [map_smul, smul_eq_mul, mul_comm] using hx
  have hv : (∑ a, star (ψ (Pi.single a 1)) • F0.e a) = 0 := by
    apply S.nondeg.1
    intro x
    first
    | simpa [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, smul_eq_mul, starRingEnd_apply, star_star] using key x
    | simpa [map_sum, LinearMap.map_smulₛₗ, smul_eq_mul, starRingEnd_apply, star_star] using key x
  have hc : ∀ a, ψ (Pi.single a 1) = 0 := by
    intro a
    have h0 := (Fintype.linearIndependent_iff.mp F0.e_indep) _ hv a
    simpa using h0
  apply hψne
  apply LinearMap.pi_ext
  intro i x
  have hs : (Pi.single i x : Fin r → E) = x • (Pi.single i 1 : Fin r → E) := by
    ext j
    by_cases h : j = i <;> simp [Pi.single_apply, h]
  rw [hs, map_smul, hc i]
  simp

private theorem star_hT_eq_hT_swap (x y : S.V) : star (S.hT x y) = S.hT y x := by
  have h : starRingEnd E (S.hT x y) = S.hT y x := by
    first
    | exact S.herm.eq x y
    | exact S.herm x y
  simpa [starRingEnd_apply] using h

theorem partner_exists {r : ℕ} {T : E} (F0 : FlagG S r T) (hT0 : T ≠ 0) :
    ∃ f : Fin r → S.V, (∀ a b, S.hT (F0.e a) (f b) = if a = b then 1 else 0) ∧
      (∀ a b, S.hT (f a) (f b) = 0) ∧ ∀ a, S.hT (f a) F0.z = 0 := by
  classical
  have hE : ∀ b, ∃ g0 : S.V, ∀ a, S.hT (F0.e a) g0 = if a = b then 1 else 0 := by
    intro b
    obtain ⟨g0, hg0⟩ := coord_surj S F0 (fun a => if a = b then (1 : E) else 0)
    refine ⟨g0, fun a => ?_⟩
    have h1 := congrFun hg0 a
    simpa using h1
  choose g0 hg0 using hE
  have hZ : S.hT F0.z F0.z ≠ 0 := by
    rw [F0.z_norm]
    exact neg_ne_zero.mpr hT0
  set g : Fin r → S.V := fun b => g0 b - (S.hT F0.z (g0 b) / S.hT F0.z F0.z) • F0.z with hgdef
  have hgE : ∀ a b, S.hT (F0.e a) (g b) = if a = b then 1 else 0 := by
    intro a b
    simp [g, map_sub, map_smul, smul_eq_mul, F0.z_orth, hg0]
  have hgZ : ∀ b, S.hT F0.z (g b) = 0 := by
    intro b
    simp only [g, map_sub, map_smul, smul_eq_mul]
    rw [div_mul_cancel₀ _ hZ, sub_self]
  have hZg : ∀ b, S.hT (g b) F0.z = 0 := by
    intro b
    rw [← star_hT_eq_hT_swap, hgZ, star_zero]
  have hgeE : ∀ a d, S.hT (g a) (F0.e d) = if d = a then 1 else 0 := by
    intro a d
    rw [← star_hT_eq_hT_swap, hgE]
    split_ifs <;> simp
  set c : Fin r → Fin r → E := fun b d => S.hT (g d) (g b) / 2 with hcdef
  have hf1 : ∀ a b, S.hT (F0.e a) (g b - ∑ d, c b d • F0.e d) = if a = b then 1 else 0 := by
    intro a b
    rw [hT_sub_sum_right]
    simp [hgE, F0.e_iso]
  refine ⟨fun b => g b - ∑ d, c b d • F0.e d, hf1, ?_, ?_⟩
  · intro a b
    rw [hT_sub_sum_left]
    simp only [hf1]
    rw [hT_sub_sum_right]
    simp only [hgeE, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hs : star (c a b) = S.hT (g a) (g b) / 2 := by
      simp only [c]
      rw [← star_hT_eq_hT_swap (S := S) (g a) (g b)]
      first
      | simp [star_div₀]
      | simp [star_div']
      | simp
    rw [hs]
    simp only [c]
    ring
  · intro a
    rw [hT_sub_sum_left]
    simp [hZg, F0.z_orth]

end Gen

theorem partner_vector_exists : PartnerEx := by
  intro D u F0
  refine partner_exists (VS D) F0 ?_
  unfold Tn
  exact_mod_cast (D.mem u).A.T_prime.ne_zero

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
