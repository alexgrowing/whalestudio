import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandA

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt

open Finset

variable {R : Type*} [Field R] {G : Type*} [Group G] [Fintype G] [MulSemiringAction G R]

def act (g : G) : Rˣ →* Rˣ := Units.map (MulSemiringAction.toRingHom G R g : R →* R)

theorem act_val (g : G) (u : Rˣ) : ((act g u : Rˣ) : R) = g • (u : R) := rfl

variable (G) in

def normU : Rˣ →* Rˣ := ∏ g : G, act g

theorem normU_val (u : Rˣ) : ((normU G u : Rˣ) : R) = ∏ g : G, g • (u : R) := by
  simp [normU, Units.coe_prod, act_val]

theorem smul_prod_univ (g : G) (x : R) : g • ∏ g' : G, g' • x = ∏ g' : G, g' • x := by
  rw [← MulSemiringAction.toRingHom_apply, map_prod]
  simp only [MulSemiringAction.toRingHom_apply, smul_smul]
  exact Fintype.prod_equiv (Equiv.mulLeft g) _ _ fun _ => rfl

theorem prod_smul_smul (g : G) (x : R) : ∏ g' : G, g' • g • x = ∏ g' : G, g' • x := by
  simp only [smul_smul]
  exact Fintype.prod_equiv (Equiv.mulRight g) _ _ fun _ => rfl

theorem sum_pow_eq {g₀ : G} (hg : ∀ g, g ∈ Subgroup.zpowers g₀) (f : G → R) :
    ∑ k ∈ range (orderOf g₀), f (g₀ ^ k) = ∑ g, f g := by
  classical
  rw [← IsCyclic.image_range_orderOf hg, sum_image]
  intro a ha b hb hab
  exact pow_injOn_Iio_orderOf (by simpa using ha) (by simpa using hb) hab

theorem telescope (g₀ : G) (z : R) (k : ℕ) :
    g₀ • ∑ j ∈ range k, g₀ ^ j • z - ∑ j ∈ range k, g₀ ^ j • z = g₀ ^ k • z - z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, smul_add, smul_smul, ← pow_succ']
    linear_combination ih

namespace Filt

variable {I : ℕ → AddSubgroup R} {e : R →+ R} (h : Filt G I e)

include h

theorem act_mem {n : ℕ} (g : G) {u : Rˣ} (hu : u ∈ h.V n) : act g u ∈ h.V n := by
  rw [mem_V, act_val]
  have := h.smul n g _ hu
  rwa [smul_sub, smul_one] at this

theorem normU_mem {n : ℕ} {u : Rˣ} (hu : u ∈ h.V n) : normU G u ∈ h.V n := by
  rw [normU, MonoidHom.finsetProd_apply]
  exact (h.V n).prod_mem fun g _ => h.act_mem g hu

theorem norm_surj (u : Rˣ) (hu : (u : R) - 1 ∈ I 0) (hfix : ∀ g : G, g • (u : R) = u) :
    ∃ v : Rˣ, (v : R) - 1 ∈ I 0 ∧ ∏ g : G, g • (v : R) = u := by
  let Z : Subgroup Rˣ :=
    { carrier := {u | ∀ g : G, act g u = u}
      one_mem' := fun g => map_one _
      mul_mem' := fun {a b} ha hb g => by rw [map_mul, ha g, hb g]
      inv_mem' := fun {a} ha g => by rw [map_inv, ha g] }
  have step : ∀ n, ∀ u ∈ h.V n, u ∈ Z → ∃ v ∈ h.V n, u / normU G v ∈ h.V (n + 1) := by
    intro n u hu hZ
    have hx : ∀ g : G, g • ((u : R) - 1) = (u : R) - 1 := fun g => by
      rw [smul_sub, smul_one, ← act_val, hZ g]
    have hy : e ((u : R) - 1) ∈ I n := h.e_mem n _ hu
    have htr : ∑ g : G, g • e ((u : R) - 1) = (u : R) - 1 := by
      conv_rhs => rw [← h.e_sum ((u : R) - 1)]
      exact Finset.sum_congr rfl fun g _ => by rw [hx]
    refine ⟨h.mkU _ (h.le_zero n hy), h.mkU_mem _ hy, h.div_mem_V (h.normU_mem (h.mkU_mem _ (h.le_zero n hy))) ?_⟩
    have hp := h.prod_one_add (n := n) univ (fun g : G => g • e ((u : R) - 1)) (fun g _ => h.smul n g _ hy)
    rw [htr] at hp
    rw [normU_val, mkU_val]
    simp only [smul_add, smul_one]
    have := (I (n + 1)).neg_mem hp
    convert this using 1
    ring
  obtain ⟨v, hv, hvu⟩ := exists_of_approx h.V h.V_comp h.V_sep Z (normU G)
    (fun n u hu => h.normU_mem hu)
    (fun u g => Units.ext (by rw [act_val, normU_val, smul_prod_univ])) step u hu
    (fun g => Units.ext (hfix g))
  exact ⟨v, hv, by rw [← normU_val, hvu]⟩

theorem hilbert90_matrix_subalgebra_norm_one (g₀ : G) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) (u : Rˣ) (hu : (u : R) - 1 ∈ I 0)
    (hN : ∏ g : G, g • (u : R) = 1) :
    ∃ v : Rˣ, (v : R) - 1 ∈ I 0 ∧ g₀ • (v : R) = u * v := by
  have step : ∀ n, ∀ u ∈ h.V n, u ∈ (normU G).ker →
      ∃ v ∈ h.V n, u / (act g₀ / MonoidHom.id _ : Rˣ →* Rˣ) v ∈ h.V (n + 1) := by
    intro n u hu hZ
    set x : R := (u : R) - 1 with hxdef
    have hx : x ∈ I n := hu
    have hux : (u : R) = 1 + x := by rw [hxdef]; ring
    have htr : ∑ g : G, g • x ∈ I (n + 1) := by
      have hp := h.prod_one_add (n := n) univ (fun g : G => g • x) (fun g _ => h.smul n g _ hx)
      have h1 : ∏ g : G, (1 + g • x) = 1 := by
        have := congrArg Units.val (MonoidHom.mem_ker.1 hZ)
        rw [normU_val, hux] at this
        simpa only [smul_add, smul_one, Units.val_one] using this
      rw [h1, sub_self, zero_sub] at hp
      simpa using (I (n + 1)).neg_mem hp
    set y : R := ∑ k ∈ range (orderOf g₀), ∑ j ∈ range k, g₀ ^ j • e ((g₀ ^ k)⁻¹ • x) with hydef
    have hy : y ∈ I n := (I n).sum_mem fun k _ => (I n).sum_mem fun j _ =>
      h.smul n _ _ (h.e_mem n _ (h.smul n _ _ hx))
    have hd : g₀ • y - y = x - e (∑ g : G, g • x) := by
      rw [hydef, smul_sum, ← sum_sub_distrib]
      simp only [telescope]
      rw [sum_sub_distrib, sum_pow_eq hg (fun g => g • e (g⁻¹ • x)), h.e_sum, ← map_sum,
        sum_pow_eq hg (fun g => g⁻¹ • x)]
      congr 2
      exact Fintype.sum_equiv (Equiv.inv G) _ _ fun _ => rfl
    have hy0 := h.le_zero n hy
    have hvV : h.mkU y hy0 ∈ h.V n := h.mkU_mem y hy
    refine ⟨h.mkU y hy0, hvV, h.div_mem_V
      ((h.V 0).div_mem (h.act_mem g₀ (h.V_le_zero n hvV)) (h.V_le_zero n hvV)) ?_⟩
    set z : R := (1 + y)⁻¹ - 1 with hzdef
    have hz : z ∈ I n := h.inv n y hy
    have hyz : (1 + y) * (1 + z) = 1 := by
      rw [hzdef, add_sub_cancel, mul_inv_cancel₀ (h.one_add_ne_zero hy0)]
    have hval : (((act g₀ / MonoidHom.id _ : Rˣ →* Rˣ) (h.mkU y hy0) : Rˣ) : R) = (1 + g₀ • y) * (1 + z) := by
      rw [MonoidHom.div_apply, MonoidHom.id_apply, div_eq_mul_inv, Units.val_mul, act_val,
        Units.val_inv_eq_inv_val, mkU_val, smul_add, smul_one, hzdef, add_sub_cancel]
    rw [hval, hux]
    have : 1 + x - (1 + g₀ • y) * (1 + z) = e (∑ g : G, g • x) - (g₀ • y - y) * z := by
      linear_combination -hyz - hd
    rw [this]
    exact (I (n + 1)).sub_mem (h.e_mem _ _ htr)
      (h.mul n _ _ ((I n).sub_mem (h.smul n _ _ hy) hy) (h.le_zero n hz))
  obtain ⟨v, hv, hvu⟩ := exists_of_approx h.V h.V_comp h.V_sep (normU G).ker (act g₀ / MonoidHom.id _)
    (fun n u hu => (h.V n).div_mem (h.act_mem g₀ hu) hu)
    (fun u => by
      rw [MonoidHom.mem_ker, MonoidHom.div_apply, MonoidHom.id_apply, map_div, div_eq_one]
      exact Units.ext (by rw [normU_val, normU_val, act_val, prod_smul_smul])) step u hu
    (Units.ext (by rw [normU_val, hN]; rfl))
  refine ⟨v, hv, ?_⟩
  rw [MonoidHom.div_apply, MonoidHom.id_apply, div_eq_iff_eq_mul] at hvu
  rw [← act_val, hvu, Units.val_mul]

end Filt

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
