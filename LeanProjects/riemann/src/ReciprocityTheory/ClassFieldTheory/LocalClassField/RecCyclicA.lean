import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPair
import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpen
import ReciprocityTheory.ClassFieldTheory.LocalClassField.CyclicBr
import ReciprocityTheory.ClassFieldTheory.LocalClassField.EqZeroOfMemBrKerOfCoprime

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.RecCyc

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

theorem qz_mem_zmultiples {n : ℕ} (hn : 0 < n) (x : QZ) (hx : n • x = 0) :
    x ∈ AddSubgroup.zmultiples (QuotientAddGroup.mk ((1 : ℚ) / n) : QZ) := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  have h1 : (QuotientAddGroup.mk (n • q) : QZ) = 0 := hx
  obtain ⟨k, hk⟩ := (QuotientAddGroup.eq_zero_iff _).1 h1
  have hk' : (k : ℚ) = n • q := hk
  refine AddSubgroup.mem_zmultiples_iff.2 ⟨k, ?_⟩
  show (QuotientAddGroup.mk (k • ((1 : ℚ) / n)) : QZ) = _
  congr 1
  rw [zsmul_eq_mul, hk', nsmul_eq_mul]
  field_simp

section general

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (M : TRep R G)

theorem exists_defect {t : G → ℚ} (χ : Additive G →+ QZ)
    (h : ∀ g, (QuotientAddGroup.mk (t g) : QZ) = χ (Additive.ofMul g)) :
    ∃ m : (Fin 2 → G) → ℤ, ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1) := by
  have : ∀ g : Fin 2 → G, ∃ k : ℤ, (k : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1) := fun g => by
    have h0 : (QuotientAddGroup.mk (t (g 0) + t (g 1) - t (g 0 * g 1)) : QZ) = 0 := by
      rw [QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add, h, h, h, ofMul_mul, map_add, sub_self]
    obtain ⟨k, hk⟩ := (QuotientAddGroup.eq_zero_iff _).1 h0
    exact ⟨k, hk⟩
  choose m hm using this
  exact ⟨m, hm⟩

theorem isLocallyConstant_defect {t : G → ℚ} (ht : IsLocallyConstant t) {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) : IsLocallyConstant m := by
  refine IsLocallyConstant.desc m (Int.cast : ℤ → ℚ) ?_ Int.cast_injective
  have : ((Int.cast : ℤ → ℚ) ∘ m) = fun g => t (g 0) + t (g 1) - t (g 0 * g 1) := funext hm
  rw [this]
  exact ((ht.comp_continuous (continuous_apply 0)).add (ht.comp_continuous (continuous_apply 1))).sub
    (ht.comp_continuous ((continuous_apply 0).mul (continuous_apply 1)))

theorem defect_cocycle {t : G → ℚ} {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) (x y w : G) :
    m ![y, w] - m ![x * y, w] + m ![x, y * w] = m ![x, y] := by
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [hm, hm, hm, hm]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_assoc]
  ring

theorem exists_defect_cocycle {t : G → ℚ} (ht : IsLocallyConstant t) {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) (a : M.V) (ha : ∀ g, M.rho g a = a) :
    ∃ z : M.coch.X 2, M.coch.d 2 z = 0 ∧ ∀ g, z.1 g = m g • a := by
  have hc : Continuous fun g => m g • a :=
    ((isLocallyConstant_defect ht hm).comp (fun k : ℤ => k • a)).continuous
  refine ⟨⟨fun g => m g • a, hc⟩, Subtype.ext (funext fun v => ?_), fun _ => rfl⟩
  show ReciprocityTheory.Gal.dn M.rho 2 (fun g => m g • a) v = 0
  rw [LowDeg.dn_two_apply, map_zsmul, ha, ← sub_smul, ← add_smul, ← sub_smul,
    defect_cocycle hm, sub_self, zero_smul]

variable [Fintype G]

theorem sum_defect_smul {m : (Fin 2 → G) → ℤ} (a : M.V) (b : M.coch.X 1)
    (hb : ∀ g, (M.coch.d 1 b).1 g = m g • a) (τ : G) :
    (∑ σ, m ![σ, τ]) • a = ∑ σ, M.rho σ (b.1 ![τ]) := by
  have h1 : ∀ σ : G, m ![σ, τ] • a = M.rho σ (b.1 ![τ]) - b.1 ![σ * τ] + b.1 ![σ] := fun σ => by
    rw [← hb]
    exact LowDeg.dn_one_apply M.rho b.1 ![σ, τ]
  have h2 : ∑ σ, b.1 ![σ * τ] = ∑ σ, b.1 ![σ] := Equiv.sum_comp (Equiv.mulRight τ) (fun σ => b.1 ![σ])
  rw [Finset.sum_smul, Finset.sum_congr rfl fun σ _ => h1 σ, Finset.sum_add_distrib, Finset.sum_sub_distrib, h2]
  abel

theorem sum_defect {t : G → ℚ} {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) (τ : G) :
    ((∑ σ, m ![σ, τ] : ℤ) : ℚ) = Fintype.card G * t τ := by
  push_cast
  rw [Finset.sum_congr rfl fun σ _ => hm ![σ, τ]]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h2 : ∑ σ, t (σ * τ) = ∑ σ, t σ := Equiv.sum_comp (Equiv.mulRight τ) t
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, h2]
  simp

theorem exists_cobound_of_norm [DiscreteTopology G] {t : G → ℚ} {m : (Fin 2 → G) → ℤ}
    (hm : ∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) (y : M.V) :
    ∃ b : M.coch.X 1, ∀ g, (M.coch.d 1 b).1 g = m g • ∑ ρ, M.rho ρ y := by
  refine ⟨⟨fun w => ∑ ρ, m ![w 0, ρ] • M.rho (w 0 * ρ) y, continuous_of_discreteTopology⟩, fun v => ?_⟩
  show ReciprocityTheory.Gal.dn M.rho 1 (fun w => ∑ ρ, m ![w 0, ρ] • M.rho (w 0 * ρ) y) v = _
  rw [LowDeg.dn_one_apply]
  simp only [Matrix.cons_val_zero]
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [← Equiv.sum_comp (Equiv.mulLeft (v 1)) (fun ρ => m ![v 0, ρ] • M.rho (v 0 * ρ) y),
    ← Equiv.sum_comp (Equiv.mulLeft (v 0 * v 1)) (fun ρ => M.rho ρ y), map_sum, Finset.smul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp only [Equiv.coe_mulLeft]
  rw [map_zsmul, ← Module.End.mul_apply, ← map_mul, ← mul_assoc, ← sub_smul, ← add_smul, defect_cocycle hm, ← hv]

end general

end ReciprocityTheory.DiscreteGroups.LocalClassField.RecCyc
