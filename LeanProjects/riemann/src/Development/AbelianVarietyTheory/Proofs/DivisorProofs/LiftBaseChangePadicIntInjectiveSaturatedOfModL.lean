import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatticeModL

theorem exists_one_tmul_add_smul (l : ℕ) [Fact l.Prime] (H : Type) [AddCommGroup H]
    (x : ℤ_[l] ⊗[ℤ] H) :
    ∃ (h : H) (y : ℤ_[l] ⊗[ℤ] H), x = (1 : ℤ_[l]) ⊗ₜ h + (l : ℤ_[l]) • y := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a h =>
    obtain ⟨c, hc⟩ : ∃ c : ℤ_[l], a - (a.zmodRepr : ℤ_[l]) = (l : ℤ_[l]) * c := by
      have := PadicInt.sub_zmodRepr_mem a
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
      exact this
    refine ⟨(a.zmodRepr : ℤ) • h, c ⊗ₜ h, ?_⟩
    have ha : a = ((a.zmodRepr : ℤ) : ℤ_[l]) + (l : ℤ_[l]) * c := by
      rw [← hc]; push_cast; ring
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      smul_eq_mul, zsmul_eq_mul, _root_.mul_one, ← TensorProduct.add_tmul, ← ha]
  | add x y hx hy =>
    obtain ⟨h₁, y₁, rfl⟩ := hx
    obtain ⟨h₂, y₂, rfl⟩ := hy
    exact ⟨h₁ + h₂, y₁ + y₂, by rw [TensorProduct.tmul_add, smul_add]; abel⟩

end GlobalTheory.LatticeModL

open GlobalTheory.LatticeModL in

theorem GlobalTheory.latticeMap_liftBaseChange_injective_saturated :
    ∀ (l : ℕ) [Fact l.Prime] (H T : Type) [AddCommGroup H] [Module.Finite ℤ H] [Module.Free ℤ H]
      [AddCommGroup T] [Module ℤ_[l] T], (∀ t : T, (l : ℤ_[l]) • t = 0 → t = 0) →
      ∀ φ : H →+ T, (∀ (h : H) (t : T), φ h = (l : ℤ_[l]) • t → ∃ h' : H, h = l • h') →
      Function.Injective (φ.toIntLinearMap.liftBaseChange ℤ_[l]) ∧
      ∀ t : T, (l : ℤ_[l]) • t ∈ LinearMap.range (φ.toIntLinearMap.liftBaseChange ℤ_[l]) →
        t ∈ LinearMap.range (φ.toIntLinearMap.liftBaseChange ℤ_[l]) := by
  intro l _ H T _ _ _ _ _ htor φ hsat
  set F := φ.toIntLinearMap.liftBaseChange ℤ_[l] with hFdef
  have hF : ∀ h, F ((1 : ℤ_[l]) ⊗ₜ h) = φ h := by
    intro h; simp [F]
  have key : ∀ (x : ℤ_[l] ⊗[ℤ] H) (t : T), F x = (l : ℤ_[l]) • t →
      ∃ x', x = (l : ℤ_[l]) • x' := by
    intro x t hx
    obtain ⟨h, y, rfl⟩ := exists_one_tmul_add_smul l H x
    rw [map_add, map_smul, hF] at hx
    have h1 : φ h = (l : ℤ_[l]) • (t - F y) := by rw [smul_sub, ← hx]; abel
    obtain ⟨h', rfl⟩ := hsat h _ h1
    refine ⟨(1 : ℤ_[l]) ⊗ₜ h' + y, ?_⟩
    rw [smul_add, TensorProduct.tmul_smul]
    simp only [Nat.cast_smul_eq_nsmul]
  have hl : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal ℤ_[l]) _
      (IsNoetherian.noetherian _) ?_ (IsLocalRing.maximalIdeal_le_jacobson _)
    intro x hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨x', rfl⟩ := key x 0 (by rw [hx, smul_zero])
    have : F x' = 0 := htor _ (by rw [← map_smul, hx])
    exact Submodule.smul_mem_smul hl this
  · rintro t ⟨x, hx⟩
    obtain ⟨x', rfl⟩ := key x t hx
    refine ⟨x', ?_⟩
    have : (l : ℤ_[l]) • (F x' - t) = 0 := by rw [smul_sub, ← map_smul, hx, sub_self]
    exact sub_eq_zero.mp (htor _ this)
