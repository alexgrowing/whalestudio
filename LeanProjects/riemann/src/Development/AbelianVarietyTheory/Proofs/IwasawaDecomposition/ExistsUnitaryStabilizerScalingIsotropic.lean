import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem hypRot_smul_mem (X : Data E N) {s : E} (hs : IsIntegral ℤ s) {v : Fin N → E}
    (hv : v ∈ X.Λ) : s • v ∈ X.Λ := by
  have : s • v = (⟨s, hs⟩ : 𝓞 E) • v := by
    rw [← algebraMap_smul E (⟨s, hs⟩ : 𝓞 E) v]; rfl
  rw [this]; exact X.Λ.smul_mem _ hv

theorem hypRot_mulVec (X : Data E N) (ξ η : Fin N → E) (a b : E) (x : Fin N → E) :
    (1 + a • rk1 X.Gm ξ η + b • rk1 X.Gm η ξ).mulVec x =
      x + (a * herm X.Gm x η) • ξ + (b * herm X.Gm x ξ) • η := by
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, one_add_smul_vecMulVec_mulVec, smul_smul]

theorem hypRot_mul_hypRot (X : Data E N) (ξ η : Fin N → E) (d : ℕ) (a b : E)
    (hξξ : herm X.Gm ξ ξ = 0) (hηη : herm X.Gm η η = 0) (hξη : herm X.Gm ξ η = d)
    (hηξ : herm X.Gm η ξ = d) (key : a + b + a * b * d = 0) :
    (1 + a • rk1 X.Gm ξ η + b • rk1 X.Gm η ξ) * (1 + b • rk1 X.Gm ξ η + a • rk1 X.Gm η ξ) = 1 := by
  have hPP : rk1 X.Gm ξ η * rk1 X.Gm ξ η = (d : E) • rk1 X.Gm ξ η := by rw [one_add_smul_vecMulVec_mul, hξη]
  have hPQ : rk1 X.Gm ξ η * rk1 X.Gm η ξ = 0 := by rw [one_add_smul_vecMulVec_mul, hηη, zero_smul]
  have hQP : rk1 X.Gm η ξ * rk1 X.Gm ξ η = 0 := by rw [one_add_smul_vecMulVec_mul, hξξ, zero_smul]
  have hQQ : rk1 X.Gm η ξ * rk1 X.Gm η ξ = (d : E) • rk1 X.Gm η ξ := by rw [one_add_smul_vecMulVec_mul, hηξ]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hPP, hPQ, hQP, hQQ,
    smul_zero, smul_smul]
  calc _ = 1 + (a + b + a * b * d) • rk1 X.Gm ξ η + (a + b + a * b * d) • rk1 X.Gm η ξ := by module
    _ = 1 := by rw [key, zero_smul, zero_smul, add_zero, add_zero]

theorem herm_hypRot (X : Data E N) (ξ η : Fin N → E) (d : ℕ) (a b : E)
    (hξξ : herm X.Gm ξ ξ = 0) (hηη : herm X.Gm η η = 0) (hξη : herm X.Gm ξ η = d)
    (hηξ : herm X.Gm η ξ = d) (ha : cc a = a) (hb : cc b = b) (key : a + b + a * b * d = 0)
    (x y : Fin N → E) :
    herm X.Gm (x + (a * herm X.Gm x η) • ξ + (b * herm X.Gm x ξ) • η)
      (y + (a * herm X.Gm y η) • ξ + (b * herm X.Gm y ξ) • η) = herm X.Gm x y := by
  have hc := cc_herm X.Gm X.Gm_herm
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, cc_mul, ha, hb, hc,
    hξξ, hηη, hξη, hηξ]
  linear_combination (herm X.Gm x ξ * herm X.Gm η y + herm X.Gm x η * herm X.Gm ξ y) * key

theorem exists_isUStab_hypRot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (ξ η : Fin N → E) (d : ℕ) (ε : E) (c : 𝓞 E), 0 < d → ξ ∈ X.Λ → η ∈ X.Λ → herm X.Gm ξ ξ = 0 → herm X.Gm η η = 0 → herm X.Gm ξ η = d → cc ε = ε → ε ≠ 0 → IsIntegral ℤ ε → IsIntegral ℤ ε⁻¹ → ε - 1 = d * X.den * c → ∃ g : GL (Fin N) E, IsUStab X.Gm X.Λ g ∧ (g : Matrix (Fin N) (Fin N) E).mulVec ξ = ε • ξ := by
  intro E _ _ _ N X ξ η d ε c hd hξ hη hξξ hηη hξη hεr hε0 hεi hεii hεc
  have hdE : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
  have hηξ : herm X.Gm η ξ = d := by rw [← cc_herm X.Gm X.Gm_herm ξ η, hξη, cc_natCast]
  obtain ⟨a, ha_def⟩ : ∃ a : E, a = (ε - 1) / d := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b : E, b = (ε⁻¹ - 1) / d := ⟨_, rfl⟩
  have ha : cc a = a := by
    rw [ha_def, div_eq_mul_inv, cc_mul, cc_inv, cc_sub, cc_one, cc_natCast, hεr]
  have hb : cc b = b := by
    rw [hb_def, div_eq_mul_inv, cc_mul, cc_inv, cc_sub, cc_one, cc_natCast, cc_inv, hεr]
  have key : a + b + a * b * d = 0 := by
    rw [ha_def, hb_def]; field_simp; ring
  have key' : b + a + b * a * d = 0 := by linear_combination key
  have ha' : a = (X.den : E) * c := by
    rw [ha_def, div_eq_iff hdE, hεc]; ring
  have hinv : ε⁻¹ * ε = 1 := inv_mul_cancel₀ hε0
  have hb' : b = -(ε⁻¹ * ((X.den : E) * c)) := by
    rw [hb_def, div_eq_iff hdE]; linear_combination (-ε⁻¹) * hεc + hinv
  have hA : ∀ x ∈ X.Λ, ∀ y ∈ X.Λ, IsIntegral ℤ (a * herm X.Gm x y) := by
    intro x hx y hy
    rw [ha', show (X.den : E) * c * herm X.Gm x y = c * (X.den * herm X.Gm x y) by ring]
    exact (RingOfIntegers.isIntegral_coe c).mul (X.Λ_int x hx y hy)
  have hB : ∀ x ∈ X.Λ, ∀ y ∈ X.Λ, IsIntegral ℤ (b * herm X.Gm x y) := by
    intro x hx y hy
    rw [hb', show -(ε⁻¹ * ((X.den : E) * c)) * herm X.Gm x y =
      -(ε⁻¹ * c * (X.den * herm X.Gm x y)) by ring]
    exact ((hεii.mul (RingOfIntegers.isIntegral_coe c)).mul (X.Λ_int x hx y hy)).neg
  have h01 := hypRot_mul_hypRot X ξ η d a b hξξ hηη hξη hηξ key
  have h10 := hypRot_mul_hypRot X ξ η d b a hξξ hηη hξη hηξ key'
  have hm0 : ∀ x ∈ X.Λ, (1 + a • rk1 X.Gm ξ η + b • rk1 X.Gm η ξ).mulVec x ∈ X.Λ := by
    intro x hx
    rw [hypRot_mulVec]
    exact X.Λ.add_mem (X.Λ.add_mem hx (hypRot_smul_mem X (hA x hx η hη) hξ))
      (hypRot_smul_mem X (hB x hx ξ hξ) hη)
  have hm1 : ∀ x ∈ X.Λ, (1 + b • rk1 X.Gm ξ η + a • rk1 X.Gm η ξ).mulVec x ∈ X.Λ := by
    intro x hx
    rw [hypRot_mulVec]
    exact X.Λ.add_mem (X.Λ.add_mem hx (hypRot_smul_mem X (hB x hx η hη) hξ))
      (hypRot_smul_mem X (hA x hx ξ hξ) hη)
  refine ⟨⟨_, _, h01, h10⟩, ⟨fun x y => ?_, fun x => ⟨hm0 x, fun h => ?_⟩⟩, ?_⟩
  · show herm X.Gm ((1 + a • rk1 X.Gm ξ η + b • rk1 X.Gm η ξ).mulVec x)
      ((1 + a • rk1 X.Gm ξ η + b • rk1 X.Gm η ξ).mulVec y) = herm X.Gm x y
    rw [hypRot_mulVec, hypRot_mulVec]
    exact herm_hypRot X ξ η d a b hξξ hηη hξη hηξ ha hb key x y
  · have := hm1 _ h
    rwa [Matrix.mulVec_mulVec, h10, Matrix.one_mulVec] at this
  · show (1 + a • rk1 X.Gm ξ η + b • rk1 X.Gm η ξ).mulVec ξ = ε • ξ
    rw [hypRot_mulVec, hξη, hξξ, mul_zero, zero_smul, add_zero]
    have : a * d = ε - 1 := by rw [ha_def]; field_simp
    rw [this]; module

end GlobalTheory.UnipKill
