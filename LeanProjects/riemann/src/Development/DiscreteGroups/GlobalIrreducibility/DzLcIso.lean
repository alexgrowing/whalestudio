import Mathlib
import GroundTheory.AutomorphicForms.Iwasawa
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne

noncomputable section

open GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzLc

variable {g : ℕ} [Fact g.Prime] {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

theorem norm_symm_le_one (i : ℚ_[g] ≃+* k) (hi : Continuous i) {x : k}
    (hx : x ∈ (ValuativeRel.valuation k).integer) : ‖i.symm x‖ ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨y, hy⟩ : ∃ y, i.symm x = y := ⟨_, rfl⟩
  rw [hy] at hlt
  have hix : i y = x := by rw [← hy, RingEquiv.apply_symm_apply]
  have hy0 : y ≠ 0 := fun h => by rw [h, norm_zero] at hlt; exact absurd hlt (by norm_num)
  have hx0 : x ≠ 0 := by rw [← hix]; exact (map_ne_zero i).2 hy0
  have hz : ‖y⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hlt
  have hϖ1 : ValuativeRel.valuation k (GLnLocal.uniformizer k : k) < 1 := GLnLocal.valuation_uniformizer_lt_one k
  have hϖ0 : (GLnLocal.uniformizer k : k) ≠ 0 := fun h =>
    GLnLocal.valuation_uniformizer_ne_zero k (by rw [h, map_zero])
  have h1 : Filter.Tendsto (fun m : ℕ => y⁻¹ ^ m * i.symm (GLnLocal.uniformizer k : k)⁻¹) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz).mul_const (i.symm (GLnLocal.uniformizer k : k)⁻¹)
  have hT : Filter.Tendsto (fun m : ℕ => i (y⁻¹ ^ m * i.symm (GLnLocal.uniformizer k : k)⁻¹)) Filter.atTop
      (nhds 0) := by
    have := (hi.tendsto 0).comp h1
    rwa [map_zero] at this
  have hO : ((ValuativeRel.valuation k).integer : Set k) ∈ nhds (0 : k) :=
    Valuation.isOpen_integer.mem_nhds (zero_mem _)
  obtain ⟨m, hm⟩ := (hT.eventually hO).exists
  have hm' : i (y⁻¹ ^ m * i.symm (GLnLocal.uniformizer k : k)⁻¹) ∈ (ValuativeRel.valuation k).integer := hm
  have hval := (Valuation.mem_integer_iff _ _).1 hm'
  have hxv := (Valuation.mem_integer_iff _ _).1 hx
  have hiy : i (y⁻¹ ^ m * i.symm (GLnLocal.uniformizer k : k)⁻¹) * x ^ m = (GLnLocal.uniformizer k : k)⁻¹ := by
    rw [map_mul, map_pow, map_inv₀, hix, RingEquiv.apply_symm_apply, inv_pow,
      mul_comm ((x ^ m)⁻¹) _, mul_assoc, inv_mul_cancel₀ (pow_ne_zero m hx0), mul_one]
  have hle : ValuativeRel.valuation k (GLnLocal.uniformizer k : k)⁻¹ ≤ 1 := by
    rw [← hiy, map_mul, map_pow]
    exact mul_le_one' hval (pow_le_one' hxv m)
  have hge : (1 : ValuativeRel.ValueGroupWithZero k) ≤ ValuativeRel.valuation k (GLnLocal.uniformizer k : k) := by
    calc (1 : ValuativeRel.ValueGroupWithZero k)
        = ValuativeRel.valuation k ((GLnLocal.uniformizer k : k) * (GLnLocal.uniformizer k : k)⁻¹) := by
          rw [mul_inv_cancel₀ hϖ0, map_one]
      _ = ValuativeRel.valuation k (GLnLocal.uniformizer k : k) *
          ValuativeRel.valuation k (GLnLocal.uniformizer k : k)⁻¹ := map_mul _ _ _
      _ ≤ ValuativeRel.valuation k (GLnLocal.uniformizer k : k) * 1 := by gcongr
      _ = _ := mul_one _
  exact absurd hϖ1 (not_lt.2 hge)

theorem exists_inc_eq (i : ℚ_[g] ≃+* k) (hi : Continuous i) {n : ℕ} (k0 : GL (Fin n) k)
    (hk : k0 ∈ GLnLocal.integralGL k n) :
    ∃ κ : GL (Fin n) ℤ_[g], Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n κ) = k0 := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff k n).1 hk
  let M : Matrix (Fin n) (Fin n) ℤ_[g] := fun a b =>
    ⟨i.symm ((k0 : Matrix (Fin n) (Fin n) k) a b), norm_symm_le_one i hi (h1 a b)⟩
  let M' : Matrix (Fin n) (Fin n) ℤ_[g] := fun a b =>
    ⟨i.symm (((k0⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a b), norm_symm_le_one i hi (h2 a b)⟩
  let φ : ℤ_[g] →+* k := i.toRingHom.comp (algebraMap ℤ_[g] ℚ_[g])
  have hφ : Function.Injective φ := fun a b h => Subtype.ext (i.injective h)
  have hMφ : M.map φ = (k0 : Matrix (Fin n) (Fin n) k) := by
    ext a b
    exact i.apply_symm_apply _
  have hM'φ : M'.map φ = ((k0⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    ext a b
    exact i.apply_symm_apply _
  have hMM : M * M' = 1 := by
    apply Matrix.map_injective hφ
    show (M * M').map φ = (1 : Matrix (Fin n) (Fin n) ℤ_[g]).map φ
    rw [Matrix.map_mul, hMφ, hM'φ, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hM'M : M' * M = 1 := by
    apply Matrix.map_injective hφ
    show (M' * M).map φ = (1 : Matrix (Fin n) (Fin n) ℤ_[g]).map φ
    rw [Matrix.map_mul, hMφ, hM'φ, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero φ) (map_one φ)]
  refine ⟨⟨M, M', hMM, hM'M⟩, Matrix.GeneralLinearGroup.ext fun a b => ?_⟩
  exact i.apply_symm_apply _

theorem exists_lift (i : ℚ_[g] ≃+* k) {n a : ℕ} (u : GL (Fin n) (ZMod g))
    (hu : u ∈ GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a)) :
    ∃ κ : GL (Fin n) ℤ_[g], GlobalTheory.GLp.red g n κ = u ∧
      Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n κ) ∈
        GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a) := by
  classical
  have hu' := GlobalTheory.FiniteGL.mem_unipRadical.1 hu
  have hoff : ∀ x y, x ≠ y → GlobalTheory.FiniteGL.twoBlocks n a y ≤ GlobalTheory.FiniteGL.twoBlocks n a x →
      (u : Matrix (Fin n) (Fin n) (ZMod g)) x y = 0 := by
    intro x y hxy h
    have := hu' x y h
    rwa [Matrix.sub_apply, Matrix.one_apply_ne hxy, sub_zero] at this
  have hdiag : ∀ x, (u : Matrix (Fin n) (Fin n) (ZMod g)) x x = 1 := by
    intro x
    have := hu' x x le_rfl
    rwa [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at this
  let M : Matrix (Fin n) (Fin n) ℤ_[g] := fun x y =>
    if x = y then 1 else (((u : Matrix (Fin n) (Fin n) (ZMod g)) x y).val : ℤ_[g])
  have hM : (PadicInt.toZMod (p := g)).mapMatrix M = (u : Matrix (Fin n) (Fin n) (ZMod g)) := by
    ext x y
    show PadicInt.toZMod (M x y) = _
    simp only [M]
    split_ifs with h
    · subst h
      rw [map_one, hdiag]
    · rw [map_natCast, ZMod.natCast_zmod_val]
  have hd : IsUnit M.det := by
    by_contra h
    have h1 : M.det ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod]
      exact h
    rw [RingHom.mem_ker, RingHom.map_det, hM] at h1
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit u)).ne_zero h1
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).2 hd).unit, Units.ext hM, ?_⟩
  refine GlobalTheory.FiniteGL.mem_unipRadical.2 fun x y hxy => ?_
  rw [Matrix.sub_apply]
  show i.toRingHom (algebraMap ℤ_[g] ℚ_[g] (M x y)) - (1 : Matrix (Fin n) (Fin n) k) x y = 0
  by_cases h : x = y
  · subst h
    simp [M]
  · have h0 := hoff x y h hxy
    simp [M, h, h0]

end DiscreteGroups.sglob.DzLc
