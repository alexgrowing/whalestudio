import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import GroundTheory.LocalFields.NormCorrespondence
import GroundTheory.GlobalFields.LocalFieldAtPlace

open UpperTheory.V.Z.Sym.Loc

namespace UpperTheory.V.Z.Sym.Glob

private def val {K : Type} [Field K] (d : K) : Subgroup Kˣ :=
  (Units.map (QuadraticAlgebra.norm : QuadraticAlgebra K d 0 →* K)).range

private theorem mem_val {K : Type} [Field K] (d : K) (u : Kˣ) :
    u ∈ val d ↔ ∃ a b : K, a ^ 2 - d * b ^ 2 = u := by
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨(w : QuadraticAlgebra K d 0).re, (w : QuadraticAlgebra K d 0).im, ?_⟩
    simp only [Units.coe_map, MonoidHom.coe_coe, QuadraticAlgebra.norm_def]
    ring
  · rintro ⟨a, b, h⟩
    have hn : QuadraticAlgebra.norm (⟨a, b⟩ : QuadraticAlgebra K d 0) = u := by
      rw [QuadraticAlgebra.norm_def]
      simp only
      linear_combination h
    have hw : IsUnit (⟨a, b⟩ : QuadraticAlgebra K d 0) :=
      QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (hn ▸ u.isUnit)
    refine ⟨hw.unit, Units.ext ?_⟩
    simp [hn]

private theorem algNorm {K : Type} [Field K] (d : K) (z : QuadraticAlgebra K d 0) :
    Algebra.norm K z = QuadraticAlgebra.norm z := by
  rw [Algebra.norm_apply, ← QuadraticAlgebra.det_toLinearMap_eq_norm]
  rfl

private theorem index_val {K : Type} [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (d : K) (hd : ¬ IsSquare d) : (val d).index = 2 := by
  classical
  haveI : IsSepClosure K (AlgebraicClosure K) :=
    IsSepClosure.of_isAlgClosure_of_perfectField K (AlgebraicClosure K)
  obtain ⟨α, hα⟩ : ∃ α : AlgebraicClosure K, α ^ 2 = algebraMap K (AlgebraicClosure K) d :=
    IsAlgClosed.exists_pow_nat_eq _ two_pos
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C d : Polynomial K) := by
    refine X_pow_sub_C_irreducible_of_prime Nat.prime_two ?_
    intro b hb
    exact hd ⟨b, by rw [← hb]; ring⟩
  have hmin : (Polynomial.X ^ 2 - Polynomial.C d : Polynomial K) = minpoly K α :=
    minpoly.eq_of_irreducible_of_monic hirr (by simp [hα])
      (Polynomial.monic_X_pow_sub_C _ two_ne_zero)
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  set L : IntermediateField K (AlgebraicClosure K) := IntermediateField.adjoin K {α} with hL
  have hrank : Module.finrank K L = 2 := by
    rw [hL, IntermediateField.adjoin.finrank hint, ← hmin, Polynomial.natDegree_X_pow_sub_C]
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ hrank
  haveI : Algebra.IsQuadraticExtension K L := ⟨hrank⟩
  haveI : IsAbelianGalois K L := IsAbelianGalois.of_isCyclic K L
  have key := GroundTheory.LocalField.index_range_normUnits_of_isAbelianGalois
    (K := K) (Ω := AlgebraicClosure K) L
  rw [hrank] at key
  rw [← key]
  congr 1
  let β : L := ⟨α, IntermediateField.mem_adjoin_simple_self K α⟩
  have hβ : β ^ 2 = algebraMap K L d := Subtype.ext (by simpa using hα)
  let φ : QuadraticAlgebra K d 0 →ₐ[K] L :=
    { toFun := fun z => algebraMap K L z.re + algebraMap K L z.im * β
      map_one' := by
        show algebraMap K L (1 : QuadraticAlgebra K d 0).re +
          algebraMap K L (1 : QuadraticAlgebra K d 0).im * β = 1
        rw [show (1 : QuadraticAlgebra K d 0).re = 1 from rfl,
          show (1 : QuadraticAlgebra K d 0).im = 0 from rfl]
        simp
      map_mul' := by
        intro z w
        simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul,
          map_zero, zero_mul, add_zero]
        linear_combination (-(algebraMap K L z.im * algebraMap K L w.im)) * hβ
      map_zero' := by simp
      map_add' := by
        intro z w
        simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add]
        ring
      commutes' := by intro r; simp }
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    have hz' : algebraMap K L z.re + algebraMap K L z.im * β = 0 := hz
    have him : z.im = 0 := by
      by_contra h
      apply hd
      have hA : algebraMap K L z.im ≠ 0 := by simpa using h
      have h1 : β = algebraMap K L (-z.re / z.im) := by
        rw [map_div₀, map_neg, eq_div_iff hA]
        linear_combination hz'
      have h2 := hβ
      rw [h1, ← map_pow] at h2
      have h3 := (algebraMap K L).injective h2
      exact ⟨-z.re / z.im, by linear_combination (-1 : K) * h3⟩
    have hre : z.re = 0 := by
      rw [him, map_zero, zero_mul, add_zero] at hz'
      simpa using hz'
    ext <;> simp [hre, him]
  have hφs : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := φ.toLinearMap)
      (by rw [QuadraticAlgebra.finrank_eq_two, hrank])).mp hφ
  let e := AlgEquiv.ofBijective φ ⟨hφ, hφs⟩
  have hnorm : ∀ z : QuadraticAlgebra K d 0, Algebra.norm K (φ z) = QuadraticAlgebra.norm z := by
    intro z
    rw [← algNorm, ← Algebra.norm_eq_of_algEquiv e z]
    rfl
  ext u
  simp only [val, GroundTheory.LocalField.normUnits, MonoidHom.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨Units.map (φ : QuadraticAlgebra K d 0 →* L) w, Units.ext ?_⟩
    rw [← hw]
    simp [hnorm]
  · rintro ⟨x, hx⟩
    refine ⟨Units.map (e.symm : L →* QuadraticAlgebra K d 0) x, Units.ext ?_⟩
    rw [← hx]
    have hx' : φ (e.symm x) = x := e.apply_symm_apply x
    simp only [Units.coe_map, MonoidHom.coe_coe]
    rw [← hnorm, hx']

private theorem hs_mul {K : Type} [Field K] [CharZero K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (d x y : K) (hd : d ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    hs d (x * y) = hs d x * hs d y := by
  classical
  by_cases hsq : IsSquare d
  · obtain ⟨r, rfl⟩ := hsq
    have hr : r ≠ 0 := by
      rintro rfl
      simp at hd
    have all : ∀ z : K, hs (r * r) z = 1 := by
      intro z
      unfold hs
      rw [if_pos]
      refine ⟨(z + 1) / 2, (z - 1) / (2 * r), ?_⟩
      field_simp
      ring
    rw [all, all, all, one_mul]
  · have hidx := index_val d hsq
    have key : ∀ (z : K) (hz : z ≠ 0),
        hs d z = if Units.mk0 z hz ∈ val d then (1 : ℂ) else -1 := by
      intro z hz
      simp only [hs, mem_val, Units.val_mk0]
    rw [key _ (mul_ne_zero hx hy), key _ hx, key _ hy]
    have hm : Units.mk0 (x * y) (mul_ne_zero hx hy) = Units.mk0 x hx * Units.mk0 y hy :=
      Units.ext rfl
    rw [hm, Subgroup.mul_mem_iff_of_index_two hidx]
    split_ifs <;> simp_all

end UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Glob.hsMul :
    UpperTheory.V.Z.Sym.Glob.HsMul := by
  intro F _ _ v d x y hd hx hy
  haveI : CharZero (Kv v) := charZero_of_injective_algebraMap (algebraMap F (Kv v)).injective
  exact hs_mul d x y hd hx hy
