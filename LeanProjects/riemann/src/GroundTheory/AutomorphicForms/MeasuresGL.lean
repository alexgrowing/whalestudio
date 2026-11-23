import Mathlib
import GroundTheory.AutomorphicForms.MeasuresChart
import GroundTheory.AutomorphicForms.RealGroupsHaar
import GroundTheory.AutomorphicForms.Cartan

namespace GroundTheory.Automorphic

open MeasureTheory Measure Topology Filter Set ValuativeRel DoubleCoset
open scoped NNReal ENNReal Pointwise

set_option linter.unusedSectionVars false

namespace Measures

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)

noncomputable def entries : Matrix (Fin n) (Fin n) F ≃ₗ[F] (Fin n × Fin n → F) :=
  ((LinearEquiv.curry F F (Fin n) (Fin n)).trans (Matrix.ofLinearEquiv F)).symm

@[simp] theorem entries_apply (A : Matrix (Fin n) (Fin n) F) (ij : Fin n × Fin n) :
    entries F n A ij = A ij.1 ij.2 :=
  rfl

@[simp] theorem entries_symm_apply (x : Fin n × Fin n → F) (i j : Fin n) :
    (entries F n).symm x i j = x (i, j) :=
  rfl

noncomputable def entriesHomeomorph : Matrix (Fin n) (Fin n) F ≃ₜ (Fin n × Fin n → F) where
  toEquiv := (entries F n).toEquiv
  continuous_toFun := continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1)
  continuous_invFun := continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)

theorem isOpenEmbedding_val :
    IsOpenEmbedding (Units.val : GL (Fin n) F → Matrix (Fin n) (Fin n) F) := by
  refine ⟨Units.isEmbedding_val_mk' (f := fun A => A⁻¹) ?_ fun u => (Matrix.coe_units_inv u).symm,
    ?_⟩
  · have hdet : ContinuousOn (fun A : Matrix (Fin n) (Fin n) F => (A.det)⁻¹) {x | IsUnit x} :=
      (continuous_id.matrix_det).continuousOn.inv₀ fun A hA =>
        ((Matrix.isUnit_iff_isUnit_det A).1 hA).ne_zero
    refine (hdet.smul (continuous_id.matrix_adjugate).continuousOn).congr fun A _ => ?_
    simp [Matrix.inv_def, Ring.inverse_eq_inv']
  · have : Set.range (Units.val : GL (Fin n) F → Matrix (Fin n) (Fin n) F) =
        (fun A : Matrix (Fin n) (Fin n) F => A.det) ⁻¹' {0}ᶜ := by
      ext A
      simp only [Set.mem_range, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨u, rfl⟩
        exact ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit).ne_zero
      · intro h
        exact ⟨((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 h)).unit, rfl⟩
    rw [this]
    exact isOpen_compl_singleton.preimage (continuous_id.matrix_det)

noncomputable def glChart : LinearChart F (Fin n × Fin n) (GL (Fin n) F) where
  toFun g := entries F n g
  isOpenEmbedding := (entriesHomeomorph F n).isOpenEmbedding.comp (isOpenEmbedding_val F n)
  left g := (entries F n).symm.trans ((Units.mulLeftLinearEquiv F _ g).trans (entries F n))
  right g := (entries F n).symm.trans ((Units.mulRightLinearEquiv F g).trans (entries F n))
  toFun_mul_left g x := by simp
  toFun_mul_right h x := by simp

theorem glChart_apply (g : GL (Fin n) F) (ij : Fin n × Fin n) :
    (glChart F n).toFun g ij = (g : Matrix (Fin n) (Fin n) F) ij.1 ij.2 :=
  rfl

theorem glChart_leftModulus (g : GL (Fin n) F) :
    (glChart F n).leftModulus g = distribHaarChar F (Matrix.GeneralLinearGroup.det g) ^ n := by
  rw [LinearChart.leftModulus, distribHaarChar_pi_eq, ← map_pow]
  congr 1
  ext
  rw [LinearEquiv.coe_det, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply]
  have := LinearMap.det_conj (LinearMap.mulLeft F (g : Matrix (Fin n) (Fin n) F)) (entries F n)
  rw [det_mulLeft_matrix, Fintype.card_fin] at this
  exact this

theorem glChart_rightModulus (g : GL (Fin n) F) :
    (glChart F n).rightModulus g = distribHaarChar F (Matrix.GeneralLinearGroup.det g) ^ n := by
  rw [LinearChart.rightModulus, distribHaarChar_pi_eq, ← map_pow]
  congr 1
  ext
  rw [LinearEquiv.coe_det, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply]
  have := LinearMap.det_conj (LinearMap.mulRight F (g : Matrix (Fin n) (Fin n) F)) (entries F n)
  rw [det_mulRight_matrix, Fintype.card_fin] at this
  exact this

theorem modularCharacter_GL : (modularCharacter : GL (Fin n) F →* ℝ≥0) = 1 := by
  ext g
  borelize F (GL (Fin n) F)
  rw [(glChart F n).modularCharacter_eq, glChart_leftModulus, glChart_rightModulus,
    div_self (pow_pos distribHaarChar_pos n).ne', MonoidHom.one_apply]

theorem isMulRightInvariant_GL [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have : modularCharacterFun g = 1 := by
    change modularCharacter g = 1
    rw [modularCharacter_GL, MonoidHom.one_apply]
  rw [isMulLeftInvariant_eq_smul (map (· * g) μ) μ, ← modularCharacterFun_eq_haarScalarFactor,
    this, one_smul]

section DoubleCoset

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]

theorem measure_preimage_mk_finset (μ : Measure G) [μ.IsMulLeftInvariant] {K : Subgroup G}
    (hK : IsOpen (K : Set G)) (O : Finset (G ⧸ K)) :
    μ ((QuotientGroup.mk : G → G ⧸ K) ⁻¹' (O : Set (G ⧸ K))) = O.card * μ K := by
  have hpre : ∀ a : G, (QuotientGroup.mk : G → G ⧸ K) ⁻¹' {(a : G ⧸ K)} = (a⁻¹ * ·) ⁻¹' K := by
    intro a
    ext b
    rw [Set.mem_preimage, Set.mem_singleton_iff, QuotientGroup.eq, ← K.inv_mem_iff, mul_inv_rev,
      inv_inv]
    rfl
  rw [show (QuotientGroup.mk : G → G ⧸ K) ⁻¹' (O : Set (G ⧸ K)) =
      ⋃ y ∈ O, (QuotientGroup.mk : G → G ⧸ K) ⁻¹' {y} by ext; simp, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl (g := fun _ => μ K) fun x _ => ?_, Finset.sum_const, nsmul_eq_mul]
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hpre, measure_preimage_mul]
  · intro x _ y _ hxy
    exact Set.disjoint_left.2 fun b hx hy => hxy (hx.symm.trans hy)
  · intro x _
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hpre]
    exact (hK.preimage (continuous_const_mul _)).measurableSet

theorem mem_map_conj_iff {K : Subgroup G} {g k : G} :
    k ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * k * g ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem measure_doubleCoset (μ : Measure G) [μ.IsMulLeftInvariant] {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (g : G) :
    μ (doubleCoset g (K : Set G) K) =
      ((K.map (MulAut.conj g).toMonoidHom).relIndex K : ℝ≥0∞) * μ K := by
  set H := K.map (MulAut.conj g).toMonoidHom with hH
  let O : Set (G ⧸ K) := MulAction.orbit K (g : G ⧸ K)
  have hstab : MulAction.stabilizer K (g : G ⧸ K) = H.subgroupOf K := by
    ext k
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_map_conj_iff]
    show ((k : G) • ((g : G) : G ⧸ K)) = ((g : G) : G ⧸ K) ↔ _
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul,
      show ((k : G) * g)⁻¹ * g = (g⁻¹ * k * g)⁻¹ by group, K.inv_mem_iff]
  have hdc : doubleCoset g (K : Set G) K = (QuotientGroup.mk : G → G ⧸ K) ⁻¹' O := by
    ext x
    rw [mem_doubleCoset, Set.mem_preimage, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨k₁, hk₁, k₂, hk₂, rfl⟩
      refine ⟨⟨k₁, hk₁⟩, ?_⟩
      show ((k₁ : G) • ((g : G) : G ⧸ K)) = _
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
      simpa [mul_assoc] using hk₂
    · rintro ⟨k, hk⟩
      change ((k : G) • ((g : G) : G ⧸ K)) = _ at hk
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq] at hk
      exact ⟨k, k.2, (k * g)⁻¹ * x, hk, by group⟩
  have hcK : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have hopen : IsOpen ((H.subgroupOf K : Subgroup K) : Set K) := by
    have : IsOpen (H : Set G) := by
      have e : (H : Set G) = (fun x => g⁻¹ * x * g) ⁻¹' K := by
        ext x
        exact mem_map_conj_iff
      rw [e]
      exact hKo.preimage (by fun_prop)
    exact this.preimage continuous_subtype_val
  have hfin : Finite (K ⧸ H.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hopen
  have hOfin : O.Finite := by
    have : Finite O := by
      rw [← hstab] at hfin
      exact Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer K (g : G ⧸ K)).symm
    exact Set.toFinite O
  have hcard : hOfin.toFinset.card = H.relIndex K := by
    rw [← Nat.card_eq_card_finite_toFinset, Subgroup.relIndex, Subgroup.index, ← hstab]
    exact Nat.card_congr (MulAction.orbitEquivQuotientStabilizer K (g : G ⧸ K))
  rw [hdc, ← hOfin.coe_toFinset, measure_preimage_mk_finset μ hKo, hcard]

end DoubleCoset

theorem measure_doubleCoset_diagPow [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    (μ : Measure (GL (Fin n) F)) [μ.IsMulLeftInvariant] (a : Fin n → ℤ) :
    μ (doubleCoset (Cartan.diagPow F n a) (GLnLocal.integralGL F n : Set (GL (Fin n) F))
        (GLnLocal.integralGL F n)) =
      (((GLnLocal.integralGL F n).map (MulAut.conj (Cartan.diagPow F n a)).toMonoidHom).relIndex
        (GLnLocal.integralGL F n) : ℝ≥0∞) * μ (GLnLocal.integralGL F n) :=
  measure_doubleCoset μ (GLnLocal.isOpen_integralGL F n) (GLnLocal.isCompact_integralGL F n) _

theorem inv_eq_self_GL [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] : μ.inv = μ := by
  have := isMulRightInvariant_GL F n μ
  set K := GLnLocal.integralGL F n
  have hK0 : μ K ≠ 0 := (GLnLocal.isOpen_integralGL F n).measure_ne_zero μ ⟨1, K.one_mem⟩
  have hKT : μ K ≠ ∞ := (GLnLocal.isCompact_integralGL F n).measure_lt_top.ne
  have e := isMulLeftInvariant_eq_smul μ.inv μ
  have hc : haarScalarFactor μ.inv μ = 1 := by
    have h := congrArg (fun ν : Measure (GL (Fin n) F) => ν K) e
    simp only [Measure.inv_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    have hKinv : (K : Set (GL (Fin n) F))⁻¹ = K := by
      ext x
      simp
    rw [hKinv] at h
    have := (ENNReal.mul_eq_right hK0 hKT).1 h.symm
    exact_mod_cast this
  rw [e, hc, one_smul]

theorem inv_doubleCoset {G : Type*} [Group G] (g : G) (K : Subgroup G) :
    (doubleCoset g (K : Set G) K)⁻¹ = doubleCoset g⁻¹ (K : Set G) K := by
  ext x
  rw [Set.mem_inv, mem_doubleCoset, mem_doubleCoset]
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    exact ⟨b⁻¹, K.inv_mem hb, a⁻¹, K.inv_mem ha, by rw [← inv_inv x, h]; group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨b⁻¹, K.inv_mem hb, a⁻¹, K.inv_mem ha, by group⟩

theorem relIndex_conj_eq {K : Subgroup (GL (Fin n) F)} (hKo : IsOpen (K : Set (GL (Fin n) F)))
    (hKc : IsCompact (K : Set (GL (Fin n) F))) (g : GL (Fin n) F) :
    (K.map (MulAut.conj g).toMonoidHom).relIndex K =
      (K.map (MulAut.conj g⁻¹).toMonoidHom).relIndex K := by
  borelize (GL (Fin n) F)
  let μ : Measure (GL (Fin n) F) := Measure.haar
  have hK0 : μ K ≠ 0 := hKo.measure_ne_zero μ ⟨1, K.one_mem⟩
  have hKT : μ K ≠ ∞ := hKc.measure_lt_top.ne
  have h1 := measure_doubleCoset μ hKo hKc g
  have h3 : μ (doubleCoset g (K : Set (GL (Fin n) F)) K) =
      μ (doubleCoset g⁻¹ (K : Set (GL (Fin n) F)) K) := by
    conv_lhs => rw [← inv_eq_self_GL F n μ]
    rw [Measure.inv_apply, inv_doubleCoset]
  rw [h3, measure_doubleCoset μ hKo hKc g⁻¹] at h1
  exact_mod_cast ((ENNReal.mul_left_inj hK0 hKT).1 h1).symm

variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin n) F)]
  [BorelSpace (GL (Fin n) F)]

noncomputable def haarGL (μ₀ : Measure (Fin n × Fin n → F)) : Measure (GL (Fin n) F) :=
  (glChart F n).haar μ₀

variable (μ₀ : Measure (Fin n × Fin n → F)) [μ₀.IsAddHaarMeasure]

theorem haarGL_eq :
    haarGL F n μ₀ = (μ₀.comap fun (g : GL (Fin n) F) (ij : Fin n × Fin n) =>
      (g : Matrix (Fin n) (Fin n) F) ij.1 ij.2).withDensity
        fun g => (((distribHaarChar F (Matrix.GeneralLinearGroup.det g) ^ n)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  rw [haarGL, LinearChart.haar]
  congr 1
  funext g
  rw [glChart_leftModulus]

instance isHaarMeasure_haarGL : (haarGL F n μ₀).IsHaarMeasure :=
  LinearChart.isHaarMeasure_haar _ μ₀

instance isMulRightInvariant_haarGL : (haarGL F n μ₀).IsMulRightInvariant :=
  isMulRightInvariant_GL F n _

theorem eq_smul_haarGL (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    μ = haarScalarFactor μ (haarGL F n μ₀) • haarGL F n μ₀ :=
  isMulLeftInvariant_eq_smul μ _

end Measures

end GroundTheory.Automorphic
