import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.ReductionNonsingularPoints
import GroundTheory.ArithmeticGeometry.AbelianVarieties.SingularCubic
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeron
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

noncomputable section

open IsLocalRing GroundTheory.Arith.Abelian

section Scale

variable {R : Type*} [CommRing R]

def scaleCoeffs (W : WeierstrassCurve R) (a : R) : WeierstrassCurve R :=
  ⟨a * W.a₁, a ^ 2 * W.a₂, a ^ 3 * W.a₃, a ^ 4 * W.a₄, a ^ 6 * W.a₆⟩

theorem map_scaleCoeffs {S : Type*} [CommRing S] (f : R →+* S) (W : WeierstrassCurve R) (a : R) :
    (scaleCoeffs W a).map f = scaleCoeffs (W.map f) (f a) := by
  ext <;> simp [scaleCoeffs]

def scaleVariableChange {F : Type*} [Field F] {c : F} (hc : c ≠ 0) :
    WeierstrassCurve.VariableChange F :=
  ⟨(Units.mk0 c hc)⁻¹, 0, 0, 0⟩

theorem scaleVariableChange_smul {F : Type*} [Field F] (W : WeierstrassCurve F) {c : F}
    (hc : c ≠ 0) : scaleVariableChange hc • W = scaleCoeffs W c := by
  ext <;> simp [scaleVariableChange, scaleCoeffs, WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃,
    WeierstrassCurve.variableChange_a₄, WeierstrassCurve.variableChange_a₆]

end Scale

section Torsion

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  [(W.map (algebraMap 𝒪 K)).IsElliptic] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]

local notation "ι" => algebraMap 𝒪 K
local notation "ρ" => residue 𝒪

theorem nsmul_ne_zero_of_notMem_range {n : ℕ} (hn : (n : ResidueField 𝒪) ≠ 0) {X Y : K}
    (h : (curveK K W).Nonsingular X Y) (hX : X ∉ Set.range ι) :
    n • WeierstrassCurve.Affine.Point.some _ _ h ≠ 0 := by
  intro hnP
  have hι := IsFractionRing.injective 𝒪 K
  obtain ⟨z, w, v, hzm, hz0, -, -, hwv, hvu, hρv, hXz, hYw⟩ :=
    exists_zw_of_notMem_range K W h.1 hX
  have hzK : ι z ≠ 0 := (map_ne_zero_iff _ hι).2 hz0
  set W' := scaleCoeffs W z with hW'
  have hC : scaleVariableChange hzK • W.map ι = W'.map ι := by
    rw [scaleVariableChange_smul, hW', map_scaleCoeffs]
  have : (W'.map ι).IsElliptic := hC ▸ inferInstance
  set v' : 𝒪 := ↑hvu.unit⁻¹ with hv'
  have hvv : v * v' = 1 := hvu.mul_val_inv
  have hvK : ι v * ι v' = 1 := by rw [← map_mul, hvv, map_one]
  have hwK : ι w = ι z ^ 3 * ι v := by rw [hwv, map_mul, map_pow]
  have hvK0 : ι v ≠ 0 := left_ne_zero_of_mul_eq_one hvK
  have hv'K : ι v' = (ι v)⁻¹ := eq_inv_of_mul_eq_one_right hvK
  have hx' : vcX (scaleVariableChange hzK) X = ι v' := by
    simp only [vcX, scaleVariableChange, inv_inv, Units.val_mk0, sub_zero]
    rw [← hXz, hwK, hv'K]
    field_simp
  have hy' : vcY (scaleVariableChange hzK) X Y = ι (-v') := by
    simp only [vcY, scaleVariableChange, inv_inv, Units.val_mk0, sub_zero, zero_mul]
    rw [← hYw, hwK, map_neg, hv'K]
    field_simp
  have h' : (curveK K W').Nonsingular (ι v') (ι (-v')) := by
    have := (nonsingular_vc (scaleVariableChange hzK) (W.map ι) X Y).2 h
    rw [hC, hx', hy'] at this
    exact this
  set φ := vcPointEquiv (scaleVariableChange hzK) hC
  have hφ : φ (.some _ _ h) = .some _ _ h' := by
    rw [vcPointEquiv_apply, vcPoint_some, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hx', hy'⟩

  have hρz : ρ z = 0 := residue_eq_zero_of_mem hzm
  have h1 : (W'.map ρ).a₁ = -2 * 0 := by simp [hW', scaleCoeffs, hρz]
  have h2 : (W'.map ρ).a₂ = -0 ^ 2 := by simp [hW', scaleCoeffs, hρz]
  have h3 : (W'.map ρ).a₃ = 0 := by simp [hW', scaleCoeffs, hρz]
  have h4 : (W'.map ρ).a₄ = 0 := by simp [hW', scaleCoeffs, hρz]
  have h6 : (W'.map ρ).a₆ = 0 := by simp [hW', scaleCoeffs, hρz]
  have hρv' : ρ v' = 1 := by
    have := congrArg ρ hvv
    rwa [map_mul, hρv, one_mul, map_one] at this
  have n' : (curveRed W').Nonsingular (ρ v') (ρ (-v')) :=
    origin_nonsingular (W'.map ρ) h3 h4 h6 (equation_residue W' (equation_of_map K W' h'.1))
      (by rw [hρv']; exact one_ne_zero)
  have hE0 : φ (.some _ _ h) ∈ E0Subgroup K W' := by
    rw [hφ]; exact mem_E0Set_some_integral K W' h' n'
  set Q : E0Subgroup K W' := ⟨_, hE0⟩
  have hnQ : n • Q = 0 := by
    apply Subtype.ext
    rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]
    change n • φ _ = 0
    rw [← map_nsmul, hnP, map_zero]
  have hred : reduceE0Hom K W' Q = .some _ _ n' := by
    rw [reduceE0Hom_apply]
    change reducePoint K W' (φ _) = _
    rw [hφ, reducePoint_some_integral K W' h' n']
  have key : n • cuspHom (W'.map ρ) h3 h4 h6 0 h1 h2 (reduceE0Hom K W' Q) = 0 := by
    rw [← map_nsmul, ← map_nsmul, hnQ, map_zero, map_zero]
  rw [hred] at key
  change n • (ρ v' / (ρ (-v') - 0 * ρ v')) = 0 at key
  rw [map_neg, hρv'] at key
  apply hn
  simpa using key

end Torsion

section Good

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  [W.IsElliptic] [DecidableEq K] [DecidableEq (ResidueField 𝒪)]

theorem eq_zero_of_nsmul_eq_zero_of_reducePoint_eq_zero {n : ℕ}
    (hn : (n : ResidueField 𝒪) ≠ 0) {P : (curveK K W).Point} (hnP : n • P = 0)
    (hP : reducePoint K W P = 0) : P = 0 := by
  rcases point_cases K W P with rfl | ⟨X, Y, h, rfl, hX⟩ | ⟨x, y, h, rfl⟩
  · rfl
  · exact absurd hnP (nsmul_ne_zero_of_notMem_range K W hn h hX)
  · rw [reducePoint_some_integral K W h (nonsingular_residue_of_isElliptic K W h.1)] at hP
    exact absurd hP (WeierstrassCurve.Affine.Point.some_ne_zero _)

theorem eq_of_reductionHom_eq_of_nsmul {n : ℕ} (hn : (n : ResidueField 𝒪) ≠ 0)
    {P Q : (curveK K W).Point} (hP : n • P = 0) (hQ : n • Q = 0)
    (h : reductionHom K W P = reductionHom K W Q) : P = Q :=
  sub_eq_zero.1 (eq_zero_of_nsmul_eq_zero_of_reducePoint_eq_zero K W hn
    (by rw [nsmul_sub, hP, hQ, sub_zero])
    (by rw [← reductionHom_apply, map_sub, h, sub_self]))

theorem reductionHom_torsionBy_injective {n : ℕ} (hn : (n : ResidueField 𝒪) ≠ 0) :
    Function.Injective
      ((reductionHom K W).comp (AddSubgroup.torsionBy (curveK K W).Point n).subtype) :=
  fun P Q h => Subtype.ext (eq_of_reductionHom_eq_of_nsmul K W hn
    (AddSubgroup.torsionBy.nsmul_iff.mp P.2) (AddSubgroup.torsionBy.nsmul_iff.mp Q.2) h)

def reductionTorsionHom (n : ℕ) :
    AddSubgroup.torsionBy (curveK K W).Point n →+ AddSubgroup.torsionBy (curveRed W).Point n :=
  ((reductionHom K W).comp (AddSubgroup.torsionBy (curveK K W).Point n).subtype).codRestrict _
    fun P => by
      rw [AddSubgroup.torsionBy.nsmul_iff, AddMonoidHom.comp_apply, ← map_nsmul,
        AddSubgroup.subtype_apply, AddSubgroup.torsionBy.nsmul_iff.mp P.2, map_zero]

theorem coe_reductionTorsionHom_apply (n : ℕ) (P : AddSubgroup.torsionBy (curveK K W).Point n) :
    (reductionTorsionHom K W n P : (curveRed W).Point) = reductionHom K W P :=
  rfl

theorem reductionTorsionHom_injective {n : ℕ} (hn : (n : ResidueField 𝒪) ≠ 0) :
    Function.Injective (reductionTorsionHom K W n) := fun _ _ h =>
  reductionHom_torsionBy_injective K W hn (congrArg Subtype.val h)

end Good

section Localization

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F] [Algebra R F]
  [IsFractionRing R F] (v : HeightOneSpectrum R)

instance isDiscreteValuationRing_valuationSubringAtPrime :
    IsDiscreteValuationRing (v.valuationSubringAtPrime F) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot _

theorem residue_algebraMap_ne_zero {a : R} (ha : a ∉ v.asIdeal) :
    residue (v.valuationSubringAtPrime F) (algebraMap R (v.valuationSubringAtPrime F) a) ≠ 0 := by
  rw [ne_eq, residue_eq_zero_iff, IsLocalization.AtPrime.to_map_mem_maximal_iff _ v.asIdeal]
  exact ha

theorem residue_natCast_ne_zero {n : ℕ} (hn : (n : R) ∉ v.asIdeal) :
    (n : ResidueField (v.valuationSubringAtPrime F)) ≠ 0 := by
  have := residue_algebraMap_ne_zero v (F := F) hn
  rwa [map_natCast, map_natCast] at this

theorem isElliptic_map_valuationSubringAtPrime (W : WeierstrassCurve R) (hΔ : W.Δ ∉ v.asIdeal) :
    (W.map (algebraMap R (v.valuationSubringAtPrime F))).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, WeierstrassCurve.map_Δ]
  by_contra hu
  apply residue_algebraMap_ne_zero v (F := F) hΔ
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
  exact hu

end Localization

section NumberField

open NumberField IsDedekindDomain

variable {F : Type*} [Field F] [NumberField F] (𝔮 : HeightOneSpectrum (𝓞 F))
  (W : WeierstrassCurve (𝔮.valuationSubringAtPrime F)) [W.IsElliptic] [DecidableEq F]
  [DecidableEq (ResidueField (𝔮.valuationSubringAtPrime F))]

theorem reductionHom_torsionBy_injective_of_notMem {n : ℕ} (hn : (n : 𝓞 F) ∉ 𝔮.asIdeal) :
    Function.Injective
      ((reductionHom F W).comp (AddSubgroup.torsionBy (curveK F W).Point n).subtype) :=
  reductionHom_torsionBy_injective F W (residue_natCast_ne_zero 𝔮 hn)

theorem eq_of_reductionHom_eq_of_nsmul_of_notMem {n : ℕ} (hn : (n : 𝓞 F) ∉ 𝔮.asIdeal)
    {P Q : (curveK F W).Point} (hP : n • P = 0) (hQ : n • Q = 0)
    (h : reductionHom F W P = reductionHom F W Q) : P = Q :=
  eq_of_reductionHom_eq_of_nsmul F W (residue_natCast_ne_zero 𝔮 hn) hP hQ h

end NumberField

end

end GroundTheory.Global
