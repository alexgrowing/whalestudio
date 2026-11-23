import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimes
import GroundTheory.GlobalFields.ComplexMultiplication.DegreeOneAutomorphismPoints
import GroundTheory.GlobalFields.ComplexMultiplication.DegreeOneAutomorphismLift
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremPointHom
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheoremReduction
import GroundTheory.GlobalFields.ComplexMultiplication.TorsionReduction
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global
namespace Elliptic

noncomputable section

open NumberField Module IsDedekindDomain IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
  GroundTheory.Arith.Abelian
open scoped nonZeroDivisors

section Congr

variable {F : Type*} [Field F] [DecidableEq F]

theorem vcPoint_pointCongr {V₁ V₂ : WeierstrassCurve F} (e : V₁ = V₂) (C : VariableChange F)
    (h₁ : C • V₁ = V₁) (h₂ : C • V₂ = V₂) (X : V₁.toAffine.Point) :
    vcPoint C h₂ (pointCongr e X) = pointCongr e (vcPoint C h₁ X) := by
  subst e
  rfl

theorem pointCongr_symm_pointCongr {V₁ V₂ : WeierstrassCurve F} (e : V₁ = V₂)
    (X : V₁.toAffine.Point) : pointCongr e.symm (pointCongr e X) = X := by
  subst e
  rfl

theorem vcPoint_nsmul {V₁ V₂ : WeierstrassCurve F} (C : VariableChange F) (h : C • V₁ = V₂)
    (n : ℕ) (X : V₁.toAffine.Point) : n • vcPoint C h X = vcPoint C h (n • X) := by
  rw [← vcPointEquiv_apply, ← vcPointEquiv_apply, map_nsmul]

omit [DecidableEq F] in
theorem vcPoint_eq_zero_of_eq_zero {V₁ V₂ : WeierstrassCurve F} (C : VariableChange F)
    (h : C • V₁ = V₂) {X : V₁.toAffine.Point} (hX : X = 0) : vcPoint C h X = 0 := by
  subst hX
  rfl

omit [DecidableEq F] in
theorem vcPoint_congr_change {V₁ V₂ : WeierstrassCurve F} {C C' : VariableChange F} (e : C = C')
    (h : C • V₁ = V₂) (h' : C' • V₁ = V₂) (X : V₁.toAffine.Point) :
    vcPoint C h X = vcPoint C' h' X := by
  subst e
  rfl

end Congr

section Scaling

universe u

variable {k : Type u} [Field k] [DecidableEq k] [PerfectField k] (Ω : Type u) [Field Ω]
  [Algebra k Ω] [IsAlgClosed Ω] [DecidableEq Ω]

def scaleChange {R : Type*} [CommRing R] (u : Rˣ) : VariableChange R := ⟨u⁻¹, 0, 0, 0⟩

omit [DecidableEq k] [PerfectField k] in
theorem scaleChange_smul {T : WeierstrassCurve k} (hT : IsShortForm T) (u : kˣ)
    (h4 : T.a₄ = (u : k) ^ 4 * T.a₄) (h6 : T.a₆ = (u : k) ^ 6 * T.a₆) :
    scaleChange u • T = T := by
  ext
  · simp [scaleChange, variableChange_a₁, hT.a₁_eq]
  · simp [scaleChange, variableChange_a₂, hT.a₂_eq, hT.a₁_eq]
  · simp [scaleChange, variableChange_a₃, hT.a₃_eq]
  · simp only [scaleChange, variableChange_a₄, hT.a₁_eq, hT.a₂_eq, hT.a₃_eq, inv_inv]
    linear_combination -h4
  · simp only [scaleChange, variableChange_a₆, hT.a₁_eq, hT.a₂_eq, hT.a₃_eq, inv_inv]
    linear_combination -h6

theorem exists_pointHomOver_eq_vcPoint {T : WeierstrassCurve k} [T.IsElliptic] (hT : IsShortForm T)
    (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (ψ : Isogeny T T) (hψ : ψ.degree = 1) :
    ∃ (u : kˣ) (hu : scaleChange u • T = T), (u : k) ^ 12 = 1 ∧ T.a₄ = (u : k) ^ 4 * T.a₄ ∧
      T.a₆ = (u : k) ^ 6 * T.a₆ ∧ ∀ P, pointHomOver Ω ψ P = vcPoint (scaleChange u) hu P := by
  obtain ⟨u, h4, h6, hP⟩ :=
    pointMap_isogBaseChange_some_of_degree_eq_one (Ω := Ω) h2 h3 hT hT ψ hψ
  have h12 := (pow_eq_one_of_scale hT h4 h6).2
  refine ⟨u, scaleChange_smul hT u h4 h6, h12, h4, h6, fun P ↦ ?_⟩
  apply constMap_injective T Ω
  rw [constMap_pointHomOver]
  rcases P with _ | ⟨x, y, h⟩
  · rw [show (Point.zero : T.toAffine.Point) = 0 from rfl, map_zero, ← Isogeny.pointHom_apply,
      map_zero, vcPoint_zero, map_zero]
  · obtain ⟨h', e⟩ := hP (algebraMap k Ω x) (algebraMap k Ω y)
      ((T.toAffine.baseChange_nonsingular (f := Algebra.ofId k Ω) (algebraMap k Ω).injective x y).2 h)
    refine e.trans ?_
    show _ = Point.some _ _ _
    simp only [vcX, vcY, scaleChange, Point.some.injEq]
    simp

end Scaling

section Main

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (hK : finrank ℚ K = 2)
  [IsTotallyComplex K] {L : IntermediateField K ℂ} [NumberField L]

omit [NumberField K] [IsTotallyComplex K] in

theorem isPrimitiveRoot_localizationAt (𝔓 : HeightOneSpectrum (𝓞 L)) {ζ : L}
    (hζ : IsPrimitiveRoot ζ 12) :
    IsPrimitiveRoot (algebraMap (𝓞 L) (localizationAt L 𝔓) hζ.toInteger) 12 :=
  hζ.toInteger_isPrimitiveRoot.map_of_injective (fun a b h ↦ by
    have := congrArg (algebraMap (localizationAt L 𝔓) L) h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    exact RingOfIntegers.ext this)

set_option maxHeartbeats 1000000 in
include hK in

theorem exists_vcPoint_pointHomOver_eq (𝔭 : HeightOneSpectrum (𝓞 K))
    (hv : (Ideal.absNorm 𝔭.asIdeal).Prime) (h5 : 5 ≤ Ideal.absNorm 𝔭.asIdeal)
    (𝔓 : HeightOneSpectrum (𝓞 L)) [𝔓.asIdeal.LiesOver 𝔭.asIdeal]
    {τ : L ≃ₐ[K] L} (hτ : IsArithFrobAt (𝓞 K) τ 𝔓.asIdeal)
    {A : WeierstrassCurve L} [A.IsElliptic]
    (hEA : Nonempty (isogEnd (A.baseChange ℂ) ≃+* 𝓞 K))
    (hEA' : Nonempty (isogEnd ((A.map (τ : L →+* L)).baseChange ℂ) ≃+* 𝓞 K))
    (φ : Isogeny A (A.map (τ : L →+* L)))
    (hφ : (homConstSet (A.baseChange ℂ) ((A.map (τ : L →+* L)).baseChange ℂ) : Set ℂ) =
      (algebraMap L ℂ (invConst φ) * ·) ''
        idealLattice (algebraMap K ℂ) (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K)⁻¹)
    {W : WeierstrassCurve (localizationAt L 𝔓)} [W.IsElliptic]
    (hW : W.map (algebraMap (localizationAt L 𝔓) L) = A) [W.IsShortNF]
    (ha₄ : W.a₄ = 0 ∨ IsUnit W.a₄) (ha₆ : W.a₆ = 0 ∨ IsUnit W.a₆)
    {ζ₁₂ : L} (hζ : IsPrimitiveRoot ζ₁₂ 12) {m : ℕ} (hm : (m : 𝓞 K) ∉ 𝔭.asIdeal) :
    ∃ (D : VariableChange L) (hD : D • A.map (τ : L →+* L) = A.map (τ : L →+* L)),
      ∀ t : A.toAffine.Point, m • t = 0 →
        pointHomOver ℂ φ t = vcPoint D hD (pointMapRing (τ : L →+* L) A t) := by
  classical
  subst hW
  obtain ⟨p, hpdef⟩ : ∃ p, p = Ideal.absNorm 𝔭.asIdeal := ⟨_, rfl⟩
  have hv₀ := hv
  rw [← hpdef] at hv h5
  have : Fact p.Prime := ⟨hv⟩
  have : CharP (ResidueField (localizationAt L 𝔓)) p := by
    refine charP_residueField_localizationAt 𝔓 hv ?_
    have := algebraMap_mem_of_liesOver (𝔓 := 𝔓) (Ideal.absNorm_mem 𝔭.asIdeal)
    rwa [map_natCast, ← hpdef] at this
  have h23 : (2 : ResidueField (localizationAt L 𝔓)) ≠ 0 ∧ (3 : ResidueField (localizationAt L 𝔓)) ≠ 0 := by
    refine two_ne_zero_and_three_ne_zero_of_five_le_ringChar ?_
    rw [ringChar.eq (ResidueField (localizationAt L 𝔓)) p]
    exact h5
  have hW' : (W.map (localizationAtRingHom 𝔓 hτ)).map (algebraMap (localizationAt L 𝔓) L) =
      (W.map (algebraMap (localizationAt L 𝔓) L)).map (τ : L →+* L) := by
    rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map, comp_algebraMap_localizationAtRingHom]
  have hres : ∀ x, IsLocalRing.residue _ ((localizationAtRingHom 𝔓 hτ) x) = IsLocalRing.residue (localizationAt L 𝔓) x ^ p :=
    fun x ↦ by rw [hpdef]; exact residue_localizationAtRingHom_of_absNorm 𝔓 hτ 𝔭 x
  have htw : (W.map (IsLocalRing.residue (localizationAt L 𝔓))).map
      (frobenius (ResidueField (localizationAt L 𝔓)) p) = (W.map (localizationAtRingHom 𝔓 hτ)).map (IsLocalRing.residue _) :=
    map_residue_eq_frobeniusTwist W p hres
  obtain ⟨-, -, ⟨ψ, hred, hψdeg, -, -⟩, -⟩ :=
    reduceIsogeny_congr_eq_comp_frobeniusIsogeny hK 𝔭 hv₀ 𝔓 hEA hEA' φ hφ rfl hW' p

  have htw' : (W.map (localizationAtRingHom 𝔓 hτ)).map (IsLocalRing.residue (localizationAt L 𝔓)) =
      frobeniusTwist (W.map (IsLocalRing.residue (localizationAt L 𝔓))) p := htw.symm
  have hT : IsShortForm (frobeniusTwist (W.map (IsLocalRing.residue (localizationAt L 𝔓))) p) :=
    ⟨by simp [frobeniusTwist], by simp [frobeniusTwist], by simp [frobeniusTwist]⟩
  have hψ'deg : (ψ.congr rfl htw').degree = 1 := by rw [Isogeny.degree_congr]; exact hψdeg
  obtain ⟨u, hu, hu12, hu4, hu6, hψ'P⟩ :=
    exists_pointHomOver_eq_vcPoint (AlgebraicClosure (ResidueField (localizationAt L 𝔓))) hT
      h23.1 h23.2 (ψ.congr rfl htw') hψ'deg

  have hζ𝒪 := isPrimitiveRoot_localizationAt 𝔓 hζ
  have h12 : ((12 : ℕ) : ResidueField (localizationAt L 𝔓)) ≠ 0 := by
    rw [show ((12 : ℕ) : ResidueField (localizationAt L 𝔓)) = 2 * 2 * 3 by norm_num]
    exact mul_ne_zero (mul_ne_zero h23.1 h23.1) h23.2
  obtain ⟨η, ⟨hη12, hηu⟩, -⟩ :=
    existsUnique_pow_eq_one_of_isPrimitiveRoot (IsLocalRing.residue _) hζ𝒪 h12 hu12
  have hηunit : IsUnit η := IsUnit.of_pow_eq_one hη12 (by norm_num)
  have injRoot : ∀ {a b : localizationAt L 𝔓}, a ^ 12 = 1 → b ^ 12 = 1 →
      IsLocalRing.residue _ a = IsLocalRing.residue _ b → a = b :=
    fun ha hb h ↦ eq_of_map_eq_of_pow_eq_one (IsLocalRing.residue _) hζ𝒪 h12 ha hb h
  have hres_ne : ∀ {a : localizationAt L 𝔓}, IsUnit a → IsLocalRing.residue _ a ≠ 0 := fun ha ↦ by
    rw [Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      not_not]
    exact ha
  have hW'1 : (W.map (localizationAtRingHom 𝔓 hτ)).a₁ = 0 := by simp
  have hW'2 : (W.map (localizationAtRingHom 𝔓 hτ)).a₂ = 0 := by simp
  have hW'3 : (W.map (localizationAtRingHom 𝔓 hτ)).a₃ = 0 := by simp
  have hpow : ∀ {n : ℕ}, n ∣ 12 → (u : ResidueField (localizationAt L 𝔓)) ^ n = 1 → η ^ n = 1 := by
    intro n _ hun
    refine injRoot (by rw [← pow_mul, mul_comm, pow_mul, hη12, one_pow]) (one_pow _) ?_
    rw [map_pow, hηu, hun, map_one]
  have key4 : η ^ 4 * (W.map (localizationAtRingHom 𝔓 hτ)).a₄ = (W.map (localizationAtRingHom 𝔓 hτ)).a₄ := by
    rcases ha₄ with h0 | hunit
    · simp [h0]
    · have hne : (frobeniusTwist (W.map (IsLocalRing.residue (localizationAt L 𝔓))) p).a₄ ≠ 0 := by
        simp only [frobeniusTwist, WeierstrassCurve.map_a₄, frobenius_def]
        exact pow_ne_zero _ (hres_ne hunit)
      have hu4' : (u : ResidueField (localizationAt L 𝔓)) ^ 4 = 1 :=
        mul_right_cancel₀ hne (by rw [one_mul]; exact hu4.symm)
      rw [hpow (by norm_num) hu4', one_mul]
  have key6 : η ^ 6 * (W.map (localizationAtRingHom 𝔓 hτ)).a₆ = (W.map (localizationAtRingHom 𝔓 hτ)).a₆ := by
    rcases ha₆ with h0 | hunit
    · simp [h0]
    · have hne : (frobeniusTwist (W.map (IsLocalRing.residue (localizationAt L 𝔓))) p).a₆ ≠ 0 := by
        simp only [frobeniusTwist, WeierstrassCurve.map_a₆, frobenius_def]
        exact pow_ne_zero _ (hres_ne hunit)
      have hu6' : (u : ResidueField (localizationAt L 𝔓)) ^ 6 = 1 :=
        mul_right_cancel₀ hne (by rw [one_mul]; exact hu6.symm)
      rw [hpow (by norm_num) hu6', one_mul]
  have hηc : ((hηunit.unit : (localizationAt L 𝔓)ˣ) : localizationAt L 𝔓) = η := hηunit.unit_spec
  have hC : scaleChange hηunit.unit • (W.map (localizationAtRingHom 𝔓 hτ)) = (W.map (localizationAtRingHom 𝔓 hτ)) := by
    refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
    · simp [scaleChange, variableChange_a₁]
    · simp [scaleChange, variableChange_a₂]
    · simp [scaleChange, variableChange_a₃]
    · simp only [scaleChange, variableChange_a₄, hW'1, hW'2, hW'3, inv_inv, hηc]
      linear_combination key4
    · simp only [scaleChange, variableChange_a₆, hW'1, hW'2, hW'3, inv_inv, hηc]
      linear_combination key6
  have hD' : ((scaleChange hηunit.unit).map (algebraMap (localizationAt L 𝔓) L)) • (W.map (localizationAtRingHom 𝔓 hτ)).map (algebraMap (localizationAt L 𝔓) L) =
      (W.map (localizationAtRingHom 𝔓 hτ)).map (algebraMap (localizationAt L 𝔓) L) := by
    rw [map_variableChange, hC]
  have hD : ((scaleChange hηunit.unit).map (algebraMap (localizationAt L 𝔓) L)) • (W.map (algebraMap (localizationAt L 𝔓) L)).map (τ : L →+* L) =
      (W.map (algebraMap (localizationAt L 𝔓) L)).map (τ : L →+* L) := by
    rw [← hW']
    exact hD'
  refine ⟨((scaleChange hηunit.unit).map (algebraMap (localizationAt L 𝔓) L)), hD, fun t ht ↦ ?_⟩

  have hm' : (m : ResidueField (localizationAt L 𝔓)) ≠ 0 := by
    rw [← map_natCast (IsLocalRing.residue (localizationAt L 𝔓)), Ne, IsLocalRing.residue_eq_zero_iff,
      ← map_natCast (algebraMap (𝓞 L) (localizationAt L 𝔓)), algebraMap_mem_maximalIdeal_localizationAt_iff]
    intro h
    apply hm
    rw [Ideal.LiesOver.over (P := 𝔓.asIdeal) (p := 𝔭.asIdeal), Ideal.mem_comap, map_natCast]
    exact h
  have e0 : pointHomOver ℂ (φ.congr rfl hW'.symm) t = pointCongr hW'.symm (pointHomOver ℂ φ t) :=
    pointHomOver_congr ℂ φ rfl hW'.symm t
  have hX : m • (pointCongr (map_curveK_eq L L (comp_algebraMap_localizationAtRingHom 𝔓 hτ) W) (pointMapRing (τ : L →+* L) (W.map (algebraMap (localizationAt L 𝔓) L)) t)) = 0 := by rw [← map_nsmul, ← map_nsmul, ht, map_zero, map_zero]
  have hφ0 : m • pointHomOver ℂ (φ.congr rfl hW'.symm) t = 0 := by rw [← map_nsmul, ht, map_zero]
  have hvX : m • vcPoint ((scaleChange hηunit.unit).map (algebraMap (localizationAt L 𝔓) L)) hD' (pointCongr (map_curveK_eq L L (comp_algebraMap_localizationAtRingHom 𝔓 hτ) W) (pointMapRing (τ : L →+* L) (W.map (algebraMap (localizationAt L 𝔓) L)) t)) = 0 := by
    rw [vcPoint_nsmul]
    exact vcPoint_eq_zero_of_eq_zero _ _ hX

  have r1 : reducePoint L (W.map (localizationAtRingHom 𝔓 hτ)) (pointHomOver ℂ (φ.congr rfl hW'.symm) t) =
      pointCongr htw (vcPoint (scaleChange u) hu (pointMapRing (frobenius (ResidueField (localizationAt L 𝔓)) p) (W.map (IsLocalRing.residue (localizationAt L 𝔓))) (reducePoint L W t))) := by
    have hred' : reduceIsogeny L W (W.map (localizationAtRingHom 𝔓 hτ)) (φ.congr rfl hW'.symm) =
        ψ.comp (frobeniusIsogeny (W.map (IsLocalRing.residue (localizationAt L 𝔓))) p) := hred
    refine (reducePoint_pointHomOver L ℂ (AlgebraicClosure (ResidueField (localizationAt L 𝔓)))
      (φ.congr rfl hW'.symm) t).trans ?_
    rw [hred', pointHomOver_comp, pointHomOver_frobeniusIsogeny]
    have h1 := pointHomOver_congr (AlgebraicClosure (ResidueField (localizationAt L 𝔓))) ψ rfl htw' (pointMapRing (frobenius (ResidueField (localizationAt L 𝔓)) p) (W.map (IsLocalRing.residue (localizationAt L 𝔓))) (reducePoint L W t))
    rw [hψ'P] at h1
    rw [← pointCongr_symm_pointCongr htw'
      (pointHomOver (AlgebraicClosure (ResidueField (localizationAt L 𝔓))) ψ (pointMapRing (frobenius (ResidueField (localizationAt L 𝔓)) p) (W.map (IsLocalRing.residue (localizationAt L 𝔓))) (reducePoint L W t))), ← h1]
    rfl
  have hCres : (scaleChange hηunit.unit).map (IsLocalRing.residue (localizationAt L 𝔓)) =
      scaleChange u := by
    have hu' : Units.map (IsLocalRing.residue (localizationAt L 𝔓) : _ →* _) hηunit.unit = u :=
      Units.ext (by rw [Units.coe_map, hηc]; exact hηu)
    simp only [scaleChange, VariableChange.map, map_zero, map_inv, hu']
  have r2 : reducePoint L (W.map (localizationAtRingHom 𝔓 hτ)) (vcPoint ((scaleChange hηunit.unit).map (algebraMap (localizationAt L 𝔓) L)) hD' (pointCongr (map_curveK_eq L L (comp_algebraMap_localizationAtRingHom 𝔓 hτ) W) (pointMapRing (τ : L →+* L) (W.map (algebraMap (localizationAt L 𝔓) L)) t))) = pointCongr htw (vcPoint (scaleChange u) hu (pointMapRing (frobenius (ResidueField (localizationAt L 𝔓)) p) (W.map (IsLocalRing.residue (localizationAt L 𝔓))) (reducePoint L W t))) := by
    rw [reducePoint_vcPoint L (W.map (localizationAtRingHom 𝔓 hτ)) (scaleChange hηunit.unit) hC (pointCongr (map_curveK_eq L L (comp_algebraMap_localizationAtRingHom 𝔓 hτ) W) (pointMapRing (τ : L →+* L) (W.map (algebraMap (localizationAt L 𝔓) L)) t)),
      reducePoint_pointMapRing_localizationAtRingHom 𝔓 hτ 𝔭 p hpdef.symm W t]
    exact (vcPoint_congr_change hCres _ _ _).trans
      (vcPoint_pointCongr htw (scaleChange u) hu (by rw [← htw]; exact hu) _)
  have heq := eq_of_reductionHom_eq_of_nsmul L (W.map (localizationAtRingHom 𝔓 hτ)) hm' hφ0 hvX
    (by rw [reductionHom_apply, reductionHom_apply, r1, r2])

  have e1 : pointHomOver ℂ φ t = pointCongr hW' (pointHomOver ℂ (φ.congr rfl hW'.symm) t) := by
    rw [e0, pointCongr_symm_pointCongr]
  rw [e1, heq]
  refine (vcPoint_pointCongr hW' _ hD' hD _).symm.trans ?_
  congr 1

end Main

end

end Elliptic
end GroundTheory.Global
