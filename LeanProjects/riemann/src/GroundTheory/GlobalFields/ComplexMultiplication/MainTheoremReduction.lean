import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.ReductionEval
import GroundTheory.GlobalFields.ComplexMultiplication.FrobeniusAtPrimes
import GroundTheory.ArithmeticGeometry.AbelianVarieties.KodairaNeron
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

noncomputable section

open IsLocalRing WeierstrassCurve GroundTheory.Arith.Abelian

section VariableChange

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  (C : VariableChange 𝒪) [W.IsElliptic] [DecidableEq K]

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] [W.IsElliptic] [DecidableEq K] in

theorem vcX_notMem_range {X : K} (hX : X ∉ Set.range (algebraMap 𝒪 K)) :
    vcX (C.map (algebraMap 𝒪 K)) X ∉ Set.range (algebraMap 𝒪 K) := by
  rintro ⟨a, ha⟩
  apply hX
  refine ⟨vcX' C a, ?_⟩
  rw [map_vcX', ha]
  exact vcX'_vcX _ X

theorem reducePoint_vcEquivK (P : (curveK K W).Point) :
    reducePoint K (C • W) (vcEquivK K W C P) =
      vcPoint (C.map (residue 𝒪)) (map_vc_eq_residue W C) (reducePoint K W P) := by
  rcases point_cases K W P with rfl | ⟨X, Y, h, rfl, hX⟩ | ⟨x, y, h, rfl⟩
  · rw [vcEquivK_zero, reducePoint_zero, reducePoint_zero]
    rfl
  · rw [vcEquivK_some K W C h (nonsingular_K_vc K W C h),
      reducePoint_some_notMem K (C • W) _ (vcX_notMem_range K C hX), reducePoint_some_notMem K W h hX]
    rfl
  · have n₁ := nonsingular_residue_of_isElliptic K W h.1
    have hx : vcX (C.map (algebraMap 𝒪 K)) (algebraMap 𝒪 K x) = algebraMap 𝒪 K (vcX C x) :=
      (map_vcX C (algebraMap 𝒪 K) x).symm
    have hy : vcY (C.map (algebraMap 𝒪 K)) (algebraMap 𝒪 K x) (algebraMap 𝒪 K y) =
        algebraMap 𝒪 K (vcY C x y) :=
      (map_vcY C (algebraMap 𝒪 K) x y).symm
    have h₂ : (curveK K (C • W)).Nonsingular (algebraMap 𝒪 K (vcX C x))
        (algebraMap 𝒪 K (vcY C x y)) := by
      have := nonsingular_K_vc K W C h
      rwa [hx, hy] at this
    have n₂ := nonsingular_residue_of_isElliptic K (C • W) h₂.1
    have e : vcEquivK K W C (.some _ _ h) = .some _ _ h₂ := by
      rw [vcEquivK_some K W C h (nonsingular_K_vc K W C h), Affine.Point.some.injEq]
      exact ⟨hx, hy⟩
    rw [e, reducePoint_some_integral K (C • W) h₂ n₂, reducePoint_some_integral K W h n₁, vcPoint_some,
      Affine.Point.some.injEq]
    exact ⟨map_vcX C (residue 𝒪) x, map_vcY C (residue 𝒪) x y⟩

theorem reducePoint_vcPoint {W' : WeierstrassCurve 𝒪} (hC : C • W = W') (P : (curveK K W).Point) :
    reducePoint K W' (vcPoint (C.map (algebraMap 𝒪 K)) (by rw [map_vc_eq, hC]) P) =
      vcPoint (C.map (residue 𝒪)) (by rw [map_vc_eq_residue, hC]) (reducePoint K W P) := by
  subst hC
  exact reducePoint_vcEquivK K W C P

end VariableChange

section Frobenius

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField 𝒪) p] {g : 𝒪 →+* 𝒪}

variable [IsLocalHom g]

theorem residueField_map_eq_frobenius (hg : ∀ x, residue 𝒪 (g x) = residue 𝒪 x ^ p) :
    ResidueField.map g = frobenius (ResidueField 𝒪) p := by
  ext y
  obtain ⟨x, rfl⟩ := residue_surjective y
  rw [ResidueField.map_residue, hg, frobenius_def]

theorem map_residue_eq_frobeniusTwist (hg : ∀ x, residue 𝒪 (g x) = residue 𝒪 x ^ p) :
    (W.map (residue 𝒪)).map (frobenius (ResidueField 𝒪) p) = (W.map g).map (residue 𝒪) := by
  rw [← residueField_map_eq_frobenius p hg]
  exact map_curveRed_eq W

variable [W.IsElliptic] [DecidableEq K] [DecidableEq (ResidueField 𝒪)] {G : K →+* K}
  (hG : G.comp (algebraMap 𝒪 K) = (algebraMap 𝒪 K).comp g)

include hG in

theorem reducePoint_pointMapRing_frobenius (hg : ∀ x, residue 𝒪 (g x) = residue 𝒪 x ^ p)
    (P : (curveK K W).Point) :
    reducePoint K (W.map g) (pointCongr (map_curveK_eq K K hG W)
        (pointMapRing G (W.map (algebraMap 𝒪 K)) P)) =
      pointCongr (map_residue_eq_frobeniusTwist W p hg)
        (pointMapRing (frobenius (ResidueField 𝒪) p) (W.map (residue 𝒪)) (reducePoint K W P)) := by
  rw [reducePoint_pointMapRing K K hG W P,
    pointMapRing_congr (residueField_map_eq_frobenius p hg), pointCongr_pointCongr]

end Frobenius

section NumberField

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
  (𝔓 : HeightOneSpectrum (𝓞 L)) {τ : L ≃ₐ[K] L} (hτ : IsArithFrobAt (𝓞 K) τ 𝔓.asIdeal)

include hτ in
theorem mem_localizationAt_of_isArithFrobAt {x : L} (hx : x ∈ localizationAt L 𝔓) :
    τ x ∈ localizationAt L 𝔓 :=
  (Elliptic.residue_apply_of_isArithFrobAt 𝔓 hτ hx).1

def localizationAtRingHom : localizationAt L 𝔓 →+* localizationAt L 𝔓 :=
  ((τ : L →+* L).comp (localizationAt L 𝔓).val.toRingHom).codRestrict (localizationAt L 𝔓).toSubsemiring
    fun x ↦ mem_localizationAt_of_isArithFrobAt 𝔓 hτ x.2

theorem comp_algebraMap_localizationAtRingHom :
    (τ : L →+* L).comp (algebraMap (localizationAt L 𝔓) L) =
      (algebraMap (localizationAt L 𝔓) L).comp (localizationAtRingHom 𝔓 hτ) :=
  rfl

theorem residue_localizationAtRingHom (x : localizationAt L 𝔓) :
    residue (localizationAt L 𝔓) (localizationAtRingHom 𝔓 hτ x) =
      residue (localizationAt L 𝔓) x ^ Nat.card (𝓞 K ⧸ 𝔓.asIdeal.under (𝓞 K)) := by
  obtain ⟨h, e⟩ := Elliptic.residue_apply_of_isArithFrobAt 𝔓 hτ x.2
  exact e

theorem residue_localizationAtRingHom_of_absNorm [NumberField K] (𝔭 : HeightOneSpectrum (𝓞 K))
    [𝔓.asIdeal.LiesOver 𝔭.asIdeal] (x : localizationAt L 𝔓) :
    residue (localizationAt L 𝔓) (localizationAtRingHom 𝔓 hτ x) =
      residue (localizationAt L 𝔓) x ^ Ideal.absNorm 𝔭.asIdeal := by
  rw [residue_localizationAtRingHom]
  congr 1
  rw [← Ideal.LiesOver.over (P := 𝔓.asIdeal) (p := 𝔭.asIdeal), Ideal.absNorm_apply,
    Submodule.cardQuot_apply]

instance : IsLocalHom (localizationAtRingHom 𝔓 hτ) := by
  refine ⟨fun x hx ↦ ?_⟩
  rw [← residue_ne_zero_iff_isUnit] at hx ⊢
  rw [residue_localizationAtRingHom] at hx
  exact fun h ↦ hx (by rw [h, zero_pow hτ.card_pos.ne'])

theorem reducePoint_pointMapRing_localizationAtRingHom [NumberField K] (𝔭 : HeightOneSpectrum (𝓞 K))
    [𝔓.asIdeal.LiesOver 𝔭.asIdeal] (p : ℕ) [Fact p.Prime] (hp : Ideal.absNorm 𝔭.asIdeal = p)
    [CharP (ResidueField (localizationAt L 𝔓)) p] (W : WeierstrassCurve (localizationAt L 𝔓))
    [W.IsElliptic] [DecidableEq L] [DecidableEq (ResidueField (localizationAt L 𝔓))]
    (P : (curveK L W).Point) :
    reducePoint L (W.map (localizationAtRingHom 𝔓 hτ))
        (pointCongr (map_curveK_eq L L (comp_algebraMap_localizationAtRingHom 𝔓 hτ) W)
          (pointMapRing (τ : L →+* L) (W.map (algebraMap (localizationAt L 𝔓) L)) P)) =
      pointCongr (map_residue_eq_frobeniusTwist W p
          (fun x ↦ by rw [residue_localizationAtRingHom_of_absNorm 𝔓 hτ 𝔭 x, hp]))
        (pointMapRing (frobenius (ResidueField (localizationAt L 𝔓)) p)
          (W.map (residue (localizationAt L 𝔓))) (reducePoint L W P)) :=
  reducePoint_pointMapRing_frobenius L W p (comp_algebraMap_localizationAtRingHom 𝔓 hτ)
    (fun x ↦ by rw [residue_localizationAtRingHom_of_absNorm 𝔓 hτ 𝔭 x, hp]) P

end NumberField

end

end GroundTheory.Global
