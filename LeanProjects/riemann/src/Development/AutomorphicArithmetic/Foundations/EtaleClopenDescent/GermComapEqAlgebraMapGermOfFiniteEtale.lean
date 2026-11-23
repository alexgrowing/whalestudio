import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry GlobalTheory.HodgeCoh GlobalTheory.CechDR ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace UpperTheory.Cb

section Alg

variable {B B' K L : Type} [CommRing B] [CommRing B'] [IsDomain B] [IsDomain B'] [Field K] [Field L]
  [Algebra B B'] [Algebra B K] [Algebra K L] [Algebra B' L] [Algebra B L]
  [IsScalarTower B K L] [IsScalarTower B B' L] [IsFractionRing B K] [IsFractionRing B' L]

include K L in
private theorem injective_algebraMap : Function.Injective (algebraMap B B') := by
  have h : Function.Injective (algebraMap B L) := by
    rw [IsScalarTower.algebraMap_eq B K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective B K)
  rw [IsScalarTower.algebraMap_eq B B' L] at h
  exact Function.Injective.of_comp (f := algebraMap B' L) h

include K L in
private theorem isLocalization_of_integral [Algebra.IsIntegral B B'] :
    IsLocalization (Algebra.algebraMapSubmonoid B' (nonZeroDivisors B)) L := by
  have hinj : Function.Injective (algebraMap B B') := injective_algebraMap (K := K) (L := L)
  have hL : Function.Injective (algebraMap B' L) := IsFractionRing.injective B' L
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · rintro ⟨_, r, hr, rfl⟩
    refine IsUnit.mk0 _ ?_
    exact (map_ne_zero_iff _ hL).2 ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hr))
  · intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := B') z
    obtain ⟨r, hr, t, ht⟩ := (Algebra.IsIntegral.isIntegral (R := B) b).isAlgebraic.exists_nonzero_dvd hb
    refine ⟨⟨a * t, ⟨algebraMap B B' r, r, mem_nonZeroDivisors_of_ne_zero hr, rfl⟩⟩, ?_⟩
    have hb0 : algebraMap B' L b ≠ 0 := (map_ne_zero_iff _ hL).2 (nonZeroDivisors.ne_zero hb)
    have e : algebraMap B' L (algebraMap B B' r) = algebraMap B' L b * algebraMap B' L t := by
      rw [ht, map_mul]
    change algebraMap B' L a / algebraMap B' L b * algebraMap B' L (algebraMap B B' r) =
      algebraMap B' L (a * t)
    rw [e, map_mul]
    field_simp
  · intro x y h
    exact ⟨1, by rw [hL h]⟩

include K L in
private theorem isPushout_of_integral [Algebra.IsIntegral B B'] : Algebra.IsPushout B K B' L := by
  have h1 := isLocalization_of_integral (B := B) (B' := B') (K := K) (L := L)
  have h2 := (isLocalizedModule_iff_isLocalization (S := nonZeroDivisors B) (A := B') (Aₛ := L)).2 h1
  exact ⟨(isLocalizedModule_iff_isBaseChange (nonZeroDivisors B) K _).1 h2⟩

private theorem algebraMap_etTrace [Module.Finite B B'] [Algebra.Etale B B'] (b : B') :
    algebraMap B K (etTrace B B' b) = Algebra.trace K L (algebraMap B' L b) := by
  haveI := projective_of_etale B B'
  haveI hp := isPushout_of_integral (B := B) (B' := B') (K := K) (L := L)
  haveI : Module.Finite K L := Module.Finite.equiv hp.out.equiv
  rw [← algTrace_eq_trace, algTrace_of_isPushout (B := B) (B' := B') b]
  rfl

end Alg

theorem germ_comap_eq_algebraMap_germ_of_finite_etale : ∀ (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (p : Z ⟶ Sp ℂ) (p' : Y ⟶ Sp ℂ)
    (c : Y ⟶ Z) (hc : c ≫ p = p') [IsFinite c] [Etale c] [Algebra Z.functionField Y.functionField],
    (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)),
      (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c.app V).hom g) =
        algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) →
    ∀ (V : Z.Opens) (hV : IsAffineOpen V) (hg : genericPoint Z ∈ V)
      (hg' : genericPoint Y ∈ c ⁻¹ᵁ V) (b' : Γ(Y, c ⁻¹ᵁ V)),
      (Z.presheaf.germ V (genericPoint Z) hg).hom (secTrace (f := c) p p' hV b') =
        Algebra.trace Z.functionField Y.functionField
          ((Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hg').hom b') := by
  intro Z Y _ _ p p' c _ _ _ _ hg V hVa hV hV' b'
  haveI : Nonempty V := ⟨⟨_, hV⟩⟩
  haveI : Nonempty (c ⁻¹ᵁ V : Y.Opens) := ⟨⟨_, hV'⟩⟩
  letI := secAlg p p' c V
  haveI := sec_finite (s := p) (s' := p') (f := c) hVa
  haveI := sec_etale (s := p) (s' := p') (f := c) hVa
  letI : Algebra (Sec p V) Z.functionField := (Z.germToFunctionField V).hom.toAlgebra
  letI : Algebra (Sec p' (c ⁻¹ᵁ V)) Y.functionField := (Y.germToFunctionField (c ⁻¹ᵁ V)).hom.toAlgebra
  letI : Algebra (Sec p V) Y.functionField :=
    ((algebraMap Z.functionField Y.functionField).comp (algebraMap (Sec p V) Z.functionField)).toAlgebra
  haveI : IsScalarTower (Sec p V) Z.functionField Y.functionField := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower (Sec p V) (Sec p' (c ⁻¹ᵁ V)) Y.functionField :=
    .of_algebraMap_eq fun g ↦ (hg V hV hV' g).symm
  haveI : IsDomain (Sec p V) := inferInstanceAs (IsDomain Γ(Z, V))
  haveI : IsDomain (Sec p' (c ⁻¹ᵁ V)) := inferInstanceAs (IsDomain Γ(Y, c ⁻¹ᵁ V))
  haveI : IsFractionRing (Sec p V) Z.functionField :=
    functionField_isFractionRing_of_isAffineOpen Z V hVa
  haveI : IsFractionRing (Sec p' (c ⁻¹ᵁ V)) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y (c ⁻¹ᵁ V) (hVa.preimage c)
  exact algebraMap_etTrace (B := Sec p V) (B' := Sec p' (c ⁻¹ᵁ V)) (K := Z.functionField)
    (L := Y.functionField) b'

end UpperTheory.Cb
