import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeNotMemRingKrullDimQuotientEqOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueFieldMapAdicCompletionSurjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
namespace GlobalTheory

theorem isJacobsonRing_int_of_dim_one : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases h : P = ⊥
  · subst h
    refine le_antisymm (fun x hx => ?_) Ideal.le_jacobson
    rw [Ideal.mem_bot]
    by_contra h0
    have h1 := Ideal.mem_jacobson_bot.1 hx x
    have h2 : 0 < x * x := mul_self_pos.2 h0
    rcases Int.isUnit_iff.1 h1 with h3 | h3 <;> omega
  · have := Ring.DimensionLEOne.maximalOfPrime h hP
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem exists_trait_finite_residueField_charZero_avoiding : ∀ (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B] (m : Ideal B) (h : B), m.IsMaximal → h ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : CharZero V) (t : B →+* V), IsAdicComplete (IsLocalRing.maximalIdeal V) V ∧ Finite (IsLocalRing.ResidueField V) ∧ t h ≠ 0 ∧ (IsLocalRing.maximalIdeal V).comap t = m := by
  intro B _ _ _ _ m h hm hh
  classical

  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  haveI : IsJacobsonRing ℤ := isJacobsonRing_int_of_dim_one
  haveI : Algebra.FiniteType ℤ (B ⧸ m) :=
    .of_surjective (Ideal.Quotient.mkₐ ℤ _) (Ideal.Quotient.mkₐ_surjective ℤ _)
  haveI : Module.Finite ℤ (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℤ (B ⧸ m)
  set p := ringChar (B ⧸ m) with hpdef
  have hp0 : p ≠ 0 := by
    intro h0
    haveI : CharP (B ⧸ m) 0 := h0 ▸ ringChar.charP (B ⧸ m)
    haveI : CharZero (B ⧸ m) := CharP.charP_to_charZero _
    haveI : Algebra.IsIntegral ℤ (B ⧸ m) := Algebra.IsIntegral.of_finite ℤ _
    exact Int.not_isField
      (isField_of_isIntegral_of_isField (algebraMap ℤ (B ⧸ m)).injective_int (Field.toIsField _))
  haveI : CharP (B ⧸ m) p := ringChar.charP (B ⧸ m)
  haveI : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero (B ⧸ m) p).resolve_right hp0⟩
  letI : Algebra (ZMod p) (B ⧸ m) := ZMod.algebra (B ⧸ m) p
  haveI : IsScalarTower ℤ (ZMod p) (B ⧸ m) := AddCommGroup.intIsScalarTower
  haveI : Algebra.FiniteType (ZMod p) (B ⧸ m) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) (B ⧸ m)
  haveI : Module.Finite (ZMod p) (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing (ZMod p) (B ⧸ m)
  haveI hfin : Finite (B ⧸ m) := Module.finite_of_finite (ZMod p)
  have hpm : (p : B) ∈ m := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact CharP.cast_eq_zero _ p
  have hpB : (p : B) ≠ 0 := Nat.cast_ne_zero.mpr hp0

  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  let R := Localization.AtPrime m
  haveI hRn : IsNoetherianRing R := IsLocalization.isNoetherianRing m.primeCompl R inferInstance
  have hinj : Function.Injective (algebraMap B R) :=
    IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors m)
  have hx0 : algebraMap B R (h * p) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap B R)]; exact fun e => mul_ne_zero hh hpB (hinj e)
  have hxm : algebraMap B R (h * p) ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff R m _).mpr (m.mul_mem_left h hpm)
  obtain ⟨q, hq, hnq, hdim⟩ := GlobalTheory.T.exists_prime_not_mem_ringKrullDim_quotient_eq_one R (algebraMap B R (h * p)) hx0 hxm
  let D := R ⧸ q
  haveI : IsDomain D := Ideal.Quotient.isDomain q
  haveI : IsLocalRing D := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  let φ : B →+* D := (Ideal.Quotient.mk q).comp (algebraMap B R)
  have hcompR : Ideal.comap (Ideal.Quotient.mk q) (IsLocalRing.maximalIdeal D) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  have hcomp : Ideal.comap φ (IsLocalRing.maximalIdeal D) = m := by
    rw [← Ideal.comap_comap, hcompR]; exact Localization.AtPrime.comap_maximalIdeal
  have hφh : φ h ≠ 0 := by
    intro e; apply hnq
    rw [map_mul]; exact q.mul_mem_right _ ((Ideal.Quotient.eq_zero_iff_mem).mp e)
  have hφp : φ (p : B) ≠ 0 := by
    intro e; apply hnq
    rw [map_mul]; exact q.mul_mem_left _ ((Ideal.Quotient.eq_zero_iff_mem).mp e)
  haveI hD0 : CharZero D := by
    haveI : CharP D (ringChar D) := ringChar.charP D
    rcases CharP.char_is_prime_or_zero D (ringChar D) with hl | hl
    · exfalso
      have hlm' : ((ringChar D : ℕ) : B) ∈ Ideal.comap φ (IsLocalRing.maximalIdeal D) := by
        rw [Ideal.mem_comap, map_natCast, CharP.cast_eq_zero]; exact zero_mem _
      have hlm : ((ringChar D : ℕ) : B) ∈ m := hcomp.le hlm'
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at hlm
      have hdvd : p ∣ ringChar D := (CharP.cast_eq_zero_iff (B ⧸ m) p _).mp hlm
      have hpl : p = ringChar D :=
        ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hl).mp hdvd)
      apply hφp; rw [map_natCast, hpl, CharP.cast_eq_zero]
    · haveI : CharP D 0 := hl ▸ ringChar.charP D
      exact CharP.charP_to_charZero D

  have hsurj : Function.Surjective ((IsLocalRing.residue D).comp φ) := by
    intro y
    obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective d
    have hsR := IsLocalization.surjective_quotientMap_of_maximal_of_localization m.primeCompl R
      (I := IsLocalRing.maximalIdeal R) (J := m)
      (H := le_of_eq Localization.AtPrime.comap_maximalIdeal.symm)
      (by rw [Localization.AtPrime.comap_maximalIdeal]; exact hm)
    obtain ⟨bb, hb⟩ := hsR (Ideal.Quotient.mk _ r)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective bb
    refine ⟨b, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hb
    simp only [RingHom.comp_apply]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have hb' : algebraMap B R b - r ∈ Ideal.comap (Ideal.Quotient.mk q) (IsLocalRing.maximalIdeal D) :=
      hcompR ▸ hb
    simpa [φ, map_sub] using hb'
  have hker : ∀ b ∈ m, ((IsLocalRing.residue D).comp φ) b = 0 := by
    intro b hb
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, ← Ideal.mem_comap, hcomp]; exact hb
  haveI hresfin : Finite (IsLocalRing.ResidueField D) :=
    Finite.of_surjective (Ideal.Quotient.lift m _ hker) (by
      intro y; obtain ⟨b, rfl⟩ := hsurj y; exact ⟨Ideal.Quotient.mk m b, rfl⟩)
  obtain ⟨V, _, _, _, hcV, g, hg, hgl, hVfin⟩ :=
    GlobalTheory.exists_complete_dvr_finite_residueField D inferInstance hdim hresfin
  haveI : CharZero V := ⟨fun a b e => by
    apply Nat.cast_injective (R := D); apply hg; rw [map_natCast, map_natCast]; exact e⟩
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, g.comp φ, hcV, hVfin, ?_, ?_⟩
  · rw [RingHom.comp_apply]; intro e; apply hφh; apply hg; rw [e, map_zero]
  · have hgm : Ideal.comap g (IsLocalRing.maximalIdeal V) = IsLocalRing.maximalIdeal D := by
      ext x; simp [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
    rw [← Ideal.comap_comap, hgm, hcomp]

end GlobalTheory
