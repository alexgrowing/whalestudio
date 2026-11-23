import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuationOverFiniteDvrExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IntOverCdvr

open IsLocalRing

theorem isIntegralElem_of_val_nonneg : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra.IsAlgebraic (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ F v → ∀ z : F, 0 ≤ v z → ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))).IsIntegralElem z := by
  intro V _ _ _ hV ϖ hϖ F _ _ _ v hv z hz
  obtain ⟨hdvr, hcomp, hchar⟩ := hV
  let K := FractionRing V
  letI : Algebra V F := ((algebraMap K F).comp (algebraMap V K)).toAlgebra
  haveI : IsScalarTower V K F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FaithfulSMul V F := (faithfulSMul_iff_algebraMap_injective V F).mpr
    ((algebraMap K F).injective.comp (IsFractionRing.injective V K))
  haveI : Algebra.IsAlgebraic V F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := K) (C := F)).mpr inferInstance
  obtain ⟨W, hW, -, -, hfin, -, hloc, hs, -⟩ := GlobalTheory.exists_complete_dvr_finite_subalgebra V F {z}
  haveI := hfin

  have hVnn : ∀ r : V, 0 ≤ v (algebraMap V F r) := fun r =>
    GlobalTheory.FiniteDVRValuation.val_nonneg hϖ hv r

  let S : ValuationSubring F := GlobalTheory.FiniteDVRValuation.nonnegSubring v (RingHom.id F)
  have hWnn : ∀ w ∈ W, 0 ≤ v w := by
    intro w hw
    have hint : IsIntegral V w := (Algebra.IsIntegral.isIntegral (R := V) (⟨w, hw⟩ : W)).map W.val
    let φ : V →+* S := (algebraMap V F).codRestrict S (fun r => hVnn r)
    have hS : (algebraMap S F).IsIntegralElem w := RingHom.IsIntegralElem.of_comp (f := φ) hint
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := S) (K := F)).1 hS
    rw [← hy]
    exact y.2

  have hϖpos : 0 < v (algebraMap V F ϖ) := by
    obtain ⟨n, hn, hu⟩ := GlobalTheory.FiniteDVRValuation.exists_nat_val hϖ hv hϖ.ne_zero
    have hn0 : n ≠ 0 := fun h => hϖ.not_isUnit (hu h)
    change 0 < v (algebraMap K F (algebraMap V K ϖ))
    rw [hn]
    exact_mod_cast Nat.pos_of_ne_zero hn0

  have hunit : ∀ c : W, v (c : F) = 0 → IsUnit c := by
    intro c hc
    by_contra hnu
    have hinj : Function.Injective (algebraMap V W) := by
      intro a b hab
      apply FaithfulSMul.algebraMap_injective V F
      have := congrArg Subtype.val hab
      simpa using this
    set ϖW : W := algebraMap V W ϖ
    have hϖW0 : ϖW ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
    obtain ⟨N, hN⟩ : ∃ N : ℕ, IsDiscreteValuationRing.addVal W ϖW = N := by
      rcases h : IsDiscreteValuationRing.addVal W ϖW with _ | N
      · exact absurd (IsDiscreteValuationRing.addVal_eq_top_iff.1 h) hϖW0
      · exact ⟨N, rfl⟩
    have hc1 : 1 ≤ IsDiscreteValuationRing.addVal W c := by
      rw [ENat.one_le_iff_ne_zero]
      exact fun h => hnu (IsDiscreteValuationRing.addVal_eq_zero_iff.1 h)
    have hdvd : ϖW ∣ c ^ N := by
      rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, AddValuation.map_pow, hN]
      calc (N : ℕ∞) = N • (1 : ℕ∞) := by simp
        _ ≤ N • IsDiscreteValuationRing.addVal W c := nsmul_le_nsmul_right hc1 N
    obtain ⟨d, hd⟩ := hdvd
    have h1 : v ((c : F) ^ N) = 0 := by rw [AddValuation.map_pow, hc, nsmul_zero]
    have h2 : v ((c : F) ^ N) = v (algebraMap V F ϖ) + v (d : F) := by
      rw [← AddValuation.map_mul]
      congr 1
      have h := congrArg Subtype.val hd
      simp only [SubmonoidClass.coe_pow, MulMemClass.coe_mul] at h
      exact h
    have h3 : 0 < v ((c : F) ^ N) := by
      rw [h2]
      exact lt_of_lt_of_le hϖpos (le_add_of_nonneg_right (hWnn d d.2))
    rw [h1] at h3
    exact lt_irrefl _ h3

  obtain ⟨a, ha, b, hb, hb0, hab⟩ := hs z (Finset.mem_singleton_self z)
  have hzW : z ∈ W := by
    let a' : W := ⟨a, ha⟩
    let b' : W := ⟨b, hb⟩
    rcases le_total (IsDiscreteValuationRing.addVal W b') (IsDiscreteValuationRing.addVal W a') with h | h
    · obtain ⟨c, hc⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.1 h
      have hc' : a = b * c := congrArg Subtype.val hc
      have : z = c := by
        apply mul_left_cancel₀ hb0
        rw [mul_comm, hab, hc']
      rw [this]; exact c.2
    · obtain ⟨c, hc⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.1 h
      have hc' : b = a * c := congrArg Subtype.val hc
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact hb0 (by simpa using hc')
      have hzc : z * c = 1 := by
        apply mul_left_cancel₀ ha0
        calc a * (z * c) = z * (a * c) := by ring
          _ = a * 1 := by rw [← hc', hab, _root_.mul_one]
      have hz0 : z ≠ 0 := left_ne_zero_of_mul_eq_one hzc
      have hvc : v (c : F) = 0 := by
        have hsum : v z + v (c : F) = 0 := by rw [← AddValuation.map_mul, hzc, AddValuation.map_one]
        have hc0 := hWnn c c.2
        refine le_antisymm ?_ hc0
        calc v (c : F) = 0 + v (c : F) := (zero_add _).symm
          _ ≤ v z + v (c : F) := by gcongr
          _ = 0 := hsum
      obtain ⟨u, hu⟩ := hunit c hvc
      have : z = ((u⁻¹ : Wˣ) : W) := by
        have h1 : ((u : W) : F) * (((u⁻¹ : Wˣ) : W) : F) = 1 := by
          rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
        rw [hu] at h1
        calc z = z * ((c : F) * (((u⁻¹ : Wˣ) : W) : F)) := by rw [h1, _root_.mul_one]
          _ = (z * c) * (((u⁻¹ : Wˣ) : W) : F) := by ring
          _ = _ := by rw [hzc, _root_.one_mul]
      rw [this]; exact Subtype.property _

  exact (Algebra.IsIntegral.isIntegral (R := V) (⟨z, hzW⟩ : W)).map W.val

end GlobalTheory.IntOverCdvr
