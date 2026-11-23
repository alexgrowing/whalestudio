import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExpEqOneAddAddSq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.NilpotentTwistStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.IsUnitCharacterDiffAtChosenInertiaStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ChosenFrobeniusIsFrobeniusStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.GaloisSubgroupLBasicPropertiesStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc.NilpotentTwist

theorem isUnit_algebraMap_of_ne_zero {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (C : Type) [CommRing C] [Algebra ℚ_[l] C] [Algebra O C]
    [Algebra ℤ_[l] C] [IsScalarTower ℤ_[l] O C] [IsScalarTower ℤ_[l] ℚ_[l] C] {c : O} (hc : c ≠ 0) :
    IsUnit (algebraMap O C c) := by
  have hI : (Ideal.span {c}).comap (algebraMap ℤ_[l] O) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hc (Ideal.mem_span_singleton_self c) (Algebra.IsIntegral.isIntegral c)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hn
  obtain ⟨d, hd⟩ := hn
  have hq : algebraMap ℤ_[l] ℚ_[l] n ≠ 0 := by
    first
      | exact (map_ne_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).mpr hn0
      | exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l])).mpr hn0
  have hu : IsUnit (algebraMap ℤ_[l] C n) := by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] C]
    exact (isUnit_iff_ne_zero.mpr hq).map (algebraMap ℚ_[l] C)
  rw [IsScalarTower.algebraMap_apply ℤ_[l] O C, hd, map_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

theorem isUnit_add_nil {C : Type} [CommRing C] {a n : C} (ha : IsUnit a) (hn : IsNilpotent n) : IsUnit (a + n) := by
  first
    | exact hn.isUnit_add_left_of_commute ha (Commute.all _ _)
    | exact IsNilpotent.isUnit_add_left_of_commute hn ha (Commute.all _ _)

theorem nil_mul {C : Type} [CommRing C] {t : C} (ht : IsNilpotent t) (z : C) : IsNilpotent (t * z) := by
  first
    | exact (Commute.all _ _).isNilpotent_mul_left ht
    | exact (Commute.all _ _).isNilpotent_mul_right ht
    | exact ht.mul_right (Commute.all _ _)

theorem prod_eq {C : Type} [CommRing C] (L K0 K1 ε t w a : C) (y : Cˣ) (hy : (y : C) = a * (1 + t * w)) :
    L * (K0 * ((y : C) - ε)) * (K1 * (1 - ε * ((y⁻¹ : Cˣ) : C))) =
      (L * K0 * K1 * ((y⁻¹ : Cˣ) : C)) * ((a - ε) + t * (a * w)) ^ 2 := by
  have h := y.mul_inv
  rw [hy] at h ⊢
  linear_combination (-(L * K0 * K1 * (a * (1 + t * w) - ε))) * h

end GlobalTheory.OrdLoc.NilpotentTwist

open GlobalTheory.OrdLoc.NilpotentTwist in

theorem GlobalTheory.OrdLoc.del_unr_twist {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E]
    [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E]
    (C : Type) [CommRing C] [Algebra ℚ_[l] C] [Module.Finite ℚ_[l] C] [Algebra O C] [Algebra ℤ_[l] C]
    [IsScalarTower ℤ_[l] O C] [IsScalarTower ℤ_[l] ℚ_[l] C] [Algebra E C] [IsScalarTower O E C]
    [IsScalarTower ℚ_[l] E C] (t : C) (ht : IsNilpotent t) :
    ∃ u : GQ l →* Cˣ, QCont l (fun g => (u g : C)) ∧ (∀ g ∈ Iq l, u g = 1) ∧ (∀ g, IsNilpotent ((u g : C) - 1)) ∧
      ∃ (j : ℕ) (v : Cˣ), j ≤ 2 ∧
        GlobalTheory.OrdLoc.del D (r0 D.η ((Units.map (algebraMap O C : O →* C)).comp D.Ψ * u)) = t ^ j * v := by
  obtain ⟨-, σ₀, m, hF, hm, hI⟩ := GlobalTheory.T.chosenFrobenius_isFrobenius D
  obtain ⟨-, -, -, -, hs0⟩ := GlobalTheory.T.galoisSubgroupL_basic_properties D
  obtain ⟨u, hcont, huI, hunil, v, hv⟩ := GlobalTheory.unr_unip_char_frob t ht σ₀ hF
  refine ⟨u, hcont, huI, hunil, ?_⟩
  obtain ⟨b, hb⟩ := hv m
  obtain ⟨-, hcc⟩ := GlobalTheory.T.isUnit_characterDiff_at_chosenInertia D C
  have huσ : u (fr D) = u (σ₀ ^ m) := by
    calc u (fr D) = u (σ₀ ^ m * ((σ₀ ^ m)⁻¹ * fr D)) := by rw [mul_inv_cancel_left]
      _ = u (σ₀ ^ m) := by rw [map_mul, huI _ hI, mul_one]
  have hmat : ∀ g, (r0 D.η ((Units.map (algebraMap O C : O →* C)).comp D.Ψ * u) g).mat =
      Matrix.diagonal (fun i => ((((Units.map (algebraMap O C : O →* C)).comp D.Ψ g * u g) ^ wt1 i : Cˣ) : C)) :=
    fun g => rfl
  have hdiag : (r0 D.η ((Units.map (algebraMap O C : O →* C)).comp D.Ψ * u) (s0 D)).mat =
      Matrix.diagonal (fun a => algebraMap O C (UpperTheory.V.UnitaryThreeInertia.psi D.Ψ a (s0 D))) := by
    rw [hmat, huI _ hs0.2.1, mul_one]
    congr 1
    funext a
    rw [MonoidHom.comp_apply, ← map_zpow, Units.coe_map]
    rfl
  have h0 := GlobalTheory.T.ordinary_derivative_entry_formula D _ hdiag 0
  have h1 := GlobalTheory.T.ordinary_derivative_entry_formula D _ hdiag 1
  rw [hmat, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at h0 h1
  have e01 : (0 : Fin 3) + 1 = 1 := rfl
  have e12 : (1 : Fin 3) + 1 = 2 := rfl
  have w0 : wt1 (0 : Fin 3) = 1 := rfl
  have w1 : wt1 (1 : Fin 3) = 0 := rfl
  have w2 : wt1 (2 : Fin 3) = -1 := rfl
  rw [e01, w0, w1, zpow_one, zpow_zero, Units.val_one, mul_one] at h0
  rw [e12, w1, w2, zpow_zero, zpow_neg_one, Units.val_one] at h1
  have hyv : (((Units.map (algebraMap O C : O →* C)).comp D.Ψ (fr D) * u (fr D) : Cˣ) : C) =
      algebraMap O C (D.Ψ (fr D) : O) * (1 + t * ((m : C) * v + t * b)) := by
    rw [Units.val_mul, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, huσ, ← hb]
    ring
  have hl : IsUnit (l : C) := by
    have : IsUnit ((l : ℚ_[l])) := isUnit_iff_ne_zero.mpr (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
    simpa using this.map (algebraMap ℚ_[l] C)
  have hmu : IsUnit (m : C) := by
    have : IsUnit ((m : ℚ_[l])) := isUnit_iff_ne_zero.mpr (by exact_mod_cast (show m ≠ 0 by omega))
    simpa using this.map (algebraMap ℚ_[l] C)
  have hk0 : IsUnit (algebraMap O C (cc D 0 * cc D 1)) := by rw [map_mul]; exact (hcc 0).mul (hcc 1)
  have hk1 : IsUnit (algebraMap O C (cc D 1 * cc D 2)) := by rw [map_mul]; exact (hcc 1).mul (hcc 2)
  have hw : IsUnit ((m : C) * v + t * b) := isUnit_add_nil (hmu.mul (Units.isUnit v)) (nil_mul ht b)
  have ha : IsUnit (algebraMap O C (D.Ψ (fr D) : O)) := (Units.isUnit (D.Ψ (fr D))).map (algebraMap O C)
  unfold GlobalTheory.OrdLoc.del
  rw [h0, h1, prod_eq _ _ _ _ _ _ _ _ hyv, ← map_sub]
  have hQ : IsUnit ((l : C) * algebraMap O C (cc D 0 * cc D 1) * algebraMap O C (cc D 1 * cc D 2) *
      ((((Units.map (algebraMap O C : O →* C)).comp D.Ψ (fr D) * u (fr D))⁻¹ : Cˣ) : C)) :=
    ((hl.mul hk0).mul hk1).mul (Units.isUnit _)
  by_cases hc : (D.Ψ (fr D) : O) - ((cycA l l O (fr D) : Oˣ) : O) = 0
  · rw [hc, map_zero, zero_add]
    refine ⟨2, (hQ.mul ((ha.mul hw).pow 2)).unit, le_rfl, ?_⟩
    rw [IsUnit.unit_spec]
    ring
  · have hn : IsUnit (algebraMap O C ((D.Ψ (fr D) : O) - ((cycA l l O (fr D) : Oˣ) : O)) +
        t * (algebraMap O C (D.Ψ (fr D) : O) * ((m : C) * v + t * b))) :=
      isUnit_add_nil (isUnit_algebraMap_of_ne_zero (l := l) C hc) (nil_mul ht _)
    refine ⟨0, (hQ.mul (hn.pow 2)).unit, by norm_num, ?_⟩
    rw [IsUnit.unit_spec, pow_zero, one_mul]
