import Mathlib
import GroundTheory.GlobalFields.SUnitsKernel

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Module
open scoped NumberField nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace SUnit

theorem exists_pow_classNumber_eq_span (v : HeightOneSpectrum (𝓞 K)) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ v.asIdeal ^ classNumber K = Ideal.span {a} := by
  let I : (Ideal (𝓞 K))⁰ := ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
  have h1 : ClassGroup.mk0 (I ^ classNumber K) = 1 := by
    rw [map_pow, classNumber, Fintype.card_eq_nat_card]
    exact pow_card_eq_one'
  have h2 := (ClassGroup.mk0_eq_one_iff (I ^ classNumber K).2).mp h1
  obtain ⟨a, ha⟩ := h2.principal
  have ha' : v.asIdeal ^ classNumber K = Ideal.span {a} := by
    rw [SubmonoidClass.coe_pow] at ha
    exact ha
  refine ⟨a, ?_, ha'⟩
  rintro rfl
  rw [Ideal.span_singleton_eq_bot.mpr rfl] at ha'
  exact pow_ne_zero _ v.ne_bot ha'

open scoped Classical in

theorem intValuation_of_pow_eq_span {v w : HeightOneSpectrum (𝓞 K)} {a : 𝓞 K} (ha : a ≠ 0)
    {n : ℕ} (h : v.asIdeal ^ n = Ideal.span {a}) :
    w.intValuation a = if w = v then WithZero.exp (-(n : ℤ)) else 1 := by
  rw [intValuation_eq_exp_neg_multiplicity w ha, ← h]
  split_ifs with hw
  · subst hw
    rw [multiplicity_pow_self_of_prime w.prime n]
  · have h0 : multiplicity w.asIdeal (v.asIdeal ^ n) = 0 := by
      rw [multiplicity_eq_zero]
      intro hdvd
      apply hw
      have hle : v.asIdeal ≤ w.asIdeal := Ideal.le_of_dvd (w.prime.dvd_of_dvd_pow hdvd)
      exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm
    rw [h0]
    simp

def placeUnit (v : HeightOneSpectrum (𝓞 K)) : Kˣ :=
  Units.mk0 (algebraMap (𝓞 K) K (exists_pow_classNumber_eq_span v).choose) <| by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
    exact (exists_pow_classNumber_eq_span v).choose_spec.1

open scoped Classical in
theorem valuationOfNeZero_placeUnit (v w : HeightOneSpectrum (𝓞 K)) :
    w.valuationOfNeZero (placeUnit v) =
      if w = v then Multiplicative.ofAdd (-(classNumber K : ℤ)) else 1 := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq, placeUnit, Units.val_mk0,
    valuation_of_algebraMap, intValuation_of_pow_eq_span
      (exists_pow_classNumber_eq_span v).choose_spec.1
      (exists_pow_classNumber_eq_span v).choose_spec.2]
  split_ifs <;> rfl

variable (S : Set (HeightOneSpectrum (𝓞 K)))

theorem placeUnit_mem {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) : placeUnit v ∈ S.unit K := by
  intro w hw
  have hwv : w ≠ v := fun h => hw (h ▸ hv)
  rw [← valuationOfNeZero_eq, valuationOfNeZero_placeUnit, if_neg hwv, WithZero.coe_one]

open scoped Classical in
theorem valuationVector_placeUnit (v : S) :
    valuationVector S (Additive.ofMul ⟨placeUnit v.1, placeUnit_mem S v.2⟩) =
      Pi.single v (-(classNumber K : ℤ)) := by
  funext w
  rw [valuationVector_apply, valuationOfNeZero_placeUnit]
  by_cases h : w = v
  · subst h; simp
  · have h' : w.1 ≠ v.1 := fun e => h (Subtype.ext e)
    simp [h, h']

theorem valuation_eq_one_of_isOfFinOrder {x : Kˣ} (hx : IsOfFinOrder x)
    (v : HeightOneSpectrum (𝓞 K)) : v.valuation K (x : K) = 1 := by
  have h := v.valuationOfNeZero.isOfFinOrder hx
  rw [isOfFinOrder_iff_eq_one] at h
  rw [← valuationOfNeZero_eq, h, WithZero.coe_one]

def torsionEquiv : Units.torsion K ≃* CommGroup.torsion (S.unit K) :=
  MulEquiv.ofBijective
    ({ toFun := fun ζ => ⟨ofUnits S ζ, (ofUnits S).isOfFinOrder ζ.2⟩
       map_one' := Subtype.ext (map_one (ofUnits S))
       map_mul' := fun a b => Subtype.ext (map_mul (ofUnits S) (a : (𝓞 K)ˣ) b) } :
        Units.torsion K →* CommGroup.torsion (S.unit K)) <| by
    constructor
    · intro a b h
      exact Subtype.ext (ofUnits_injective S (congrArg Subtype.val h))
    · rintro ⟨x, hx⟩
      have hx' : IsOfFinOrder (x : Kˣ) := (S.unit K).subtype.isOfFinOrder hx
      obtain ⟨u, hu⟩ :=
        (forall_valuation_eq_one_iff (x : Kˣ)).mp (valuation_eq_one_of_isOfFinOrder hx')
      have hux : ofUnits S u = x := Subtype.ext hu
      refine ⟨⟨u, ?_⟩, Subtype.ext hux⟩
      change u ∈ CommGroup.torsion _
      rw [CommGroup.mem_torsion, ← orderOf_pos_iff,
        ← orderOf_injective (ofUnits S) (ofUnits_injective S), hux, orderOf_pos_iff]
      exact hx

instance : Finite (CommGroup.torsion (S.unit K)) :=
  Finite.of_equiv _ (torsionEquiv S).toEquiv

instance : IsCyclic (CommGroup.torsion (S.unit K)) :=
  isCyclic_of_surjective (torsionEquiv S).toMonoidHom (torsionEquiv S).surjective

variable [Finite S]

def placeUnitsMap : (S → ℤ) →ₗ[ℤ] Additive (S.unit K) :=
  (Pi.basisFun ℤ S).constr ℤ fun v => Additive.ofMul ⟨placeUnit v.1, placeUnit_mem S v.2⟩

theorem valuationVector_comp_placeUnitsMap :
    valuationVector S ∘ₗ placeUnitsMap S = (-(classNumber K : ℤ)) • LinearMap.id := by
  classical
  refine (Pi.basisFun ℤ S).ext fun v => ?_
  rw [LinearMap.comp_apply, placeUnitsMap, Basis.constr_basis, valuationVector_placeUnit,
    LinearMap.smul_apply, LinearMap.id_apply, Pi.basisFun_apply]
  rw [← Pi.single_smul, smul_eq_mul, mul_one]

theorem finrank_range_valuationVector :
    finrank ℤ (LinearMap.range (valuationVector S)) = Nat.card S := by
  have : Fintype S := Fintype.ofFinite S
  apply le_antisymm
  · calc finrank ℤ (LinearMap.range (valuationVector S)) ≤ finrank ℤ (S → ℤ) :=
          Submodule.finrank_le _
      _ = Nat.card S := by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_eq_nat_card]
  · have hinj : Function.Injective (valuationVector S ∘ₗ placeUnitsMap S) := by
      rw [valuationVector_comp_placeUnitsMap]
      intro c d hcd
      have hh : (-(classNumber K : ℤ)) ≠ 0 := by
        simpa using classNumber_ne_zero K
      exact smul_right_injective (S → ℤ) hh hcd
    calc Nat.card S = finrank ℤ (S → ℤ) := by
          rw [Module.finrank_fintype_fun_eq_card, Fintype.card_eq_nat_card]
      _ = finrank ℤ (LinearMap.range (valuationVector S ∘ₗ placeUnitsMap S)) :=
          (LinearMap.finrank_range_of_inj hinj).symm
      _ ≤ finrank ℤ (LinearMap.range (valuationVector S)) :=
          Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)

instance : Module.Finite ℤ (Additive (S.unit K)) := by
  rw [Module.finite_def]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (valuationVector S) ?_ ?_
  · exact IsNoetherian.noetherian _
  · rw [inf_of_le_right le_top, ← Module.Finite.iff_fg]
    exact Module.Finite.equiv (unitsEquivKer S)

theorem fg : Group.FG (S.unit K) := by
  rw [Group.fg_iff_monoid_fg, Monoid.fg_iff_add_fg, ← AddGroup.fg_iff_addMonoid_fg,
    ← Module.Finite.iff_addGroup_fg]
  infer_instance

instance : Group.FG (S.unit K) := fg S

theorem finrank_eq : finrank ℤ (Additive (S.unit K)) = Units.rank K + Nat.card S := by
  rw [← Submodule.finrank_quotient_add_finrank (LinearMap.ker (valuationVector S)),
    LinearEquiv.finrank_eq (valuationVector S).quotKerEquivRange,
    finrank_range_valuationVector, ← LinearEquiv.finrank_eq (unitsEquivKer S),
    Units.finrank_eq, add_comm]

end SUnit

end

end GroundTheory.Global
