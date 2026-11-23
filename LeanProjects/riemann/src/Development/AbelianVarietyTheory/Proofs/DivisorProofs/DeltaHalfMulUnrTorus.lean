import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Formalism.SatakeDualWeyl.StatementE
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUniMat

open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp ValuativeRel NumberField IsDedekindDomain
open scoped NNReal

noncomputable section
namespace GlobalTheory.LGrp.BorelCompletion

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem ordV_eq (x : v.adicCompletion F) : Formalism.UG.ordV F v x = -WithZero.log (Valued.v x) := by
  unfold Formalism.UG.ordV
  split_ifs with h
  · simp [h]
  · rw [WithZero.toAdd_unzero_eq_log]

theorem nabs_completion (x : (v.adicCompletion F)ˣ) :
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    GlobalTheory.SplitWeil.nabs (v.adicCompletion F) x =
      (Formalism.UG.qV F v : ℝ) ^ (WithZero.log (Valued.v (x : v.adicCompletion F))) := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  haveI : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (v.adicCompletion F))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))
  have hO : 𝒪[v.adicCompletion F] = (v.adicCompletionIntegers F).toSubring := by
    ext y
    rw [Valuation.mem_integer_iff, he.le_one_iff_le_one]
    exact Iff.rfl
  have hq : GlobalTheory.SplitWeil.resCard (v.adicCompletion F) = Formalism.UG.qV F v := by
    rw [← Formalism.UG.P.tjcosets_card_residue]
    exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (RingEquiv.subringCongr hO)).toEquiv
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact WithZero.exp_ne_zero (hπ.symm.trans (map_zero _))
  have hle : ∀ y : 𝒪[v.adicCompletion F], Valued.v (y : v.adicCompletion F) ≤ 1 := fun y =>
    he.le_one_iff_le_one.1 ((Valuation.mem_integer_iff _ _).1 y.2)
  have hunit : ∀ y : 𝒪[v.adicCompletion F], IsUnit y ↔ Valued.v (y : v.adicCompletion F) = 1 := fun y => by
    rw [← he.eq_one_iff_eq_one]
    exact (Valuation.integer.integers (valuation (v.adicCompletion F))).isUnit_iff_valuation_eq_one
  have hπO : π ∈ 𝒪[v.adicCompletion F] := by
    rw [Valuation.mem_integer_iff, he.le_one_iff_le_one, hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  have hirr : Irreducible (⟨π, hπO⟩ : 𝒪[v.adicCompletion F]) := by
    refine ⟨?_, fun a b hab => ?_⟩
    · rw [hunit]
      show Valued.v π ≠ 1
      rw [hπ, ← WithZero.exp_zero, Ne, WithZero.exp_inj]
      norm_num
    · have h1 : Valued.v (a : v.adicCompletion F) * Valued.v (b : v.adicCompletion F) =
          WithZero.exp (-1 : ℤ) := by
        rw [← hπ, ← map_mul]
        exact congrArg _ (congrArg Subtype.val hab).symm
      have ha : Valued.v (a : v.adicCompletion F) ≠ 0 := left_ne_zero_of_mul (by rw [h1]; simp)
      have hb : Valued.v (b : v.adicCompletion F) ≠ 0 := right_ne_zero_of_mul (by rw [h1]; simp)
      have ha1 := hle a
      have hb1 := hle b
      rw [hunit, hunit]
      rw [← WithZero.exp_log ha] at h1 ha1 ⊢
      rw [← WithZero.exp_log hb] at h1 hb1 ⊢
      rw [← WithZero.exp_add, WithZero.exp_inj] at h1
      rw [← WithZero.exp_zero, WithZero.exp_le_exp] at ha1 hb1
      rw [← WithZero.exp_zero, WithZero.exp_inj, WithZero.exp_inj]
      omega
  have h1 := GlobalTheory.SplitWeil.nabs_uniformiser hirr (x := Units.mk0 π hπ0) rfl
  rw [hq] at h1
  set m := WithZero.log (Valued.v (x : v.adicCompletion F)) with hm
  have hx : Valued.v (x : v.adicCompletion F) = WithZero.exp m := (WithZero.exp_log (by simp)).symm
  have h2 : GlobalTheory.SplitWeil.nabs (v.adicCompletion F) (x * (Units.mk0 π hπ0) ^ m) = 1 := by
    apply GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one
    rw [he.eq_one_iff_eq_one, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, Units.val_mk0,
      hπ, hx, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have h3 : GlobalTheory.SplitWeil.nabs (v.adicCompletion F) ((Units.mk0 π hπ0) ^ m) = ((Formalism.UG.qV F v : ℝ)⁻¹) ^ m := by
    rw [← h1]
    simp only [GlobalTheory.SplitWeil.nabs, map_zpow, NNReal.coe_zpow]
  rw [GlobalTheory.SplitWeil.nabs_mul, h3, inv_zpow] at h2
  exact (eq_inv_of_mul_eq_one_left h2).trans (inv_inv _)

theorem sqrt_zpow_eq (q : ℕ) (m e : ℤ) :
    ((Real.sqrt (((q : ℝ) ^ m) ^ e) : ℝ) : ℂ) = (q : ℂ) ^ ((m : ℂ) * ((e : ℂ) / 2)) := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rw [Real.sqrt_eq_rpow, ← zpow_mul, ← Real.rpow_intCast, ← Real.rpow_mul hq, Complex.ofReal_cpow hq]
  congr 1
  push_cast
  ring

theorem deltaHalf_mul_unrTorus : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) [LocallyCompactSpace (v.adicCompletion F)] (n : ℕ) (α : Fin n → ℂˣ) (b : (borelGL (v.adicCompletion F) (Fin n)).Q), (((borelGL (v.adicCompletion F) (Fin n)).deltaHalf b : ℂˣ) : ℂ) * ((unrTorus (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).toMonoidWithZeroHom α ((borelGL (v.adicCompletion F) (Fin n)).p b) : ℂˣ) : ℂ) = Formalism.UG.chiDelta F v (fun i => (α i : ℂ)) b.1 := by
  intro F _ _ v _ n α b
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  have h := GlobalTheory.BorelModulus.delta_borelGL (v.adicCompletion F) n b
  rw [LeviDatum.deltaHalf_coe, h, Real.sqrt_prod _ (fun i _ => zpow_nonneg (GlobalTheory.SplitWeil.nabs_pos _ _).le _),
    unrTorus_apply, Formalism.UG.chiDelta, Complex.ofReal_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e : (((borelGL (v.adicCompletion F) (Fin n)).p b i : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      (b.1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i := rfl
  rw [nabs_completion, sqrt_zpow_eq, unrChar_apply, ordV_eq, e, mul_comm, Units.val_zpow_eq_zpow_val]
  congr 2
  push_cast
  ring

end GlobalTheory.LGrp.BorelCompletion
