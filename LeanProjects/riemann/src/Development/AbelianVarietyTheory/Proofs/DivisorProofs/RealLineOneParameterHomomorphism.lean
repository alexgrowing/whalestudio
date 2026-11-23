import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormallyUnramifiedRingOfIntegersIffDifferentIdea
open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors
open Formalism.L2.Host (aboveF)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UnrEuler

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def ideleAtF (v : HeightOneSpectrum (𝓞 F)) : (Fv F v)ˣ →* (AF F)ˣ :=
  Units.map
    { toFun := fun y => 1 - GlobalTheory.Doubling.inFin v 1 + GlobalTheory.Doubling.inFin v y
      map_one' := sub_add_cancel _ _
      map_mul' := fun a b => by
        have h1 := GlobalTheory.Doubling.inFin_mul v 1 1
        have h2 := GlobalTheory.Doubling.inFin_mul v a 1
        have h3 := GlobalTheory.Doubling.inFin_mul v 1 b
        rw [mul_one] at h1 h2
        rw [one_mul] at h3
        rw [GlobalTheory.Doubling.inFin_mul]
        linear_combination h1 - h2 - h3 }

theorem ideleAt_algebraMap (v : HeightOneSpectrum (𝓞 F)) (a : (Fv F v)ˣ) :
    GlobalTheory.Doubling.ideleAt F E v (Units.map (algebraMap (Fv F v) (Fv F v ⊗[F] E) : Fv F v →* Fv F v ⊗[F] E) a) =
      Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) (ideleAtF v a) := by
  refine Units.ext ?_
  rw [GlobalTheory.Doubling.ideleAt, GlobalTheory.Doubling.val_extUnit]
  change 1 - GlobalTheory.Doubling.inFin v 1 ⊗ₜ[F] (1 : E) + GlobalTheory.Doubling.inFin v a ⊗ₜ[F] (1 : E) =
    (1 - GlobalTheory.Doubling.inFin v 1 + GlobalTheory.Doubling.inFin v a) ⊗ₜ[F] (1 : E)
  rw [TensorProduct.add_tmul, TensorProduct.sub_tmul]
  rfl

open Classical in

theorem count_map_prime (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) :
    FractionalIdeal.count E w ((v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) =
      if w.under (𝓞 F) = v then (w.asIdeal.ramificationIdx (𝓞 F) : ℤ) else 0 := by
  classical
  have h0 : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot v.ne_bot
  rw [FractionalIdeal.count_coe E w h0]
  split_ifs with h
  · subst h
    have : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
    rw [Ideal.count_associates_factors_eq h0 w.isPrime w.ne_bot,
      Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ _ h0]
  · rw [Nat.cast_eq_zero]
    by_contra hc
    rw [← Ne, Associates.count_ne_zero_iff_dvd h0 w.irreducible, Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap] at hc
    apply h
    exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le (w.under (𝓞 F)).isPrime.ne_top hc).symm

theorem idealVal_map_prime (ν : Chr F E)
    (hν : ∀ x : (AF F)ˣ, ν (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) x) = 1)
    (v : HeightOneSpectrum (𝓞 F)) (hu : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt ν w) :
    idealVal ν ((v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
  classical
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hv : Valued.v (algebraMap F (Fv F v) π) = WithZero.exp (-1 : ℤ) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π).trans hπ
  have ha : algebraMap F (Fv F v) π ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have h1 := hν (ideleAtF v (Units.mk0 _ ha))
  rw [← ideleAt_algebraMap, ideleAt_eq_prod_locIdele, map_prod] at h1
  have h2 := congrArg Circle.toUnits h1
  rw [map_prod, map_one] at h2
  unfold idealVal
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := (Formalism.L2.Host.finite_aboveF (L := E) F v).toFinset),
    ← Finset.prod_attach, ← h2]
  · refine Finset.prod_congr rfl fun w _ => ?_
    have h : w.1.under (𝓞 F) = v := (Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.1 w.2
    refine (locChar_eq_val_zpow (hu _ h) ?_).symm
    rw [count_map_prime, if_pos h]
    change Valued.v (toCompl h (algebraMap F (Fv F v) π ⊗ₜ[F] (1 : E))) = _
    rw [toCompl_tmul, map_one, mul_one, complMap_algebraMap]
    have : w.1.asIdeal.LiesOver v.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal h).symm⟩
    refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w.1 (algebraMap F E π)).trans ?_
    rw [← HeightOneSpectrum.valuation_liesOver E v w.1 π,
      Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot, hπ, ← WithZero.exp_nsmul]
    simp
  · intro w hw
    by_contra hc
    apply hw
    have h : ¬ w.under (𝓞 F) = v := fun h =>
      hc ((Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.2 h)
    simp only [count_map_prime, if_neg h, zpow_zero]

theorem idealVal_map (ν : Chr F E)
    (hν : ∀ x : (AF F)ˣ, ν (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) x) = 1)
    (I : Ideal (𝓞 F)) : I ≠ 0 →
    (∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal ∣ I.map (algebraMap (𝓞 F) (𝓞 E)) → UnrAt ν w) →
    idealVal ν ((I.map (algebraMap (𝓞 F) (𝓞 E)) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun h => absurd rfl h
  | h₂ x hx =>
    intro _ _
    rw [Ideal.isUnit_iff.1 hx, Ideal.map_top]
    simp [idealVal, FractionalIdeal.count_one]
  | h₃ a p ha hp ih =>
    intro _ hu
    let v : HeightOneSpectrum (𝓞 F) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    rw [Ideal.map_mul] at hu ⊢
    rw [FractionalIdeal.coeIdeal_mul, idealVal_mul ν
      (FractionalIdeal.coeIdeal_ne_zero.2 (Ideal.map_ne_bot_of_ne_bot hp.ne_zero))
      (FractionalIdeal.coeIdeal_ne_zero.2 (Ideal.map_ne_bot_of_ne_bot ha)),
      ih ha fun w hw => hu w (hw.mul_left _), mul_one]
    refine idealVal_map_prime ν hν v fun w hw => hu w (Dvd.dvd.mul_right ?_ _)
    rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
    exact (congrArg HeightOneSpectrum.asIdeal hw).ge

theorem idealVal_diffE : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ ν : Chr F E, (∀ x : (AF F)ˣ, ν (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) x) = 1) → (∀ w : HeightOneSpectrum (𝓞 E), FractionalIdeal.count E w (diffE E) ≠ 0 → UnrAt ν w) → idealVal ν (diffE E) = 1 := by
  intro F E _ _ _ _ _ hU ν hν hu
  classical
  have hd : differentIdeal ℤ (𝓞 E) = (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E),
      (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hU.formallyUnramified, Ideal.top_mul]
  have h0 : differentIdeal ℤ (𝓞 E) ≠ 0 := differentIdeal_ne_bot
  have := idealVal_map ν hν (differentIdeal ℤ (𝓞 F)) differentIdeal_ne_bot fun w hw => hu w (by
    rw [← hd] at hw
    rw [diffE, FractionalIdeal.count_coe E w h0, Nat.cast_ne_zero]
    exact (Associates.count_ne_zero_iff_dvd h0 w.irreducible).2 hw)
  rwa [← hd] at this

end GlobalTheory.UnrEuler
