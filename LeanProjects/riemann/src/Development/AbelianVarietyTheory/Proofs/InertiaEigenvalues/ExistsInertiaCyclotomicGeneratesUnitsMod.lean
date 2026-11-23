import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterValuesInjectiveLength
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameFixedLift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.ConsExists GlobalTheory.SpanRing
namespace GlobalTheory.CycGen

open Pointwise

theorem fix_of_unram {E Ω : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field Ω] [Algebra E Ω]
    [Algebra ℚ Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hw : IsPlaceOver A w)
    (he : w.asIdeal.ramificationIdx ℤ = 1) (σ : G ℚ Ω) (hσ : σ ∈ Ine (F := ℚ) A) (x : E) :
    σ (algebraMap E Ω x) = algebraMap E Ω x := by
  have : IsScalarTower ℚ E Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  set τ : E ≃ₐ[ℚ] E := AlgEquiv.restrictNormalHom E σ with hτdef
  have hcomm : ∀ y : E, algebraMap E Ω (τ y) = σ (algebraMap E Ω y) := fun y =>
    AlgEquiv.restrictNormal_commutes σ E y
  have hin : τ ∈ Ideal.inertia (E ≃ₐ[ℚ] E) w.asIdeal := by
    intro y
    show τ • y - y ∈ w.asIdeal
    rw [← hw]
    have hy : algebraMap E Ω (y : E) ∈ A :=
      ReciprocityTheory.Gal.mem_of_isIntegral_int A ((y.2).map (IsScalarTower.toAlgHom ℤ E Ω))
    have h := hσ.2 (algebraMap E Ω (y : E)) ((A.valuation_le_one_iff _).mpr hy)
    have e : ((τ • y - y : 𝓞 E) : E) = τ y - y := rfl
    rw [e, map_sub, hcomm]
    exact h
  have hcard : Nat.card (Ideal.inertia (E ≃ₐ[ℚ] E) w.asIdeal) = 1 := by
    have := w.isPrime
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[ℚ] E) (w.asIdeal.under ℤ) w.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (w.asIdeal.under ℤ) w.asIdeal (E ≃ₐ[ℚ] E), he]
  have h1 : τ = 1 := by
    have := (Subgroup.card_eq_one.mp hcard)
    have h2 : τ ∈ (⊥ : Subgroup (E ≃ₐ[ℚ] E)) := this ▸ hin
    exact Subgroup.mem_bot.mp h2
  rw [← hcomm, h1]
  rfl

end GlobalTheory.CycGen

namespace GlobalTheory.CycGen

theorem exists_unit_gen (l : ℕ) [Fact l.Prime] :
    ∃ v : ℤ_[l]ˣ, orderOf (PadicInt.toZMod (v : ℤ_[l])) = l - 1 := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  set b : ℤ_[l] := ((a : ZMod l).val : ℤ_[l])
  have hb : PadicInt.toZMod b = (a : ZMod l) := by
    simp only [b, map_natCast, ZMod.natCast_zmod_val]
  have hu : IsUnit b := by
    by_contra hn
    have hm : b ∈ IsLocalRing.maximalIdeal ℤ_[l] := hn
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, hb] at hm
    exact a.ne_zero hm
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec, hb, orderOf_units, orderOf_eq_card_of_forall_mem_zpowers ha,
    Nat.card_eq_fintype_card, ZMod.card_units]

theorem main : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc), (∀ v ∈ placesOver H.E (N.l i), v.asIdeal.ramificationIdx ℤ = 1) → ∃ w ∈ placesOver H.E (N.l i), ∃ g0 ∈ Ine (F := H.E) (N.plOm.1 w), orderOf (PadicInt.toZMod ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g0 : ℤ_[N.l i]ˣ) : ℤ_[N.l i])) = N.l i - 1 := by
  intro R H what₂ N i hram
  obtain ⟨w, hw⟩ := GlobalTheory.TameFixedLift.exists_place H.E (N.l i)
  refine ⟨w, hw, ?_⟩
  have : CharZero N.Om := charZero_of_injective_algebraMap (algebraMap H.E N.Om).injective
  have : IsAlgClosed N.Om := IsAlgClosure.isAlgClosed H.E
  have : IsScalarTower ℚ H.E N.Om := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  have : IsAlgClosure ℚ N.Om := IsAlgClosure.ofAlgebraic ℚ H.E N.Om
  have hA : (N.plOm.1 w).valuation (N.l i : N.Om) < 1 := by
    have := (N.plOm.2 w (N.l i : 𝓞 H.E)).2 hw
    simpa using this
  have := H.hostE_isGalois
  obtain ⟨v, hv⟩ := exists_unit_gen (N.l i)
  obtain ⟨σ, hσ, hσv⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective N.Om (N.l i) (N.plOm.1 w) hA v
  obtain ⟨g, hg, hc⟩ := GlobalTheory.TameFixedLift.transfer (E := H.E) (N.plOm.1 w) (N.l i) σ hσ
    (fix_of_unram (N.plOm.1 w) w (N.plOm.2 w) (hram w hw) σ hσ)
  exact ⟨g, hg, by rw [hc, hσv, hv]⟩

end GlobalTheory.CycGen
