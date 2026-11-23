import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceRead

theorem exists_extend_fractionRing {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]
    (hinj : Function.Injective (algebraMap A B)) (e : FractionRing A →+* ℂ) :
    ∃ ε : FractionRing B →+* ℂ, ε.comp (algebraMap A (FractionRing B)) = e.comp (algebraMap A (FractionRing A)) := by
  letI : Algebra A ℂ := (e.comp (algebraMap A (FractionRing A))).toAlgebra
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hinj
  haveI : FaithfulSMul A ℂ := (faithfulSMul_iff_algebraMap_injective A ℂ).2
    (e.injective.comp (IsFractionRing.injective A (FractionRing A)))
  haveI : FaithfulSMul A (FractionRing B) := (faithfulSMul_iff_algebraMap_injective A _).2 (by
    rw [IsScalarTower.algebraMap_eq A B (FractionRing B)]
    exact (IsFractionRing.injective B (FractionRing B)).comp hinj)
  haveI : Algebra.IsAlgebraic A B := inferInstance
  haveI : Algebra.IsAlgebraic B (FractionRing B) := IsLocalization.isAlgebraic _ (nonZeroDivisors B)
  haveI : Algebra.IsAlgebraic A (FractionRing B) := Algebra.IsAlgebraic.trans A B _
  let φ : FractionRing B →ₐ[A] ℂ := IsAlgClosed.lift
  exact ⟨φ.toRingHom, RingHom.ext fun a => φ.commutes a⟩

theorem exists_extends_and_emb : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw), ρ.Good → (∃ ε : KE c w →+* ℂ, Extends ρ ε) ∧
  (NChTie D c → ∀ ε : KE c w →+* ℂ, Extends ρ ε → ∀ x : D.LL0, ε (c.embW w (x : D.what₂.LL)) = embLL0 D x) := by
  intro D c w ρ hρ
  haveI := c.Oe_fin w
  refine ⟨exists_extend_fractionRing (c.Oe_inj w) (ρ.ek (c.twI w) (c.sd w) (c.k' w)), fun hT ε hε x => ?_⟩
  obtain ⟨y, z, hz, hyz⟩ := IsFractionRing.div_surjective (A := D.ntw.O0 (c.twI w))
    ((if c.sd w = true then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) x)
  have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
  have hz1 : algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) z ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hz
  have h0 : (if c.sd w = true then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) x * algebraMap _ _ z = algebraMap _ _ y := by
    rw [← hyz, div_mul_cancel₀ _ hz1]
  have h1 := congrArg ε (hT.embedding_baseField_condition w x y z hz0 h0)
  have key : ∀ t : D.ntw.O (c.twI w), ε (algebraMap (c.Oe w) (FractionRing (c.Oe w))
      (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w) (algebraMap _ (D.ntw.Ok (c.twI w) (c.k' w)) t))) =
      ρ.eO (c.twI w) (c.sd w) t := fun t => by
    rw [← IsScalarTower.algebraMap_apply (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w), hε.apply, hρ.ek_e]
  rw [map_mul, key, key] at h1
  rw [← hρ.e_LL0 (c.twI w) (c.sd w) x]
  let m : FractionRing (D.ntw.O0 (c.twI w)) →+* FractionRing (D.ntw.O (c.twI w)) := IsFractionRing.map (D.ntw.O_inj (c.twI w))
  have hm : ∀ t, ρ.e (c.twI w) (c.sd w) (m (algebraMap _ _ t)) =
      ρ.eO (c.twI w) (c.sd w) (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) t) := fun t =>
    congrArg (ρ.e (c.twI w) (c.sd w)) (IsLocalization.map_eq _ t)
  have h2 := congrArg (fun t => ρ.e (c.twI w) (c.sd w) (m t)) h0
  simp only [map_mul, hm] at h2
  have hne : ρ.eO (c.twI w) (c.sd w) (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) z) ≠ 0 := by
    rw [← hm]
    exact (map_ne_zero _).2 ((map_ne_zero m).2 hz1)
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

end GlobalTheory.PlaceRead
