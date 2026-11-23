import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.EigChar

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Z.J.D
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

private theorem norm_le_of_isIntegral {l : ℕ} [Fact l.Prime] {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (x : B →+* PadicAlgCl l) (h : ∀ a, ‖x (algebraMap A B a)‖ ≤ 1) {t : B} (ht : IsIntegral A t) : ‖x t‖ ≤ 1 := by
  obtain ⟨p, hm, hp⟩ := ht
  let S := integralClosure ℤ_[l] (PadicAlgCl l)
  let g : A →+* S := (x.comp (algebraMap A B)).codRestrict S.toSubring (fun a => by
    show IsIntegral ℤ_[l] (x (algebraMap A B a))
    exact (UpperTheory.V.Hi.Up.intIff _).2 (h a))
  have hint : IsIntegral S (x t) := by
    refine ⟨p.map g, hm.map g, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : (algebraMap S (PadicAlgCl l)).comp g = x.comp (algebraMap A B) := by
      ext a
      rfl
    rw [hc, ← Polynomial.hom_eval₂, hp, map_zero]
  exact (UpperTheory.V.Hi.Up.intIff _).1 (isIntegral_trans (R := ℤ_[l]) _ hint)

private theorem isIntegral_of_subalgebra {A Y : Type} [CommRing A] [AddCommGroup Y] [Module A Y] [Module.Finite A Y]
    (T : Subalgebra A (Module.End A Y)) (t : T) : IsIntegral A t := by
  have h : IsIntegral A (t : Module.End A Y) := by
    obtain ⟨p, hp, he⟩ := LinearMap.exists_monic_and_aeval_eq_zero A (t : Module.End A Y)
    exact ⟨p, hp, by rwa [← Polynomial.aeval_def]⟩
  exact (isIntegral_algHom_iff T.val Subtype.val_injective).1 h

private theorem norm_unit {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] (x : B →+* PadicAlgCl l) (u : Bˣ)
    (h : ∀ t, ‖x t‖ ≤ 1) : ‖x u‖ = 1 := by
  have e : ‖x u‖ * ‖x (u⁻¹ : Bˣ)‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  refine le_antisymm (h _) ?_
  calc (1 : ℝ) = ‖x u‖ * ‖x (u⁻¹ : Bˣ)‖ := e.symm
    _ ≤ ‖x u‖ * 1 := mul_le_mul_of_nonneg_left (h _) (norm_nonneg _)
    _ = ‖x u‖ := mul_one _

theorem UpperTheory.V.Z.J.D.unitEv :
    UnitEv := by
  intro L Ω _ _ _ _ _ l _ n c H hAx A _ _ _ θ _ ι K a _ _ I D ψ hU z v j
  obtain ⟨s, hs⟩ := GlobalTheory.LocLanglands.IsLocalArtin.surj (hAx.art_spec v)
    (UpperTheory.V.Hi.unif (IsDedekindDomain.HeightOneSpectrum.adicCompletion L (H.Sl v)))
  let g : Dec (H.pl v) := ⟨s, GlobalTheory.WeilDeligne.Weil_le_Dec (H.ovr v) s.2⟩
  rw [← hU.ψ_unif v j s g rfl hs]
  apply norm_unit z.toRingHom
  intro t
  refine norm_le_of_isIntegral (A := A) z.toRingHom ?_ (isIntegral_of_subalgebra _ t)
  intro a0
  let y : A →ₐ[c.O] PadicAlgCl l := z.comp (IsScalarTower.toAlgHom c.O A (H.TK θ a K))
  show ‖y a0‖ ≤ 1
  obtain ⟨b, hb⟩ := UpperTheory.V.Alg.IsCO.res_surj (O := c.O) a0
  have hm := UpperTheory.V.Hi.Up.normLt (l := l) (O := c.O) y _ hb
  have hi1 : IsIntegral ℤ_[l] (y (a0 - algebraMap c.O A b)) :=
    (UpperTheory.V.Hi.Up.intIff _).2 hm.le
  have hbi : IsIntegral ℤ_[l] b := by
    haveI := c.fin
    exact IsIntegral.of_finite ℤ_[l] b
  have hi2 : IsIntegral ℤ_[l] (y (algebraMap c.O A b)) := by
    rw [AlgHom.commutes]
    exact (isIntegral_algHom_iff c.O.val Subtype.val_injective).2 hbi
  have := hi1.add hi2
  rw [← map_add, sub_add_cancel] at this
  exact (UpperTheory.V.Hi.Up.intIff _).1 this
