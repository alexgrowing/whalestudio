import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalizeQuotientStages
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

noncomputable section

theorem length_self_eq_of_ringEquiv {A C : Type*} [CommRing A] [CommRing C] (e : A ≃+* C) :
    Module.length A A = Module.length C C := by
  have : RingHomSurjective (e : A →+* C) := ⟨e.surjective⟩
  let f : A →ₛₗ[(e : A →+* C)] C :=
    { toFun := e, map_add' := e.map_add, map_smul' := fun a b => by simp }
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f e.bijective)]

theorem LocalizeQuotientStages.proof : LocalizeQuotientStages.Statement.{u} := by
  intro R _ m W I _ _ hWm hIW P _ hP
  let Q := R ⧸ I
  let B := Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))
  let T := Localization.AtPrime W ⧸ I.map (algebraMap R (Localization.AtPrime W))

  have hdisj : Disjoint (m.primeCompl : Set R) (W : Set R) :=
    Set.disjoint_left.2 fun a ha hW => ha (hWm hW)
  have hPR : P.comap (algebraMap R B) = W := by
    rw [IsScalarTower.algebraMap_eq R (Localization.AtPrime m) B, ← Ideal.comap_comap,
      Ideal.Quotient.algebraMap_eq, ← hP,
      ← Ideal.map_map, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 (Ideal.map_mono hIW)]
    exact IsLocalization.under_map_of_isPrime_disjoint m.primeCompl _ ‹W.IsPrime› hdisj

  have hsub : (P.comap (algebraMap Q B)).primeCompl =
      Algebra.algebraMapSubmonoid Q W.primeCompl := by
    ext q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    have h1 : Ideal.Quotient.mk I r ∈ (P.comap (algebraMap Q B)).primeCompl ↔ r ∉ W := by
      rw [← hPR]; exact Iff.rfl
    rw [h1]
    constructor
    · intro hr; exact ⟨r, hr, rfl⟩
    · rintro ⟨r', hr', he⟩ hr
      apply hr'
      have : r' - r ∈ I := Ideal.Quotient.eq.1 he
      simpa using W.add_mem (hIW this) hr
  have hBP : IsLocalization (Algebra.algebraMapSubmonoid Q W.primeCompl)
      (Localization.AtPrime P) := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid Q m.primeCompl) (Localization.AtPrime P) P
    rw [IsLocalization.AtPrime, hsub] at this
    exact this
  let e := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid Q W.primeCompl)
    (Localization.AtPrime P) T
  exact (length_self_eq_of_ringEquiv (A := Localization.AtPrime P) (C := T) e.toRingEquiv).trans
    (Module.length_eq_of_surjective (R := T) (S := Localization.AtPrime W) (M := T)
      Ideal.Quotient.mk_surjective).symm

end

end GroundTheory.Heights₂.Heights
