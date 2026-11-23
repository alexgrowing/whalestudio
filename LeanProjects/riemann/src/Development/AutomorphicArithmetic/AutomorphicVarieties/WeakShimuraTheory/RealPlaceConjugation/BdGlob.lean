import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.StrResidueLeCocyclesVanishingOnInertiaKernel
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.Strict
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.CardGlobalCocyclesLeOfIwasawaRank
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.EvenRt
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.KrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.RankCard

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem isLocalHom_algebraMap_padicInt_coef_O {l : ℕ} [Fact l.Prime] (c : Coef l) :
    IsLocalHom (algebraMap ℤ_[l] c.O) := by
  haveI := c.fin
  apply RingHom.IsIntegral.isLocalHom
  · exact (Algebra.IsIntegral.of_finite ℤ_[l] c.O).isIntegral
  · intro a b h
    have h' := congrArg (fun x : c.O => (x : PadicAlgCl l)) h
    simp only [Subalgebra.coe_algebraMap] at h'
    have hinj : Function.Injective (algebraMap ℤ_[l] (PadicAlgCl l)) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l)]
      exact (algebraMap ℚ_[l] (PadicAlgCl l)).injective.comp (fun a b h => Subtype.ext h)
    exact hinj h'

private theorem finite_residueField_coef {l : ℕ} [Fact l.Prime] (c : Coef l) :
    Finite (ResidueField c.O) := by
  haveI := c.fin
  haveI := isLocalHom_algebraMap_padicInt_coef_O c
  exact IsLocalRing.ResidueField.finite_of_finite (R := ℤ_[l]) inferInstance

private theorem prime_nsmul_residueField_coef_eq_zero {l : ℕ} [Fact l.Prime] (c : Coef l) (m : ResidueField c.O) :
    l • m = 0 := by
  haveI := isLocalHom_algebraMap_padicInt_coef_O c
  have h0 : IsLocalRing.residue c.O (algebraMap ℤ_[l] c.O (l : ℤ_[l])) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).2
      (fun hu => PadicInt.p_nonunit (isUnit_of_map_unit (algebraMap ℤ_[l] c.O) _ hu))
  have h1 : ((l : ResidueField c.O)) = 0 := by
    rw [map_natCast] at h0
    rw [← map_natCast (IsLocalRing.residue c.O)]
    exact h0
  rw [nsmul_eq_mul, h1, zero_mul]

theorem UpperTheory.V.Ws.rank_cocycleSpaces_le_of_towerIwasawaRank :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (T : Tower D) (r g : ℕ), (plDvd T.F (prodS D)).ncard ≤ g → XRk l 1 T.Kr r → (∀ w, Module.rank (ResidueField c.O) ((T.fr ∅).Str (residue c.O) w) ≤ (r + 1 : ℕ)) ∧ (∀ w ∈ [0, wPs, -wPs], Module.rank (ResidueField c.O) ((T.fr ∅).Zgl (residue c.O) w) ≤ (r + 2 + g : ℕ)) ∧ ∀ w, Module.rank (ResidueField c.O) ((T.fr ∅).Zgl (residue c.O) w) ≤ T.d + (r + 2 + g : ℕ) := by
  intro hP Ω _ _ _ l _ c D hD T r g hg hX
  obtain ⟨hN, hO, hI, hC, hK, hU, ⟨hS0, hSl⟩, hIne, -⟩ := residualKernel_properties D hD T
  haveI := finite_residueField_coef c
  have tor := prime_nsmul_residueField_coef_eq_zero c
  have triv : ∀ (w : ℤ × ℤ), ∀ σ ∈ T.Kr, ∀ m : ResidueField c.O, (charRep (T.rbU w)) σ m = m := by
    intro w σ hσ m
    simp [charRep, hU w σ (hK σ hσ)]
  have hinf : ∀ (w : ℤ × ℤ), ∀ σ ∈ ineOff (↥T.F) Ω (prodS D), ∀ m : ResidueField c.O,
      (charRep (T.rbU w)) σ m = m := by
    intro w σ hσ m
    simp [charRep, hU w σ (hIne σ hσ).2]
  have sub : ∀ (w : ℤ × ℤ), (T.fr ∅).Zgl (residue c.O) w ≤
      cocOff (charRep (T.rbU w)) (ineOff (↥T.F) Ω (prodS D)) := by
    intro w z hz
    obtain ⟨h1, h2, h3, -⟩ := hz
    refine ⟨h1, ?_, ?_⟩
    · intro a b
      rw [h2 a b]
      simp [charRep, Tower.rbU]
    · intro a ha
      exact h3 a (hIne a ha).1
  refine ⟨?_, ?_, ?_⟩
  · intro w
    have h := card_cocycles_vanishing_on_inertia_le_pow T.F Ω l (ResidueField c.O) (ResidueField c.O) tor (charRep (T.rbU w)) T.Kr r hI
      (triv w) hX
    refine le_trans (Submodule.rank_mono (str_residue_le_cocycles_vanishing_on_inertia_kernel D hD T w)) ?_
    haveI := h.1
    exact rank_le_of_card_le_pow_card_field _ _ _ h
  · intro w hw
    have h := (card_globalCocycles_le_of_iwasawaRank hP T.F Ω l _ _ tor (charRep (T.rbU w)) T.Kr (prodS D) r g hD.l_odd hS0 hSl hg
      (hinf w) hN hO hI (triv w) hC hX).2 T.realF
      (fun σ hσ m => by simp [charRep, residualCharacter_complexConjugation_eq_one D hD T σ hσ w hw])
    refine le_trans (Submodule.rank_mono (sub w)) ?_
    haveI := h.1
    exact rank_le_of_card_le_pow_card_field _ _ _ h
  · intro w
    have h := (card_globalCocycles_le_of_iwasawaRank hP T.F Ω l _ _ tor (charRep (T.rbU w)) T.Kr (prodS D) r g hD.l_odd hS0 hSl hg
      (hinf w) hN hO hI (triv w) hC hX).1
    refine le_trans (Submodule.rank_mono (sub w)) ?_
    haveI := h.1
    have h2 := rank_le_of_card_le_pow_card_field _ _ _ h
    refine le_trans h2 (le_of_eq ?_)
    simp only [Tower.d]
    push_cast
    ring
