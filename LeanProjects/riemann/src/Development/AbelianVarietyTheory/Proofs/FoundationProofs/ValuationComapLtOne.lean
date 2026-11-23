import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerCrystallineCocycles

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

namespace GlobalTheory.AntiRam

section General

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem valuation_comap_lt_one (c : Ω ≃+* Ω) (A : ValuationSubring Ω) (y : Ω) :
    (A.comap c.symm.toRingHom).valuation y < 1 ↔ A.valuation (c.symm y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ValuationSubring.mem_comap,
    ValuationSubring.mem_comap, ← map_inv₀, map_eq_zero_iff _ c.symm.injective]
  rfl

theorem exists_conj_mem_Ine (c : Ω ≃+* Ω) (κ : E → E)
    (hc : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (κ x)) (hκ : ∀ x, κ (κ x) = x)
    (A : ValuationSubring Ω) (σ : G E Ω) (hσ : σ ∈ Ine (F := E) A) :
    ∃ σ' : G E Ω, (∀ x, σ' x = c (σ (c.symm x))) ∧ σ' ∈ Ine (F := E) (A.comap c.symm.toRingHom) := by
  have hs : ∀ x, c.symm (algebraMap E Ω x) = algebraMap E Ω (κ x) := fun x => by
    rw [RingEquiv.symm_apply_eq, hc, hκ]
  let σ' : Ω ≃ₐ[E] Ω := AlgEquiv.ofRingEquiv (f := (c.symm.trans (σ : Ω ≃ₐ[E] Ω).toRingEquiv).trans c)
    (fun x => by
      show c (σ (c.symm (algebraMap E Ω x))) = _
      rw [hs, AlgEquiv.commutes, hc, hκ])
  have h' : ∀ x, σ' x = c (σ (c.symm x)) := fun _ => rfl
  have hm : ∀ y, y ∈ A.comap c.symm.toRingHom ↔ c.symm y ∈ A := fun _ => Iff.rfl
  refine ⟨σ', h', ?_, fun x hx => ?_⟩
  · change σ' ∈ Dec (F := E) _
    rw [mem_Dec]
    ext y
    obtain ⟨z, rfl⟩ := σ'.surjective y
    rw [← AlgEquiv.smul_def σ' z, ValuationSubring.smul_mem_pointwise_smul_iff, AlgEquiv.smul_def,
      hm, hm, h', RingEquiv.symm_apply_apply, apply_mem_iff_of_mem_Dec hσ.1]
  · rw [valuation_comap_lt_one, map_sub, h', RingEquiv.symm_apply_apply]
    refine hσ.2 _ ?_
    rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
    exact (hm x).1 hx

end General

theorem ramExactly_conj : ∀ (D : D7) (M : Type) [CommGroup M] (ψ : G D.host.E D.nd.Om →* M) (Q : Set (PlE D.host)), AntiHom D.ntw.cc ψ → RamExactly ψ Q → ∀ P ∈ Q, ∀ P' : PlE D.host, IsConjPl D.host P P' → P' ∈ Q := by
  intro D M _ ψ Q hA hR P hP P' hPP
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x :=
    bridge_star_holds D.R D.host
  obtain ⟨⟨j, hj⟩, -⟩ := D.ntw.cc_cm
  have hκ : ∀ x, D.host.conj (D.host.conj x) = x := fun x => by
    rw [← hst, ← hst, IsCMField.complexConj_apply_apply]
  have hc : ∀ x, D.ntw.cc (algebraMap D.host.E D.nd.Om x) =
      algebraMap D.host.E D.nd.Om (D.host.conj x) := fun x => by
    apply j.injective
    rw [hj, ← hst]
    exact (IsCMField.complexEmbedding_complexConj D.host.E
      (j.comp (algebraMap D.host.E D.nd.Om)) x).symm
  have hs : ∀ x, D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) =
      algebraMap D.host.E D.nd.Om (D.host.conj x) := fun x => by
    rw [RingEquiv.symm_apply_eq, hc, hκ]
  have hpl : IsPlaceOver (D.nd.plOm.1 P) P := D.nd.plOm.2 P
  obtain ⟨σ, hσ, hne⟩ := (hR P _ hpl).2 hP
  obtain ⟨σ', h1, h2⟩ := exists_conj_mem_Ine D.ntw.cc (fun x => D.host.conj x) hc hκ _ σ hσ
  refine (hR P' _ (fun y => ?_)).1 ⟨σ', h2, ?_⟩
  · have hint : IsIntegral ℤ (D.host.conj (y : D.host.E)) := by
      rw [← hst]
      exact (RingOfIntegers.isIntegral_coe y).map
        ((IsCMField.complexConj D.host.E).toRingEquiv.toRingHom.toIntAlgHom)
    rw [valuation_comap_lt_one, hs, ← hPP ⟨_, hint⟩ y (hκ _).symm]
    exact hpl ⟨_, hint⟩
  · rw [hA σ σ' h1]
    exact inv_ne_one.2 hne

end GlobalTheory.AntiRam
