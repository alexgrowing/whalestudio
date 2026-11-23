import Mathlib
import GroundTheory.LocalFields.NormCorrespondence
import GroundTheory.LocalFields.OpenCompletion

noncomputable section

namespace GroundTheory.LocalField

open Abstract ValuativeRel

section Restrict

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]

theorem restrictAb_eq_of_le {E E' : IntermediateField F Ω} [Normal F E] [Normal F E']
    (hE' : E' ≤ maximalAbelianExtension F Ω) (hEE' : E ≤ E')
    {σ τ : maximalAbelianExtension F Ω ≃ₐ[F] maximalAbelianExtension F Ω}
    (h : restrictAb E' hE' σ = restrictAb E' hE' τ) :
    restrictAb E (hEE'.trans hE') σ = restrictAb E (hEE'.trans hE') τ := by
  ext y
  have := congrArg (fun ρ : E' ≃ₐ[F] E' => ((ρ ⟨y, hEE' y.2⟩ : E') : Ω)) h
  simp only [restrictAb_apply] at this ⊢
  exact this

end Restrict

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section ClassField

variable (K Ω) in

def classField (H : openFiniteIndex Kˣ) : finiteAbelianExtensions K Ω :=
  (normGroupOrderIso K Ω).symm (OrderDual.toDual ⟨H.1, H.2⟩)

theorem range_normUnits_classField (H : openFiniteIndex Kˣ) :
    (normUnits K (classField K Ω H : IntermediateField K Ω)).range = H.1 :=
  congrArg (fun y => (OrderDual.ofDual y).1)
    ((normGroupOrderIso K Ω).apply_symm_apply (OrderDual.toDual ⟨H.1, H.2⟩))

theorem classField_anti {H H' : openFiniteIndex Kˣ} (h : H.1 ≤ H'.1) :
    (classField K Ω H' : IntermediateField K Ω) ≤ classField K Ω H := by
  have := (classField K Ω H).2.1
  have := (classField K Ω H).2.2
  have := (classField K Ω H').2.1
  have := (classField K Ω H').2.2
  rw [← range_normUnits_le_iff, range_normUnits_classField, range_normUnits_classField]
  exact h

theorem le_classField (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L] :
    L ≤ classField K Ω ⟨(normUnits K L).range, isOpen_range_normUnits_and_finiteIndex (Ω := Ω) L⟩ := by
  have := (classField K Ω ⟨(normUnits K L).range, isOpen_range_normUnits_and_finiteIndex (Ω := Ω) L⟩).2.1
  have := (classField K Ω ⟨(normUnits K L).range, isOpen_range_normUnits_and_finiteIndex (Ω := Ω) L⟩).2.2
  rw [← range_normUnits_le_iff, range_normUnits_classField]

end ClassField

section Coord

variable (K Ω) in

def artinCoord (H : openFiniteIndex Kˣ) :
    (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) →* Kˣ ⧸ H.1 :=
  have := (classField K Ω H).2.1
  have := (classField K Ω H).2.2
  (QuotientGroup.quotientMulEquivOfEq (range_normUnits_classField H)).toMonoidHom.comp
    ((localReciprocityAbelian (classField K Ω H : IntermediateField K Ω)).toMonoidHom.comp
      (restrictAb _ (le_maximalAbelianExtension _)))

theorem artinCoord_eq_of (H : openFiniteIndex Kˣ)
    (σ : maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) (x : Kˣ)
    (h : have := (classField K Ω H).2.1; have := (classField K Ω H).2.2
      restrictAb (classField K Ω H : IntermediateField K Ω) (le_maximalAbelianExtension _) σ =
        restrictAb _ (le_maximalAbelianExtension _) (localArtinMap K Ω x)) :
    artinCoord K Ω H σ = (x : Kˣ ⧸ H.1) := by
  have := (classField K Ω H).2.1
  have := (classField K Ω H).2.2
  simp only [artinCoord, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [h, restrictAb_localArtinMap, MulEquiv.apply_symm_apply, QuotientGroup.quotientMulEquivOfEq_mk]

theorem artinCoord_localArtinMap (H : openFiniteIndex Kˣ) (x : Kˣ) :
    artinCoord K Ω H (localArtinMap K Ω x) = (x : Kˣ ⧸ H.1) :=
  artinCoord_eq_of H _ x rfl

theorem exists_artinCoord_eq (H H' : openFiniteIndex Kˣ) (h : H.1 ≤ H'.1)
    (σ : maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) :
    ∃ x : Kˣ, artinCoord K Ω H σ = (x : Kˣ ⧸ H.1) ∧ artinCoord K Ω H' σ = (x : Kˣ ⧸ H'.1) := by
  have := (classField K Ω H).2.1
  have := (classField K Ω H).2.2
  have := (classField K Ω H').2.1
  have := (classField K Ω H').2.2
  obtain ⟨x, hx⟩ := surjective_restrictAb_localArtinMap (Ω := Ω) (classField K Ω H : IntermediateField K Ω)
    (restrictAb _ (le_maximalAbelianExtension _) σ)
  refine ⟨x, artinCoord_eq_of H σ x hx.symm, artinCoord_eq_of H' σ x ?_⟩
  exact restrictAb_eq_of_le (le_maximalAbelianExtension _) (classField_anti h) hx.symm

theorem continuous_artinCoord (H : openFiniteIndex Kˣ) : Continuous (artinCoord K Ω H) := by
  have := (classField K Ω H).2.1
  have := (classField K Ω H).2.2
  change Continuous ((fun ρ => (QuotientGroup.quotientMulEquivOfEq (range_normUnits_classField H))
    (localReciprocityAbelian (classField K Ω H : IntermediateField K Ω) ρ)) ∘
      restrictAb _ (le_maximalAbelianExtension _))
  exact continuous_of_discreteTopology.comp (continuous_restrictAb _ _)

end Coord

section Completion

variable (K Ω) in

def galToOpenCompletion :
    (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) →* openCompletion Kˣ :=
  MonoidHom.codRestrict (MonoidHom.pi fun H => artinCoord K Ω H) (openCompletion Kˣ) fun σ H H' h => by
    obtain ⟨x, hx, hx'⟩ := exists_artinCoord_eq H H' h σ
    change quotientMapOfLE h (artinCoord K Ω H σ) = artinCoord K Ω H' σ
    rw [hx, hx', quotientMapOfLE_mk]

theorem galToOpenCompletion_apply (σ : maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω)
    (H : openFiniteIndex Kˣ) :
    ((galToOpenCompletion K Ω σ : openCompletion Kˣ) : ∀ H : openFiniteIndex Kˣ, Kˣ ⧸ H.1) H =
      artinCoord K Ω H σ :=
  rfl

theorem galToOpenCompletion_localArtinMap (x : Kˣ) :
    galToOpenCompletion K Ω (localArtinMap K Ω x) = openCompletion.of Kˣ x :=
  openCompletion.ext fun H => artinCoord_localArtinMap H x

theorem continuous_galToOpenCompletion : Continuous (galToOpenCompletion K Ω) :=
  Continuous.subtype_mk (continuous_pi fun H => continuous_artinCoord H) _

theorem injective_galToOpenCompletion : Function.Injective (galToOpenCompletion K Ω) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  refine ext_restrictAb fun L _ _ => ?_
  set H : openFiniteIndex Kˣ := ⟨(normUnits K L).range, isOpen_range_normUnits_and_finiteIndex (Ω := Ω) L⟩
  have := (classField K Ω H).2.1
  have := (classField K Ω H).2.2
  have hH : artinCoord K Ω H σ = 1 := by
    rw [← galToOpenCompletion_apply, hσ]
    rfl
  have h1 : restrictAb (classField K Ω H : IntermediateField K Ω) (le_maximalAbelianExtension _) σ =
      restrictAb (classField K Ω H : IntermediateField K Ω) (le_maximalAbelianExtension _) 1 := by
    rw [map_one]
    simpa [artinCoord] using hH
  exact restrictAb_eq_of_le (le_maximalAbelianExtension _) (le_classField L) h1

theorem surjective_galToOpenCompletion : Function.Surjective (galToOpenCompletion K Ω) := by
  have hc : IsClosed (Set.range (galToOpenCompletion K Ω)) :=
    (isCompact_range continuous_galToOpenCompletion).isClosed
  have hsub : Set.range (openCompletion.of Kˣ) ⊆ Set.range (galToOpenCompletion K Ω) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨_, galToOpenCompletion_localArtinMap x⟩
  have := (openCompletion.denseRange_of (G := Kˣ)).closure_range
  intro a
  have ha : a ∈ closure (Set.range (openCompletion.of Kˣ)) := by rw [this]; trivial
  exact hc.closure_subset_iff.2 hsub ha

variable (K Ω) in

def localArtinCompletion :
    openCompletion Kˣ ≃ₜ* (maximalAbelianExtension K Ω ≃ₐ[K] maximalAbelianExtension K Ω) :=
  let e := MulEquiv.ofBijective (galToOpenCompletion K Ω)
    ⟨injective_galToOpenCompletion, surjective_galToOpenCompletion⟩
  ContinuousMulEquiv.symm
    { e with
      continuous_toFun := continuous_galToOpenCompletion
      continuous_invFun :=
        (continuous_galToOpenCompletion.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

end Completion

end GroundTheory.LocalField
