import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.CdvrExt

theorem injective_of_flat_local {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
    (φ : A →+* R) (hφ : φ.Flat) [IsLocalHom φ] : Function.Injective φ := by
  letI := φ.toAlgebra
  haveI : Module.Flat A R := hφ
  haveI : IsLocalHom (algebraMap A R) := ‹_›
  haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := A) (B := R)
  rw [injective_iff_map_eq_zero]
  intro a ha
  have h := Ideal.comap_map_eq_self_of_faithfullyFlat (A := A) (B := R) ⊥
  rw [Ideal.map_bot] at h
  have : a ∈ Ideal.comap (algebraMap A R) ⊥ := by rw [Ideal.mem_comap, Ideal.mem_bot]; exact ha
  rw [h] at this
  simpa using this

theorem isLocalHom_of_map_maximalIdeal {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
    (φ : A →+* R) (h : (maximalIdeal A).map φ = maximalIdeal R) : IsLocalHom φ := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have : φ a ∈ maximalIdeal R := h ▸ Ideal.mem_map_of_mem φ ((mem_maximalIdeal a).2 hna)
  exact (mem_maximalIdeal _).1 this ha

theorem isDVR_of_ringKrullDim_eq_one {A : Type} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (hA : ringKrullDim A = 1) : IsDiscreteValuationRing A := by
  obtain ⟨hf, hrad⟩ := ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.1 hA
  have key := (IsDiscreteValuationRing.TFAE A hf).out 0 3
  try simp only [List.length_cons, List.getElem_cons_succ, List.getElem_cons_zero] at key
  refine key.2 ⟨inferInstance, maximalIdeal A, ⟨?_, ?_⟩, ?_⟩
  · exact (isField_iff_maximalIdeal_eq).not.1 hf
  · exact (maximalIdeal.isMaximal A).isPrime
  · rintro P ⟨hP, hPp⟩
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    refine le_antisymm (le_maximalIdeal hPp.ne_top) ?_
    refine (hrad x hx0).trans ?_
    rw [hPp.radical_le_iff, Ideal.span_singleton_le_iff_mem]
    exact hxP

theorem cdvr_of_isEtaleCompletion : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [CommRing R] [IsDomain R] [IsLocalRing R] (φ : A →+* R), ringKrullDim A = 1 →
    IsEtaleCompletion φ → IsCN R → CDvr R := by
  intro A R _ _ _ _ _ _ _ _ φ hA hφ hR
  obtain ⟨hfl, hm, -⟩ := hφ
  obtain ⟨hRn, -, hRc, hR0⟩ := hR
  haveI := hRn
  haveI := isLocalHom_of_map_maximalIdeal φ hm
  have hinj := injective_of_flat_local φ hfl
  haveI := isDVR_of_ringKrullDim_eq_one hA
  have hAf : ¬IsField A := (isField_iff_maximalIdeal_eq).not.2 (IsDiscreteValuationRing.not_a_field A)
  have keyA := (IsDiscreteValuationRing.TFAE A hAf).out 0 4
  try simp only [List.length_cons, List.getElem_cons_succ, List.getElem_cons_zero] at keyA
  obtain ⟨π, hπ⟩ := (keyA.1 inferInstance).principal
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact IsDiscreteValuationRing.not_a_field A (by rw [hπ]; simp)
  have hmR : maximalIdeal R = Ideal.span {φ π} := by
    rw [← hm, hπ]
    show Ideal.map φ (Ideal.span {π}) = _
    rw [Ideal.map_span, Set.image_singleton]
  have hnf : ¬IsField R := by
    rw [isField_iff_maximalIdeal_eq, hmR, Ideal.span_singleton_eq_bot]
    exact (map_ne_zero_iff φ hinj).2 hπ0
  refine ⟨?_, hRc, hR0⟩
  have keyR := (IsDiscreteValuationRing.TFAE R hnf).out 0 4
  try simp only [List.length_cons, List.getElem_cons_succ, List.getElem_cons_zero] at keyR
  exact keyR.2 ⟨⟨φ π, by rw [hmR]⟩⟩

end GlobalTheory.CdvrExt
