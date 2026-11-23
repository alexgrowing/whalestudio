import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LocalComponentsSurjective
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PropZ
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.CurveInFibre

theorem valAt_inv {X : Scheme.{0}} {Ω K : Type} [Field Ω] [Field K] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {η : Spec (CommRingCat.of K) ⟶ X} {a : Ω} {r : K} (h : ValAt ξ η a r) (hr : r ≠ 0) :
    ValAt ξ η a⁻¹ r⁻¹ := by
  obtain ⟨hz, s, rfl, rfl⟩ := h
  have hl := Scheme.isLocalHom_stalkClosedPointTo η
  have hs : IsUnit s := hl.map_nonunit s (IsUnit.mk0 _ hr)
  obtain ⟨u, rfl⟩ := hs
  refine ⟨hz, ↑u⁻¹, ?_, ?_⟩
  · exact map_units_inv _ u
  · exact map_units_inv _ u

theorem finite_not_integral {K O A : Type} [Field K] [CommRing O] [CommRing A] (C : Crv.ACurve K) (g : O →+* A)
    (hg : g.FiniteType) (φ : A →+* K) (hO : ∀ i a, φ (g a) ∈ (C.v i).valuationSubring) :
    {i | ¬ ∀ a, φ a ∈ (C.v i).valuationSubring}.Finite := by
  letI := g.toAlgebra
  obtain ⟨t, ht⟩ := (show Algebra.FiniteType O A from hg).out
  have hfin : ∀ a : A, {i | φ a ∉ (C.v i).valuationSubring}.Finite := by
    intro a
    by_cases h0 : φ a = 0
    · simp [h0]
    · exact (C.fin _ h0).subset fun i hi h1 => hi (le_of_eq h1)
  refine (t.finite_toSet.biUnion fun a _ => hfin a).subset fun i hi => ?_
  by_contra hc
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not] at hc
  refine hi fun a => ?_
  have ha : a ∈ Algebra.adjoin O (t : Set A) := ht ▸ Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem y hy => exact hc y hy
  | algebraMap r => exact hO i r
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

theorem ae_centre {X : Scheme.{0}} {K O : Type} [Field K] [CommRing O] (s : X ⟶ Spec (CommRingCat.of O))
    [IsSeparated s] [LocallyOfFiniteType s] (C : Crv.ACurve K) (η : Spec (CommRingCat.of K) ⟶ X)
    (z : ∀ i, Spec (CommRingCat.of (C.v i).valuationSubring) ⟶ X)
    (hz : ∀ i, Spec.map (CommRingCat.ofHom (C.v i).valuationSubring.subtype) ≫ z i = η)
    (U : X.Opens) (hU : centre η ∈ U) : {i | centre (z i) ∉ U}.Finite := by
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hU
  have hV : IsAffineOpen V := hV
  have hr : Set.range η ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    have : p = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]
    exact hxV
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hV.fromSpec η hr)
  have hφ' : Spec.map φ ≫ hV.fromSpec = η := by rw [hφ, IsOpenImmersion.lift_fac]
  obtain ⟨g, hg⟩ := Spec.map_surjective (hV.fromSpec ≫ s)
  have hgf : g.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 (hg ▸ inferInstance)
  choose ψ hψ using fun i => Spec.map_surjective (z i ≫ s)
  have hsq : ∀ i, ψ i ≫ CommRingCat.ofHom (C.v i).valuationSubring.subtype = g ≫ φ := fun i => by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hψ, hg, ← Category.assoc, ← Category.assoc, hz, hφ']
  have hsq' : ∀ i a, φ.hom (g.hom a) = ((ψ i).hom a : K) := fun i a =>
    (congrArg (fun f => f.hom a) (hsq i)).symm
  refine (finite_not_integral C g.hom hgf φ.hom fun i a => ?_).subset fun i hi hc => hi ?_
  · rw [hsq' i a]
    exact ((ψ i).hom a).2
  · let χ : Γ(X, V) ⟶ CommRingCat.of (C.v i).valuationSubring :=
      CommRingCat.ofHom (φ.hom.codRestrict (C.v i).valuationSubring hc)
    haveI : IsDominant (Spec.map (CommRingCat.ofHom (C.v i).valuationSubring.subtype)) :=
      ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (C.v i).valuationSubring.subtype).2 (by
        rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]
        exact bot_le)⟩
    have e : z i = Spec.map χ ≫ hV.fromSpec := by
      refine ext_of_isDominant_of_isSeparated s ?_
        (Spec.map (CommRingCat.ofHom (C.v i).valuationSubring.subtype)) ?_
      · rw [Category.assoc, ← hg, ← hψ, ← Spec.map_comp]
        congr 1
        ext a
        exact (hsq' i a).symm
      · rw [hz, ← Category.assoc, ← Spec.map_comp, ← hφ']
        rfl
    refine hVU ?_
    change centre (z i) ∈ (V : Set X)
    rw [e, ← hV.range_fromSpec]
    exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩

end PositivityTheory.Xgn.CurveInFibre

theorem PositivityTheory.Xgn.exists_curve_in_fibre_degree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] (s : X ⟶ Spec (CommRingCat.of O)) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : Ω) (Γ : FibreCurve ξ ϖ), IsCptGen ξ → ∃ Y : Crv.CurveIn Γ.C Γ.η, Y.x = Γ.z ∧ ∀ (L : Lat ξ Ω) (n : ℤ), L.IsVB 1 ⊤ → (Γ.HasDeg L n ↔ Y.IsDeg L n) := by
  intro X Ω _ ξ O _ s _ _ ϖ Γ _
  refine ⟨⟨Γ.z, Γ.z_gen, PositivityTheory.Xgn.CurveInFibre.ae_centre s Γ.C Γ.η Γ.z Γ.z_gen⟩, rfl, fun L n _ => ⟨?_, ?_⟩⟩
  · rintro ⟨e, f, r, he, hf, hr, hfin, hd⟩
    refine ⟨Γ.η_spec, Γ.z_spec, e, f, fun i => (r i)⁻¹, he, fun i => (hf i).2, fun i => ⟨inv_ne_zero (hr i).1, ?_⟩,
      ?_, ?_⟩
    · rw [← inv_div]
      exact PositivityTheory.Xgn.CurveInFibre.valAt_inv (hr i).2 (hr i).1
    · simpa using hfin
    · rw [← hd]
      simp
  · rintro ⟨h₀, h, e, f, r, he, hf, hr, hfin, hd⟩
    refine ⟨e, f, fun i => (r i)⁻¹, he, fun i => ⟨h i, hf i⟩, fun i => ⟨inv_ne_zero (hr i).1, ?_⟩, ?_, ?_⟩
    · rw [← inv_div]
      exact PositivityTheory.Xgn.CurveInFibre.valAt_inv (hr i).2 (hr i).1
    · simpa using hfin
    · rw [hd]
      simp
