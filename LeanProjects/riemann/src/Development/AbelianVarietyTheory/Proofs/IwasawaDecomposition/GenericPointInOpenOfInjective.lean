import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLinForms
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

noncomputable section

namespace GlobalTheory.GenericRange

theorem eq_of_specializes_generic {X : Scheme.{0}} (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ξ : Sp R ⟶ X) (hξ : Function.Injective (Scheme.stalkClosedPointTo ξ).hom) (p : Sp (FractionRing R))
    {z : X} (hz : z ⤳ (jK R ≫ ξ) p) : z = (jK R ≫ ξ) p := by
  have hfac : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk (ξ (closedPoint R)) = ξ :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  set q0 := (jK R ≫ Spec.map (Scheme.stalkClosedPointTo ξ)) p with hq0def
  have hq0 : q0.asIdeal = ⊥ := by
    ext a
    change a ∈ (PrimeSpectrum.comap (Scheme.stalkClosedPointTo ξ).hom
      (PrimeSpectrum.comap (CommRingCat.ofHom (algebraMap R (FractionRing R))).hom p)).asIdeal ↔ a ∈ (⊥ : Ideal _)
    have hp : p.asIdeal = ⊥ := @Ideal.eq_bot_of_prime (FractionRing R) _ p.asIdeal p.isPrime
    change (algebraMap R (FractionRing R)) ((Scheme.stalkClosedPointTo ξ).hom a) ∈ p.asIdeal ↔ a ∈ (⊥ : Ideal _)
    rw [hp, Ideal.mem_bot, Ideal.mem_bot]
    constructor
    · intro h
      apply hξ
      rw [map_zero]
      exact IsFractionRing.injective R (FractionRing R) (by simpa using h)
    · intro h
      simp [h]
  have hη : (jK R ≫ ξ) p = X.fromSpecStalk (ξ (closedPoint R)) q0 := by
    calc (jK R ≫ ξ) p = (jK R ≫ Spec.map (Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk (ξ (closedPoint R))) p := by
          rw [hfac]
      _ = _ := by simp only [q0, Scheme.Hom.comp_apply]
  have hηy : (jK R ≫ ξ) p ⤳ ξ (closedPoint R) := by
    rw [Scheme.Hom.comp_apply]
    exact (IsLocalRing.specializes_closedPoint _).map ξ.continuous
  obtain ⟨q, hq⟩ : z ∈ Set.range (X.fromSpecStalk (ξ (closedPoint R))) := by
    rw [Scheme.range_fromSpecStalk]; exact hz.trans hηy
  rw [hη, ← hq] at hz ⊢
  have h1 : q ⤳ q0 := (IsPreimmersion.isEmbedding (X.fromSpecStalk _)).isInducing.specializes_iff.1 hz
  have h2 : q.asIdeal ≤ q0.asIdeal := (PrimeSpectrum.le_iff_specializes q q0).2 h1
  rw [hq0, le_bot_iff, ← hq0] at h2
  rw [PrimeSpectrum.ext h2]

end GlobalTheory.GenericRange

namespace GlobalTheory.GenericRange

theorem mem_range_of_mem_closure {T X : Scheme.{0}} [IsNoetherian T] (f : T ⟶ X) {η : X}
    (hmax : ∀ z, z ⤳ η → z = η) (hη : η ∈ closure (Set.range f)) : η ∈ Set.range f := by
  have hfin : (irreducibleComponents T).Finite := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hsub : Set.range f ⊆ ⋃ C ∈ irreducibleComponents T, closure (f '' C) := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨C, hC, ht⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {t} isIrreducible_singleton
    exact Set.mem_biUnion hC (subset_closure ⟨t, ht rfl, rfl⟩)
  have hcl : IsClosed (⋃ C ∈ irreducibleComponents T, closure (f '' C)) :=
    hfin.isClosed_biUnion fun _ _ => isClosed_closure
  obtain ⟨C, hC, h⟩ := Set.mem_iUnion₂.1 (closure_minimal hsub hcl hη)
  have hirr : IsIrreducible C := hC.1
  have hg := hirr.isGenericPoint_genericPoint_closure
  rw [(isClosed_of_mem_irreducibleComponents C hC).closure_eq] at hg
  have him : f '' C ⊆ closure {f hirr.genericPoint} := by
    rintro _ ⟨t, ht, rfl⟩
    exact specializes_iff_mem_closure.1 ((hg.specializes ht).map f.continuous)
  have h' : η ∈ closure {f hirr.genericPoint} := closure_minimal him isClosed_closure h
  exact ⟨_, hmax _ (specializes_iff_mem_closure.2 h')⟩

end GlobalTheory.GenericRange

namespace GlobalTheory.GenericRange

theorem range_jK_comp_subset : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ξ : Sp R ⟶ Z.X), Function.Injective (Scheme.stalkClosedPointTo ξ).hom →
      Set.range (jK R ≫ ξ) ⊆ Set.range Z.j := by
  intro E _ _ _ H D l Xo c Z R _ _ _ ξ hξ
  rintro _ ⟨p, rfl⟩
  have hmax : ∀ z, z ⤳ (jK R ≫ ξ) p → z = (jK R ≫ ξ) p := fun z hz => eq_of_specializes_generic R ξ hξ p hz
  set η := (jK R ≫ ξ) p with hηdef
  let pt : Sp c.F := IsLocalRing.closedPoint c.F
  have hg : spMap (algebraMap (𝓞 c.F) c.F) pt ⤳ Z.s η := by
    refine (PrimeSpectrum.le_iff_specializes (R := 𝓞 c.F) _ _).1 ((PrimeSpectrum.asIdeal_le_asIdeal _ _).1 ?_)
    intro a ha
    change algebraMap (𝓞 c.F) c.F a ∈ IsLocalRing.maximalIdeal c.F at ha
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at ha
    have : a = 0 := FaithfulSMul.algebraMap_injective (𝓞 c.F) c.F (ha.trans (map_zero _).symm)
    rw [this]
    exact Ideal.zero_mem _
  have := Z.flat
  obtain ⟨η', hη', hs'⟩ := Flat.generalizingMap Z.s hg
  rw [hmax η' hη'] at hs'
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Z.s) (g := spMap (algebraMap (𝓞 c.F) c.F)) η pt hs'
  have hcl : η ∈ closure (Set.range Z.j) := by
    rw [← hw]
    refine map_mem_closure (pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F))).continuous
      (Z.jQ_dense.closure_eq ▸ Set.mem_univ w) ?_
    rintro _ ⟨v, rfl⟩
    exact ⟨v, rfl⟩
  have : IsNoetherian (Xo.XF c) := Formalism.L2.Pj.CompFin.isNoetherian_XF Xo c
  exact mem_range_of_mem_closure Z.j hmax hcl

end GlobalTheory.GenericRange
