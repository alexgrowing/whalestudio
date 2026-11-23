import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.GenPt

theorem mem_of_maximal {X : Scheme.{0}} [IsLocallyNoetherian X] (p : X)
    (hp : ∀ q : X, q ⤳ p → q = p) (O : Set X) (hO : IsOpen O) (hd : Dense O) : p ∈ O := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ p) isOpen_univ
  haveI := IsLocallyNoetherian.component_noetherian (X := X) ⟨V, hV⟩
  have hN0 := noetherianSpace_of_isAffineOpen V hV
  haveI : NoetherianSpace (V : Set X) := hN0
  haveI : QuasiSober (V : Set X) := V.isOpen.isOpenEmbedding_subtypeVal.quasiSober
  let p' : V := ⟨p, hpV⟩
  have hC := irreducibleComponent_mem_irreducibleComponents p'
  obtain ⟨o, ho, hne, hoC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hC
  have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
  have hgp : (hC.1.genericPoint).1 = p :=
    hp _ ((hg.specializes (mem_irreducibleComponent)).map continuous_subtype_val)
  obtain ⟨x, ⟨r, hro, rfl⟩, hxO⟩ := hd.inter_open_nonempty _ (V.isOpen.isOpenMap_subtype_val o ho)
    (hne.image _)
  have hpr : p ⤳ r.1 := hgp ▸ (hg.specializes (hoC hro)).map continuous_subtype_val
  exact hpr.mem_open hO hxO

theorem injective_of_flat {A R : Type} [CommRing A] [IsDomain A] [CommRing R] [IsDomain R]
    (φ : A →+* R) (hφ : φ.Flat) : Function.Injective φ := by
  letI := φ.toAlgebra
  haveI : Module.Flat A R := hφ
  rw [injective_iff_map_eq_zero]
  by_contra hne
  push_neg at hne
  obtain ⟨a, ha, ha0⟩ := hne
  have hlt : (⊥ : Ideal A) < (⊥ : Ideal R).under A := by
    refine lt_of_le_of_ne bot_le fun h => ha0 ?_
    have : a ∈ (⊥ : Ideal R).under A := by
      rw [Ideal.under, Ideal.mem_comap]; exact (Ideal.mem_bot).2 ha
    rw [← h] at this
    exact (Ideal.mem_bot).1 this
  obtain ⟨P, hP, -, hPo⟩ := Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt (p := ⊥) (⊥ : Ideal R) hlt
  have hPb : P = ⊥ := le_bot_iff.1 hP
  subst hPb
  exact hlt.ne (hPo.over)

end GlobalTheory.GenPt

theorem GlobalTheory.GenPt.generic_factors_dense : ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j], Dense (Set.range j) →
    (∀ x : X, IsDomain (X.presheaf.stalk x)) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X),
    (Scheme.stalkClosedPointTo ξ).hom.Flat → ∃ y : Sp (FractionRing R) ⟶ U, y ≫ j = jK R ≫ ξ := by
  intro X U _ j _ hd hdom R _ _ _ ξ hfl
  set z := ξ (closedPoint (CommRingCat.of R))
  haveI := hdom z
  have hinj := GlobalTheory.GenPt.injective_of_flat _ hfl
  have hξ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have hrange : Set.range (jK R ≫ ξ) ⊆ Set.range j := by
    rintro _ ⟨x0, rfl⟩
    set η := Spec.map (Scheme.stalkClosedPointTo ξ) (jK R x0) with hη
    have hη0 : η.asIdeal = ⊥ := by
      have h0 : x0.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ x0.asIdeal x0.isPrime
      change Ideal.comap _ (Ideal.comap _ x0.asIdeal) = ⊥
      rw [h0, CommRingCat.hom_ofHom, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R _),
        ← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot _).1 hinj
    have hp : (jK R ≫ ξ) x0 = X.fromSpecStalk z η := by
      rw [Scheme.Hom.comp_apply, ← hξ, Scheme.Hom.comp_apply]
    rw [hp]
    apply GlobalTheory.GenPt.mem_of_maximal _ _ _ j.isOpenEmbedding.isOpen_range hd
    intro q hq
    have hqz : q ∈ Set.range (X.fromSpecStalk z) := by
      rw [Scheme.range_fromSpecStalk]
      exact hq.trans (((IsLocalRing.specializes_closedPoint η).map (X.fromSpecStalk z).continuous).trans
        (specializes_of_eq Scheme.fromSpecStalk_closedPoint))
    obtain ⟨Q, rfl⟩ := hqz
    have hQ : Q ⤳ η := (IsPreimmersion.isEmbedding (X.fromSpecStalk z)).specializes_iff.1 hq
    have hQη : Q = η := PrimeSpectrum.ext (le_antisymm ((PrimeSpectrum.le_iff_specializes Q η).2 hQ)
      (hη0 ▸ bot_le))
    rw [hQη]
  exact ⟨IsOpenImmersion.lift j (jK R ≫ ξ) hrange, IsOpenImmersion.lift_fac _ _ _⟩
