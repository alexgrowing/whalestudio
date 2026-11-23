import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsAffineOpenPreimageEqOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecPullSurjectiveAndKer

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys.OfLift

theorem sec_smooth {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [Smooth s] (U : X.affineOpens) :
    Algebra.Smooth R (Sec s U.1) := by
  have h := HasRingHomProperty.appLE @Smooth s ‹_› ⟨⊤, isAffineOpen_top _⟩ U le_top
  have h' : RingHom.Smooth ((s.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :=
    RingHom.Smooth.comp (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective) h
  exact RingHom.smooth_algebraMap.mp h'

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}
  {X₀ X : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s : X ⟶ Sp R} {i : X₀ ⟶ X}

theorem surjective_spMap (hI : I ^ 2 = 0) (hk : RingHom.ker π = I) (hπ : Function.Surjective π) :
    Surjective (spMap π) := by
  constructor
  intro x
  have hx : (show PrimeSpectrum R from x) ∈ Set.range (PrimeSpectrum.comap π) := by
    refine (range_comap_of_surjective R₀ π hπ).ge ?_
    rw [hk]
    intro a ha
    have h2 : a ^ 2 = 0 := by
      have := Ideal.pow_mem_pow ha 2
      rwa [hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact (show PrimeSpectrum R from x).2.mem_of_pow_mem 2 (by rw [h2]; exact zero_mem _)
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, hy⟩

variable (hpb : IsPullback i s₀ s (spMap π)) (hπ : Function.Surjective π) (hn : IsNilpotent (RingHom.ker π))

def liftOpen (U : X₀.affineOpens) : X.affineOpens :=
  ⟨(GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent R R₀ π hπ hn X X₀ s s₀ i hpb U.1 U.2).choose,
    (GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent R R₀ π hπ hn X X₀ s s₀ i hpb U.1 U.2).choose_spec.1⟩

theorem preimage_liftOpen (U : X₀.affineOpens) : i ⁻¹ᵁ (liftOpen hpb hπ hn U).1 = U.1 :=
  (GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent R R₀ π hπ hn X X₀ s s₀ i hpb U.1 U.2).choose_spec.2

theorem liftOpen_mono (hi : Function.Surjective i.base) {U V : X₀.affineOpens} (h : V ≤ U) :
    liftOpen hpb hπ hn V ≤ liftOpen hpb hπ hn U := by
  intro x hx
  obtain ⟨y, rfl⟩ := hi x
  have hy : y ∈ i ⁻¹ᵁ (liftOpen hpb hπ hn V).1 := hx
  rw [preimage_liftOpen] at hy
  have hy' : y ∈ i ⁻¹ᵁ (liftOpen hpb hπ hn U).1 := by
    rw [preimage_liftOpen]; exact h hy
  exact hy'

def pr (U : X₀.affineOpens) : GlobalTheory.CechDR.Pair i := ⟨(U, liftOpen hpb hπ hn U), (preimage_liftOpen hpb hπ hn U).ge⟩

end GlobalTheory.LiftSys.OfLift

open GlobalTheory.LiftSys.OfLift in

theorem GlobalTheory.LiftSys.exists_sys_presents : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X), IsPullback i s₀ s (spMap π) → Smooth s → ∃ S : Sys I π s₀, Nonempty (S.Presents s i) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ X s i hpb hsm
  have hn : IsNilpotent (RingHom.ker π) := ⟨2, hk ▸ hI⟩
  haveI := surjective_spMap hI hk hπ
  have hi : Function.Surjective i.base :=
    (MorphismProperty.of_isPullback (P := @Surjective) hpb.flip ‹_›).surj
  let G : AffOp X₀ ⥤ AffOp X :=
    (Monotone.functor (f := liftOpen hpb hπ hn) fun _ _ h ↦ liftOpen_mono hpb hπ hn hi h).op
  let S : Sys I π s₀ :=
    { F := G ⋙ OAff s
      p := fun U ↦ GlobalTheory.CechDR.secPull s s₀ (pr hpb hπ hn U.unop)
      semi := fun U ↦ GlobalTheory.CechDR.semiHom_secPull hpb.w _
      nat := fun {U V} a b ↦ (congrArg (fun t ↦ t.hom b) (i.map_appLE (pr hpb hπ hn V.unop).2
          (homOfLE (liftOpen_mono hpb hπ hn hi (leOfHom a.unop))).op)).trans
        (congrArg (fun t ↦ t.hom b) (i.appLE_map (pr hpb hπ hn U.unop).2 (homOfLE (show V.unop.1 ≤ U.unop.1 from leOfHom a.unop)).op)).symm
      surj := fun U ↦ (GlobalTheory.CechDR.secPull_surjective_and_ker R R₀ I π hπ hk X₀ X s₀ s i hpb (pr hpb hπ hn U.unop) (preimage_liftOpen hpb hπ hn U.unop)).1
      ker := fun U b ↦ (GlobalTheory.CechDR.secPull_surjective_and_ker R R₀ I π hπ hk X₀ X s₀ s i hpb (pr hpb hπ hn U.unop) (preimage_liftOpen hpb hπ hn U.unop)).2 b
      smooth := fun U ↦ sec_smooth s _ }
  exact ⟨S, ⟨⟨fun U ↦ affPt s (liftOpen hpb hπ hn U.unop), fun U ↦ (liftOpen hpb hπ hn U.unop).2.isOpenImmersion_fromSpec, fun U ↦ affPt_w s _,
    fun U V a ↦ affPt_res s _, fun U ↦ GlobalTheory.CechDR.secPull_affPt s s₀ (pr hpb hπ hn U.unop),
    S.cover_of_surjective ⟨hi⟩ _ fun U ↦ GlobalTheory.CechDR.secPull_affPt s s₀ (pr hpb hπ hn U.unop)⟩⟩⟩
