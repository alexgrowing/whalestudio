import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkClosedPointToGermTop
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitOfBasicOpenNonemptyOfUniversallyClosed
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.FibreFunctionConstant

theorem exists_section_of_germs (Y : Scheme.{0}) (g : ∀ y : Y, Y.presheaf.stalk y)
    (hg : ∀ y : Y, ∃ (W : Y.Opens) (_ : y ∈ W) (t : Γ(Y, W)),
      ∀ z (hz : z ∈ W), Y.presheaf.germ W z hz t = g z) :
    ∃ a : Γ(Y, ⊤), ∀ y, Y.presheaf.germ ⊤ y trivial a = g y := by
  choose W hW t ht using hg
  have compat : TopCat.Presheaf.IsCompatible Y.sheaf.obj W t := by
    intro i j
    apply TopCat.Presheaf.section_ext Y.sheaf (W i ⊓ W j)
    rintro y ⟨hi, hj⟩
    exact (TopCat.Presheaf.germ_res_apply Y.presheaf
      (TopologicalSpace.Opens.infLELeft (W i) (W j)) y ⟨hi, hj⟩ (t i)).trans
      ((ht i y hi).trans ((ht j y hj).symm.trans
        (TopCat.Presheaf.germ_res_apply Y.presheaf
          (TopologicalSpace.Opens.infLERight (W i) (W j)) y ⟨hi, hj⟩ (t j)).symm))
  have hcov : (⊤ : Y.Opens) ≤ iSup W := fun y _ =>
    TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hW y⟩
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' W ⊤ (fun i => homOfLE le_top) hcov t compat
  refine ⟨a, fun q => ?_⟩
  have e := TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE (le_top : W q ≤ ⊤)) q (hW q) a
  have e2 : (Y.presheaf.map (homOfLE (le_top : W q ≤ ⊤)).op).hom a = t q := ha q
  exact e.symm.trans ((congrArg (fun z => (Y.presheaf.germ (W q) q (hW q)).hom z) e2).trans (ht q q (hW q)))

theorem unit_of_cover {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (hc : IsCptGen ξ)
    (π : Γ(X, ⊤)) (ϖ : Ω) (h0 : ϖ ≠ 0)
    (hπ : ∀ p : Cpt ξ, genMap ξ p (X.presheaf.germ ⊤ p.1 trivial π) = ϖ)
    (k : Type) [Field k] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of k)) [UniversallyClosed f]
    [ConnectedSpace Y] (ι : Y ⟶ X) (hι : ι.appTop π = 0) (hr : Set.range ι = zeroSet ξ ϖ)
    (h : Cpt ξ → Ω)
    (H : ∀ p : Cpt ξ, ¬ unitAt ξ p ϖ → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q ϖ →
      h p ∈ regAt ξ q ∧ (h p - h q) / ϖ ∈ regAt ξ q)
    (hex : ∃ p, ¬ unitAt ξ p ϖ ∧ unitAt ξ p (h p)) : ∀ p, ¬ unitAt ξ p ϖ → unitAt ξ p (h p) := by
  have hy : ∀ y : Y, ι y ∈ zeroSet ξ ϖ := fun y => hr ▸ ⟨y, rfl⟩
  choose hs hn using hy
  have hreg : ∀ y : Y, ∃ c : X.presheaf.stalk (ι y), genMap ξ ⟨ι y, hs y⟩ c = h ⟨ι y, hs y⟩ := fun y => by
    obtain ⟨U, hU, HU⟩ := H ⟨ι y, hs y⟩ (hn y)
    exact (HU _ hU (hn y)).1
  choose c hcv using hreg
  have hzero : ∀ y : Y, (ι.stalkMap y).hom (X.presheaf.germ ⊤ (ι y) trivial π) = 0 := fun y => by
    have := Scheme.Hom.germ_stalkMap_apply ι ⊤ y trivial π
    rw [this]
    have e : (ι.app ⊤).hom π = 0 := hι
    erw [e]
    exact map_zero _
  obtain ⟨a, ha⟩ := exists_section_of_germs Y (fun y => (ι.stalkMap y).hom (c y)) (fun y => by
    obtain ⟨U, hU, HU⟩ := H ⟨ι y, hs y⟩ (hn y)
    obtain ⟨W, hW, t, ht⟩ := X.presheaf.exists_germ_eq (c y)
    refine ⟨ι ⁻¹ᵁ (W ⊓ U), ⟨hW, hU⟩, ι.app (W ⊓ U) (X.presheaf.map (homOfLE inf_le_left).op t), fun z hz => ?_⟩
    have hz' : ι z ∈ W ⊓ U := hz
    rw [← Scheme.Hom.germ_stalkMap_apply ι (W ⊓ U) z hz']
    have e1 := TopCat.Presheaf.germ_res_apply X.presheaf
      (homOfLE inf_le_left : W ⊓ U ⟶ W) (ι z) hz' t
    erw [e1]
    obtain ⟨d, hd⟩ := (HU ⟨ι z, hs z⟩ hz'.2 (hn z)).2
    have e2 : genMap ξ ⟨ι z, hs z⟩ (X.presheaf.germ W (ι z) hz'.1 t) = h ⟨ι y, hs y⟩ := by
      rw [← hcv y, ← ht]
      exact genMap_germ_eq_genMap_germ ξ W ⟨ι z, hs z⟩ ⟨ι y, hs y⟩ hz'.1 hW t
    have e3 : X.presheaf.germ W (ι z) hz'.1 t = c z + X.presheaf.germ ⊤ (ι z) trivial π * d := by
      apply hc.inj ⟨ι z, hs z⟩
      have e4 := hπ ⟨ι z, hs z⟩
      refine e2.trans ?_
      rw [map_add, map_mul]
      erw [hcv z, e4, hd]
      field_simp
      ring
    erw [e3]
    rw [map_add, map_mul, hzero, zero_mul, add_zero])
  have hiff : ∀ y : Y, y ∈ Y.basicOpen a ↔ unitAt ξ ⟨ι y, hs y⟩ (h ⟨ι y, hs y⟩) := fun y => by
    rw [Scheme.mem_basicOpen_top]
    erw [ha y]
    rw [isUnit_map_iff]
    refine Iff.trans ?_ (unitAt_iff_of_isCptGen ξ hc ⟨ι y, hs y⟩ _).symm
    constructor
    · intro hu
      exact ⟨c y, hu, hcv y⟩
    · rintro ⟨u, hu, e⟩
      rwa [← hc.inj ⟨ι y, hs y⟩ (e.trans (hcv y).symm)]
  have lift : ∀ p : Cpt ξ, ¬ unitAt ξ p ϖ → ∃ y : Y, p = ⟨ι y, hs y⟩ := fun p hp => by
    obtain ⟨y, hy⟩ : p.1 ∈ Set.range ι := hr ▸ (coe_mem_zeroSet p).2 hp
    exact ⟨y, Subtype.ext hy.symm⟩
  obtain ⟨p₀, hp₀, hu₀⟩ := hex
  obtain ⟨y₀, rfl⟩ := lift p₀ hp₀
  have hu := isUnit_of_basicOpen_nonempty_of_universallyClosed k Y f a ⟨y₀, (hiff y₀).2 hu₀⟩
  intro p hp
  obtain ⟨y, rfl⟩ := lift p hp
  refine (hiff y).1 ?_
  rw [Y.basicOpen_of_isUnit hu]
  trivial

end PositivityTheory.Xgn.FibreFunctionConstant

open PositivityTheory.Xgn.FibreFunctionConstant in
theorem PositivityTheory.Xgn.function_on_connected_fibre_unit : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) → ∀ h : Cpt ξ → Ω, (∀ p : Cpt ξ, ¬ unitAt ξ p (algebraMap O Ω ϖ) → ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → ¬ unitAt ξ q (algebraMap O Ω ϖ) → h p ∈ regAt ξ q ∧ (h p - h q) / algebraMap O Ω ϖ ∈ regAt ξ q) → (∃ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) ∧ unitAt ξ p (h p)) → ∀ p, ¬ unitAt ξ p (algebraMap O Ω ϖ) → unitAt ξ p (h p) := by
  intro X Ω _ ξ O _ _ _ _ s _ ϖ hϖ hinj hs hc hconn h H hex
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  obtain ⟨U, hU, hUc, -⟩ := cpt_open_integral X Ω ξ hc
  haveI : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _ (by simpa using hUc)
  let r : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ Spec (CommRingCat.of O) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))
  haveI : IsClosedImmersion r :=
    IsClosedImmersion.spec_of_surjective _ (IsLocalRing.residue_surjective (R := O))
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hrr : ∀ x : Spec (CommRingCat.of O), x ∈ Set.range r ↔ ϖ ∈ x.asIdeal := fun x => by
    have e : Set.range r = PrimeSpectrum.zeroLocus (RingHom.ker (IsLocalRing.residue O) : Set O) :=
      range_comap_of_surjective _ _ (IsLocalRing.residue_surjective (R := O))
    rw [e, IsLocalRing.ker_residue, hmax, PrimeSpectrum.zeroLocus_span]
    exact Set.singleton_subset_iff
  let ι : pullback (U.ι ≫ s) r ⟶ X := pullback.fst _ _ ≫ U.ι
  have hr : Set.range ι = zeroSet ξ (algebraMap O Ω ϖ) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      have h1 : genPt ξ ⤳ ι y := (hU _).1 (pullback.fst (U.ι ≫ s) r y).2
      refine ⟨h1, ?_⟩
      rw [(ConstReg.regular_const X Ω ξ O s hs ⟨_, h1⟩ ϖ).2 hc, not_not, ← hrr]
      refine ⟨pullback.snd (U.ι ≫ s) r y, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← pullback.condition]
      simp [ι]
    · rintro ⟨h1, h2⟩
      rw [(ConstReg.regular_const X Ω ξ O s hs ⟨_, h1⟩ ϖ).2 hc, not_not, ← hrr] at h2
      have h3 : (⟨x, (hU x).2 h1⟩ : U.toScheme) ∈ Set.range (pullback.fst (U.ι ≫ s) r) := by
        rw [Scheme.Pullback.range_fst]
        exact h2
      obtain ⟨y, hy⟩ := h3
      refine ⟨y, ?_⟩
      simp [ι, hy]
  haveI : ConnectedSpace (pullback (U.ι ≫ s) r : Scheme.{0}) := by
    rw [← hr, ← Set.image_univ] at hconn
    rw [connectedSpace_iff_univ]
    exact ⟨hconn.1.of_image, ι.isEmbedding.isInducing.isPreconnected_image.1 hconn.2⟩
  refine unit_of_cover ξ hc (s.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ)) _
    ((map_ne_zero_iff _ hinj).2 hϖ.ne_zero) (fun p => ConstReg.genMap_germ_const ξ s hs p ϖ)
    (IsLocalRing.ResidueField O) _ (pullback.snd (U.ι ≫ s) r) ι ?_ hr h H hex
  have e : ι ≫ s = pullback.snd (U.ι ≫ s) r ≫ r := by
    rw [← pullback.condition]; simp [ι]
  have e1 : r.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ) = 0 := by
    have h3 := congrArg (fun q => q.hom ϖ)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (IsLocalRing.residue O)))
    have h3' : (Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField O))).inv.hom (IsLocalRing.residue O ϖ) =
      r.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom ϖ) := h3
    rw [← h3', (IsLocalRing.residue_eq_zero_iff ϖ).2 (hmax ▸ Ideal.mem_span_singleton_self ϖ), map_zero]
  have e2 : (ι ≫ s).appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ) = 0 := by
    rw [e, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, e1, map_zero]
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at e2
  exact e2
