import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PhiDivisorArcBlowup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMonomialLevelFormDvr
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitGeneric

theorem mem_of_dense_of_maximal {X : Type} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X] {x : X}
    (hx : ∀ y, y ⤳ x → x ⤳ y) {U : Set X} (hU : IsOpen U) (hd : Dense U) : x ∈ U := by
  obtain ⟨o, ho, hne, hs⟩ := NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _
    (irreducibleComponent_mem_irreducibleComponents x)
  obtain ⟨y, hyo, hyU⟩ := hd.inter_open_nonempty o ho hne
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := x)) isClosed_irreducibleComponent
  have e := hx ξ (hξ.specializes mem_irreducibleComponent)
  exact (e.trans (hξ.specializes (hs hyo))).mem_open hU hyU

theorem maximal_of_flat {V Y : Scheme.{0}} (f : V ⟶ Y) [Flat f] {x : V} (hx : ∀ y, y ⤳ x → x ⤳ y) :
    ∀ y, y ⤳ f x → f x ⤳ y := by
  intro y hy
  obtain ⟨z, h₁, rfl⟩ := Flat.generalizingMap f hy
  exact (hx z h₁).map f.continuous

theorem maximal_of_injective {V : Scheme.{0}} (v : V) [IsDomain (V.presheaf.stalk v)] {W : Type} [CommRing W]
    [IsDomain W] (g : V.presheaf.stalk v →+* W) (hg : Function.Injective g) (p : Sp (FractionRing W)) :
    ∀ y, y ⤳ (jK W ≫ spMap g ≫ V.fromSpecStalk v) p → (jK W ≫ spMap g ≫ V.fromSpecStalk v) p ⤳ y := by
  intro y hy
  have hq : (jK W ≫ spMap g ≫ V.fromSpecStalk v) p = V.fromSpecStalk v ((jK W ≫ spMap g) p) := rfl
  rw [hq] at hy ⊢
  have h1 : V.fromSpecStalk v ((jK W ≫ spMap g) p) ⤳ v := by
    have : V.fromSpecStalk v ((jK W ≫ spMap g) p) ∈ Set.range (V.fromSpecStalk v) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  obtain ⟨q, rfl⟩ : y ∈ Set.range (V.fromSpecStalk v) := by
    rw [Scheme.range_fromSpecStalk]; exact hy.trans h1
  refine Specializes.map ?_ (V.fromSpecStalk v).continuous
  refine (PrimeSpectrum.le_iff_specializes _ _).1 fun a ha => ?_
  have h2 : algebraMap W (FractionRing W) (g a) ∈ p.asIdeal := ha
  have h3 : p.asIdeal = ⊥ := by
    rcases Ideal.eq_bot_or_top p.asIdeal with h | h
    · exact h
    · exact absurd h p.isPrime.ne_top
  rw [h3, Ideal.mem_bot, FaithfulSMul.algebraMap_eq_zero_iff, map_eq_zero_iff g hg] at h2
  subst h2
  exact zero_mem _

theorem flat_of_stalkClosedPointTo {X : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ X)
    (h : (Scheme.stalkClosedPointTo ξ).hom.Flat) : Flat ξ := by
  have h1 : Flat (Spec.map (Scheme.stalkClosedPointTo ξ)) := Flat.SpecMap_iff.2 h
  have h2 := GlobalTheory.GenericExt.flat_fromSpecStalk X (ξ (closedPoint R))
  have h3 : Flat (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk (ξ (closedPoint R))) :=
    MorphismProperty.comp_mem _ _ _ h1 h2
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of R) ξ ▸ h3

theorem range_generic_subset_range_j : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (π : Z.X ⟶ X.X) (e : gen Y ≅ gen Z) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X.X), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ∀ v : ↥(pullback ξ (e.hom ≫ genι Z ≫ π) : Scheme.{0}), IsDomain ((pullback ξ (e.hom ≫ genι Z ≫ π)).presheaf.stalk v) → ∀ (W : Type) [CommRing W] [IsDomain W] (g : (pullback ξ (e.hom ≫ genι Z ≫ π)).presheaf.stalk v →+* W), Function.Injective g → Set.range (jK W ≫ spMap g ≫ (pullback ξ (e.hom ≫ genι Z ≫ π)).fromSpecStalk v ≫ pullback.snd ξ (e.hom ≫ genι Z ≫ π) ≫ genι Y) ⊆ Set.range Y.j := by
  intro E _ _ _ H D l Xo c X Z Y π e R _ _ _ ξ hξ v hv W _ _ g hg
  have hfl : Flat ξ := flat_of_stalkClosedPointTo ξ hξ.1
  have hfl' : Flat (pullback.snd ξ (e.hom ≫ genι Z ≫ π)) := inferInstance
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver Y.proj
  have := Y.jQ_open
  have : IsLocallyNoetherian (gen Y) := LocallyOfFiniteType.isLocallyNoetherian (genStr Y)
  have : CompactSpace (gen Y) := QuasiCompact.compactSpace_of_compactSpace (genStr Y)
  have : IsNoetherian (gen Y) := {}
  rintro _ ⟨p, rfl⟩
  obtain ⟨a, ha⟩ := mem_of_dense_of_maximal
    (maximal_of_flat (pullback.snd ξ (e.hom ≫ genι Z ≫ π)) (maximal_of_injective v g hg p))
    Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense
  exact ⟨a, congrArg (genι Y) ha⟩

end GlobalTheory.TraitGeneric
