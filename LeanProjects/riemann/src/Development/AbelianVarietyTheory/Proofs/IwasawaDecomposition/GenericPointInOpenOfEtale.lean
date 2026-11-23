import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolOfFiniteSurjective
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

noncomputable section

namespace GlobalTheory.GenFibre

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

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem mem_range_j_of_maximal (Z : GMod Xo c) (P : Z.X) (hP : ∀ q : Z.X, q ⤳ P → q = P) :
    P ∈ Set.range Z.j := by
  have := GlobalTheory.AmpleDown.isNoetherian_gmod Z
  haveI : GlobalTheory.IsNormalScheme Z.X := GlobalTheory.IsNormalScheme.of_pred Z.normal
  haveI := Z.flat
  have b₂ : Flat (spMap (algebraMap (𝓞 c.F) c.F)) := by
    have : Module.Flat (𝓞 c.F) c.F := IsLocalization.flat c.F (nonZeroDivisors (𝓞 c.F))
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 this)
  have a₂ : Flat (pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback _ _).flip b₂
  let g0 : PrimeSpectrum (𝓞 c.F) := ⟨⊥, Ideal.bot_prime⟩
  have hsP : Z.s P = g0 := by
    have s₀ : g0 ⤳ Z.s P := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    obtain ⟨P', h₁, h₂⟩ := Flat.generalizingMap Z.s s₀
    rw [← hP P' h₁, h₂]
  let f0 : PrimeSpectrum c.F := ⟨⊥, Ideal.bot_prime⟩
  have hf0 : spMap (algebraMap (𝓞 c.F) c.F) f0 = g0 := by
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap (𝓞 c.F) c.F) ⊥ = ⊥
    exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective (𝓞 c.F) c.F)
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Z.s)
    (g := spMap (algebraMap (𝓞 c.F) c.F)) P f0 (hsP.trans hf0.symm)
  have hC := irreducibleComponent_mem_irreducibleComponents P
  have hCo : IsOpen (irreducibleComponent P) := GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents hC
  have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
  have hgP : hC.1.genericPoint = P := hP _ (hg.specializes mem_irreducibleComponent)
  obtain ⟨w, hwC, ⟨v, rfl⟩⟩ := Z.jQ_dense.inter_open_nonempty _
    (hCo.preimage (pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F))).continuous)
    ⟨z, by rw [Set.mem_preimage, hz]; exact mem_irreducibleComponent⟩
  have hPw : P ⤳ pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F)) (Z.jQ v) := hgP ▸ hg.specializes hwC
  obtain ⟨w', h₁, h₂⟩ := Flat.generalizingMap (pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F))) hPw
  have := Z.jQ_open
  obtain ⟨v', rfl⟩ := h₁.mem_open Z.jQ.isOpenEmbedding.isOpen_range ⟨v, rfl⟩
  exact ⟨v', by rw [Model.j, Scheme.Hom.comp_apply]; exact h₂⟩

theorem range_jK_subset_range_j : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (ξ : Sp R ⟶ Z.X), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → Set.range (jK R ≫ ξ) ⊆ Set.range Z.j := by
  intro E _ _ _ H D l Xo c Z R _ _ _ ξ hξe
  set x' := ξ (closedPoint (CommRingCat.of R))
  haveI : IsLocalHom (Scheme.stalkClosedPointTo ξ).hom := Scheme.isLocalHom_stalkClosedPointTo ξ
  have hinj := injective_of_flat_local _ hξe.1
  haveI : IsDomain (Z.X.presheaf.stalk x') := hinj.isDomain _
  have hξ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  rintro _ ⟨x0, rfl⟩
  set η := Spec.map (Scheme.stalkClosedPointTo ξ) (jK R x0) with hη
  have hη0 : η.asIdeal = ⊥ := by
    have h0 : x0.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ x0.asIdeal x0.isPrime
    change Ideal.comap _ (Ideal.comap _ x0.asIdeal) = ⊥
    rw [h0, CommRingCat.hom_ofHom, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R _), ← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).1 hinj
  have hp : (jK R ≫ ξ) x0 = Z.X.fromSpecStalk x' η := by
    rw [Scheme.Hom.comp_apply, ← hξ, Scheme.Hom.comp_apply]
  rw [hp]
  apply mem_range_j_of_maximal Z
  intro q hq
  have hqz : q ∈ Set.range (Z.X.fromSpecStalk x') := by
    rw [Scheme.range_fromSpecStalk]
    exact hq.trans (((IsLocalRing.specializes_closedPoint η).map (Z.X.fromSpecStalk x').continuous).trans
      (specializes_of_eq Scheme.fromSpecStalk_closedPoint))
  obtain ⟨Q, rfl⟩ := hqz
  have hQ : Q ⤳ η := (IsPreimmersion.isEmbedding (Z.X.fromSpecStalk x')).specializes_iff.1 hq
  have hQη : Q = η := PrimeSpectrum.ext (le_antisymm ((PrimeSpectrum.le_iff_specializes Q η).2 hQ)
    (hη0 ▸ bot_le))
  rw [hQη]

end GlobalTheory.GenFibre
