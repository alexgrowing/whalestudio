import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedGenericFibreOfDense
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GeometricallyConnectedOfIsPullbackOfSurjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.VeryDenseFibres

theorem geometricallyConnected_fiber_iff {X T S : Scheme.{0}} (f : X ⟶ S) (t : T ⟶ S) (y : T) :
    GeometricallyConnected ((pullback.snd f t).fiberToSpecResidueField y) ↔
      GeometricallyConnected (f.fiberToSpecResidueField (t y)) := by
  have hp := isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f t) y
  refine ⟨fun h => ?_, fun h => MorphismProperty.of_isPullback (P := @GeometricallyConnected) hp h⟩
  have : Surjective (Spec.map (t.residueFieldMap y)) :=
    ⟨fun z => ⟨default, Subsingleton.elim _ _⟩⟩
  exact GlobalTheory.geometricallyConnected_of_isPullback_of_surjective hp

theorem smooth_fiber_of_smooth_fiber {X T S : Scheme.{0}} (f : X ⟶ S) (t : T ⟶ S) (y : T)
    (h : Smooth ((pullback.snd f t).fiberToSpecResidueField y)) :
    Smooth (f.fiberToSpecResidueField (t y)) := by
  have hp := isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f t) y
  refine MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hp.flip ⟨⟨?_, ?_⟩, ?_⟩ h
  · exact ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  · infer_instance
  · infer_instance

theorem mem_smoothLocus_of_smooth_fiber {R : CommRingCat.{0}} {X : Scheme.{0}} (f : X ⟶ Spec R)
    [LocallyOfFinitePresentation f] [Flat f] (x : X)
    (h : Smooth (f.fiberToSpecResidueField (f x))) : x ∈ f.smoothLocus := by
  wlog hX : ∃ S, X = Spec S generalizing f X
  · obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
    have _ : Smooth (pullback.snd f ((Spec R).fromSpecResidueField
        ((X.affineCover.f i ≫ f) y))) := h
    have H := this (X.affineCover.f i ≫ f) y (by
      rw [Scheme.Hom.fiberToSpecResidueField, ← pullbackRightPullbackFstIso_inv_snd_snd]
      infer_instance) ⟨_, rfl⟩
    rwa [← Scheme.Hom.preimage_smoothLocus_eq] at H
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  letI := φ.hom.toAlgebra
  haveI : Algebra.FinitePresentation R S :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation) (φ := φ)).mp ‹_›
  haveI : Module.Flat R S :=
    (HasRingHomProperty.Spec_iff (P := @Flat) (φ := φ)).mp ‹_›
  haveI : x.asIdeal.IsPrime := PrimeSpectrum.isPrime x
  let p : PrimeSpectrum R := Spec.map φ x
  haveI : x.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  haveI : Algebra.FormallySmooth p.asIdeal.ResidueField (p.asIdeal.Fiber S) := by
    rw [← RingHom.formallySmooth_algebraMap]
    refine RingHom.Smooth.formallySmooth ?_
    rw [← CommRingCat.hom_ofHom (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber ↑S)),
      ← HasRingHomProperty.Spec_iff (P := @Smooth),
      ← MorphismProperty.arrow_mk_iso_iff (P := @Smooth) (Spec.fiberToSpecResidueFieldIso R S p)]
    exact h
  haveI := Algebra.IsSmoothAt.of_formallySmooth_fiber (R := R) p.asIdeal x.asIdeal
  obtain ⟨g, hg, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R x.asIdeal
  let j : Spec (CommRingCat.of (Localization.Away g)) ⟶ Spec S :=
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))
  haveI : IsOpenImmersion j := IsOpenImmersion.of_isLocalization g
  haveI : Smooth (j ≫ Spec.map φ) := by
    rw [← Spec.map_comp, HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr hsm
  obtain ⟨y, rfl⟩ : x ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ g]
    exact hg
  have := (j ≫ Spec.map φ).smoothLocus_eq_top.ge (Set.mem_univ y)
  rwa [← Scheme.Hom.preimage_smoothLocus_eq] at this

theorem exists_opens_smoothOfRelativeDimension {X T S : Scheme.{0}} (f : X ⟶ S) [Smooth f]
    (t : T ⟶ S) (g : ℕ) (h : SmoothOfRelativeDimension g (pullback.snd f t)) (x : X) (y : T)
    (hxy : f x = t y) : ∃ W : X.Opens, x ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ f) := by
  obtain ⟨n, W, hW, hd⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim f x
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} n
  have h1 : SmoothOfRelativeDimension n (pullback.snd (W.ι ≫ f) t) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) _ _ hd
  have h2 : SmoothOfRelativeDimension (0 + (0 + g)) (pullback.snd (W.ι ≫ f) t) := by
    rw [← pullbackRightPullbackFstIso_inv_snd_snd]
    infer_instance
  obtain ⟨z, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback (W.ι ≫ f) t)
    ⟨x, hW⟩ y hxy
  have e : n = g := by simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h1 h2 z
  exact ⟨W, hW, e ▸ hd⟩

theorem eq_top_of_forall_mem {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R)
    [UniversallyClosed s] (P : Set (Ideal R))
    (hP : ∀ q : Ideal R, q.IsPrime → ∃ p ∈ P, p.IsPrime ∧ q ≤ p) (U : Z.Opens)
    (hU : ∀ z : Z, (s z).asIdeal ∈ P → z ∈ U) : U = ⊤ := by
  rw [← top_le_iff]
  intro x _
  by_contra hx
  have hc : IsClosed (s '' (U : Set Z)ᶜ) := s.isClosedMap _ U.2.isClosed_compl
  obtain ⟨p, hp, hp', hle⟩ := hP (s x).asIdeal (PrimeSpectrum.isPrime _)
  have hs : s x ⤳ (⟨p, hp'⟩ : PrimeSpectrum R) := (PrimeSpectrum.le_iff_specializes _ _).1 hle
  obtain ⟨y, hy, hy'⟩ := hs.mem_closed hc ⟨x, hx, rfl⟩
  exact hy (hU y (by rw [hy']; exact hp))

theorem spMap_apply_asIdeal {R K : Type} [CommRing R] [Field K] (x : R →+* K) (y : Sp K) :
    (spMap x y).asIdeal = RingHom.ker x := by
  have : y.asIdeal = ⊥ := by
    have := PrimeSpectrum.isPrime y
    exact Ideal.eq_bot_of_prime _
  change Ideal.comap x y.asIdeal = _
  rw [this]
  rfl

theorem geometricallyConnected_of_veryDense {R : Type} [CommRing R] [IsNoetherianRing R]
    {Z : Scheme.{0}} (s : Z ⟶ Sp R) [LocallyOfFiniteType s] [QuasiCompact s] (P : Set (Ideal R))
    (hP : ∀ (q₀ : Ideal R) (f₀ : R), q₀.IsPrime → f₀ ∉ q₀ →
      ∃ p₀ ∈ P, p₀.IsPrime ∧ q₀ ≤ p₀ ∧ f₀ ∉ p₀)
    (h : ∀ y : Sp R, y.asIdeal ∈ P → GeometricallyConnected (s.fiberToSpecResidueField y)) :
    GeometricallyConnected s := by
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  intro q
  have hq : q.asIdeal.IsPrime := PrimeSpectrum.isPrime q
  let t : Sp (R ⧸ q.asIdeal) ⟶ Sp R := spMap (Ideal.Quotient.mk q.asIdeal)
  have hd : Dense {y : Sp (R ⧸ q.asIdeal) | (t y).asIdeal ∈ P} := by
    refine (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R ⧸ q.asIdeal)).dense_iff.2 ?_
    rintro _ ⟨a, rfl⟩ ⟨z, hz⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have ha : a ∉ q.asIdeal := fun ha => hz (by
      rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]; exact Ideal.zero_mem _)
    obtain ⟨p, hp, hp', hle, hap⟩ := hP _ a hq ha
    obtain ⟨y, hy⟩ : (⟨p, hp'⟩ : PrimeSpectrum R) ∈
        Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk q.asIdeal)) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
      exact hle
    have hy' : Ideal.comap (Ideal.Quotient.mk q.asIdeal) y.asIdeal = p :=
      congrArg PrimeSpectrum.asIdeal hy
    refine ⟨y, fun hy2 => hap (hy' ▸ hy2), ?_⟩
    change Ideal.comap (Ideal.Quotient.mk q.asIdeal) y.asIdeal ∈ P
    rwa [hy']
  have H := GlobalTheory.geometricallyConnected_genericFibre_of_dense _ (Sp (R ⧸ q.asIdeal))
    (pullback.snd s t) _ hd fun y hy => (geometricallyConnected_fiber_iff s t y).2 (h _ hy)
  rw [geometricallyConnected_fiber_iff] at H
  have e : t (genericPoint (Sp (R ⧸ q.asIdeal))) = q := by
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext (Ideal.mk_ker (I := q.asIdeal))
  rwa [e] at H

theorem smoothOfRelativeDimension_and_geometricallyConnected_of_veryDense :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (g : ℕ) (P : Set (Ideal R)), (∀ (q₀ : Ideal R) (f₀ : R), q₀.IsPrime → f₀ ∉ q₀ → ∃ p₀ ∈ P, p₀.IsPrime ∧ q₀ ≤ p₀ ∧ f₀ ∉ p₀) → IsProjOver s → Flat s → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K), RingHom.ker x = q ∧ SmoothOfRelativeDimension g (pullback.snd s (spMap x)) ∧ GeometricallyConnected (pullback.snd s (spMap x))) → SmoothOfRelativeDimension g s ∧ GeometricallyConnected s := by
  intro R _ _ Z s g P hP hs hf h
  have : IsProper s := by
    obtain ⟨N, i, hi, rfl⟩ := hs
    have := isProper_str R N
    infer_instance
  have : LocallyOfFinitePresentation s := inferInstance
  have hP' : ∀ q : Ideal R, q.IsPrime → ∃ p ∈ P, p.IsPrime ∧ q ≤ p := fun q hq => by
    obtain ⟨p, h1, h2, h3, -⟩ := hP q 1 hq ((Ideal.ne_top_iff_one q).1 hq.ne_top)
    exact ⟨p, h1, h2, h3⟩
  have h' : ∀ y : Sp R, y.asIdeal ∈ P → ∃ (T : Scheme.{0}) (t : T ⟶ Sp R) (w : T), t w = y ∧
      SmoothOfRelativeDimension g (pullback.snd s t) ∧
      GeometricallyConnected (pullback.snd s t) := fun y hy => by
    obtain ⟨K, _, x, hx, h1, h2⟩ := h _ hy
    exact ⟨_, spMap x, (default : PrimeSpectrum K),
      PrimeSpectrum.ext ((spMap_apply_asIdeal x _).trans hx), h1, h2⟩
  refine ⟨?_, geometricallyConnected_of_veryDense s P hP fun y hy => ?_⟩
  · have : Smooth s := by
      rw [← Scheme.Hom.smoothLocus_eq_top_iff]
      refine eq_top_of_forall_mem s P hP' _ fun z hz => ?_
      obtain ⟨T, t, w, hw, h1, -⟩ := h' _ hz
      refine mem_smoothLocus_of_smooth_fiber s z ?_
      rw [← hw]
      have : Smooth (pullback.snd s t) := SmoothOfRelativeDimension.smooth g _
      exact smooth_fiber_of_smooth_fiber s t w
        (inferInstanceAs (Smooth (pullback.snd (pullback.snd s t) (T.fromSpecResidueField w))))
    let V : {W : Z.Opens // SmoothOfRelativeDimension g (W.ι ≫ s)} → Z.Opens := fun W => W.1
    have htop : iSup V = ⊤ := by
      refine eq_top_of_forall_mem s P hP' _ fun z hz => ?_
      obtain ⟨T, t, w, hw, h1, -⟩ := h' _ hz
      obtain ⟨W, hW, hW'⟩ := exists_opens_smoothOfRelativeDimension s t g h1 z w hw.symm
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW'⟩, hW⟩
    have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} g) :=
      HasRingHomProperty.instIsZariskiLocalAtSource
    exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} g) V htop
      fun W => W.2
  · obtain ⟨T, t, w, rfl, -, h2⟩ := h' _ hy
    exact (geometricallyConnected_fiber_iff s t w).1 inferInstance

end GlobalTheory.VeryDenseFibres
