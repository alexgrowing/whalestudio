import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartFiniteType
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

noncomputable section

namespace GlobalTheory.Reg.ChartOpens

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem away_irreducible {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] {ϖ : O} (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ K := by
  have hi := IsFractionRing.injective O K
  refine IsLocalization.Away.mk _ (IsUnit.mk0 _ (by simpa using hϖ.ne_zero)) (fun z => ?_)
    (fun a b h => ⟨0, by rw [hi h]⟩)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) z
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hϖ
  refine ⟨n, a * ↑u⁻¹, ?_⟩
  have h1 : algebraMap O K ϖ ≠ 0 := by simpa using hϖ.ne_zero
  have h2 : algebraMap O K u * algebraMap O K ↑u⁻¹ = 1 := by rw [← map_mul]; simp
  have h3 : algebraMap O K u ≠ 0 := left_ne_zero_of_mul_eq_one h2
  rw [map_mul, map_mul, map_pow, eq_inv_of_mul_eq_one_right h2]
  field_simp

theorem exists_finset_basicOpen {A : Type} [CommRing A] [IsNoetherianRing A] (V : Set (PrimeSpectrum A))
    (hV : IsOpen V) (hne : V.Nonempty) :
    ∃ es : Finset A, es.Nonempty ∧ (∀ e ∈ es, e ≠ 0) ∧ ∀ p, p ∈ V ↔ ∃ e ∈ es, e ∉ p.asIdeal := by
  classical
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1 hV.isClosed_compl
  obtain ⟨s, rfl⟩ := IsNoetherian.noetherian I
  have key : ∀ p, p ∈ V ↔ ∃ e ∈ s.filter (· ≠ 0), e ∉ p.asIdeal := by
    intro p
    have : p ∉ V ↔ (s : Set A) ⊆ p.asIdeal := by
      rw [← Set.mem_compl_iff, hI]
      exact (PrimeSpectrum.mem_zeroLocus _ _).trans Ideal.span_le
    constructor
    · intro hp
      obtain ⟨e, he, h⟩ := Set.not_subset.1 (fun h => this.2 h hp)
      exact ⟨e, Finset.mem_filter.2 ⟨he, fun h0 => h (h0 ▸ p.asIdeal.zero_mem)⟩, h⟩
    · rintro ⟨e, he, h⟩
      by_contra hp
      exact h (this.1 hp (Finset.mem_filter.1 he).1)
  obtain ⟨p, hp⟩ := hne
  obtain ⟨e, he, -⟩ := (key p).1 hp
  exact ⟨_, ⟨e, he⟩, fun e he => (Finset.mem_filter.1 he).2, key⟩

theorem isOpenImmersion_of_surj {O K A R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [CommRing A] [CommRing R] [Algebra K R] (α : O →+* A) (f : A →+* R)
    (hf : f.comp α = (algebraMap K R).comp (algebraMap O K)) (x : A) (hx : IsUnit (f x)) (hi : Function.Injective f)
    (hs : ∀ r : R, ∃ (a : A) (k : K) (N : ℕ), r * f x ^ N = algebraMap K R k * f a) :
    IsOpenImmersion (spMap f) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have := away_irreducible (K := K) hϖ
  have hfo : ∀ o, f (α o) = algebraMap K R (algebraMap O K o) := fun o => RingHom.congr_fun hf o
  letI := f.toAlgebra
  have : IsLocalization.Away (α ϖ * x) R := by
    refine IsLocalization.Away.mk _ ?_ (fun r => ?_) (fun a b h => ⟨0, by rw [hi h]⟩)
    · show IsUnit (f _)
      rw [map_mul, hfo]
      exact ((IsLocalization.Away.algebraMap_isUnit (S := K) ϖ).map _).mul hx
    · obtain ⟨a, k, N, h⟩ := hs r
      obtain ⟨n, o, ho⟩ := IsLocalization.Away.surj ϖ k
      refine ⟨N + n, α (o * ϖ ^ N) * x ^ n * a, ?_⟩
      show r * f _ ^ _ = f _
      have h2 : algebraMap K R k * f (α ϖ) ^ n = f (α o) := by
        rw [hfo, hfo, ← ho, map_mul, map_pow]
      simp only [map_mul, map_pow]
      rw [← h2]
      linear_combination (f (α ϖ) ^ (N + n) * f x ^ n) * h
  exact IsOpenImmersion.of_isLocalization (α ϖ * x)

theorem chart_opens {O K A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [CommRing A] [IsDomain A] {X Z : Scheme.{0}} (s : X ⟶ Sp O) [Flat s]
    (g : Sp A ⟶ X) [IsOpenImmersion g] (α : O →+* A) (hα : g ≫ s = spMap α) (hft : α.FiniteType)
    (t : Z ⟶ Sp K) [Smooth t] (jQ : Z ⟶ pullback s (spMap (algebraMap O K))) [IsOpenImmersion jQ]
    (hd : Dense (Set.range jQ)) (hj : jQ ≫ pullback.snd _ _ = t) :
    ∃ es : Finset A, Function.Injective α ∧ es.Nonempty ∧ (∀ e ∈ es, e ≠ 0) ∧
      (∀ e ∈ es, ∀ (R : Type) [CommRing R] [Algebra K R] (f : A →+* R),
        f.comp α = (algebraMap K R).comp (algebraMap O K) → IsUnit (f e) →
          (∃ xF : Sp R ⟶ Z, xF ≫ t = spMap (algebraMap K R) ∧ xF ≫ jQ ≫ pullback.fst _ _ = spMap f ≫ g) ∧
          ∀ d : A, Function.Injective f → IsUnit (f d) →
            (∀ r : R, ∃ (a : A) (k : K) (N : ℕ), r * f (e * d) ^ N = algebraMap K R k * f a) → Algebra.Smooth K R) ∧
      ∀ (L : Type) [Field L] [Algebra K L] (f : A →+* L) (xF : Sp L ⟶ Z), xF ≫ t = spMap (algebraMap K L) →
        xF ≫ jQ ≫ pullback.fst _ _ = spMap f ≫ g →
          f.comp α = (algebraMap K L).comp (algebraMap O K) ∧ ∃ e ∈ es, f e ≠ 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have := away_irreducible (K := K) hϖ
  have hopen : IsOpenImmersion (spMap (algebraMap O K)) := IsOpenImmersion.of_isLocalization ϖ
  have hjs : (jQ ≫ pullback.fst _ _) ≫ s = t ≫ spMap (algebraMap O K) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hj]
  have hflat : α.Flat := (HasRingHomProperty.Spec_iff (P := @Flat) (φ := CommRingCat.ofHom α)).1 (by
    show Flat (spMap α)
    rw [← hα]; infer_instance)
  have hinj : Function.Injective α := by
    letI := α.toAlgebra
    have : Module.Flat O A := hflat
    exact FaithfulSMul.algebraMap_injective O A
  have hN : IsNoetherianRing A := by
    letI := α.toAlgebra
    have : Algebra.FiniteType O A := hft
    exact Algebra.FiniteType.isNoetherianRing O A
  let j := jQ ≫ pullback.fst s (spMap (algebraMap O K))
  let V : Set (PrimeSpectrum A) := g ⁻¹' Set.range j
  have hV : IsOpen V := j.isOpenEmbedding.isOpen_range.preimage g.continuous
  have hne : V.Nonempty := by
    have h0 : g (⊥ : PrimeSpectrum A) ∈ Set.range (pullback.fst s (spMap (algebraMap O K))) := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨(⊥ : PrimeSpectrum K), ?_⟩
      refine Eq.trans ?_ (Scheme.Hom.comp_apply g s _)
      rw [hα]
      refine PrimeSpectrum.ext ?_
      show Ideal.comap (algebraMap O K) ⊥ = Ideal.comap α ⊥
      rw [Ideal.comap_bot_of_injective _ hinj, Ideal.comap_bot_of_injective _ (IsFractionRing.injective O K)]
    obtain ⟨y, hy⟩ := h0
    obtain ⟨_, ⟨p, hp⟩, z, rfl⟩ := hd.inter_open_nonempty
      (pullback.fst s (spMap (algebraMap O K)) ⁻¹' Set.range g)
      (g.isOpenEmbedding.isOpen_range.preimage (Scheme.Hom.continuous _)) ⟨y, _, hy.symm⟩
    exact ⟨p, z, by rw [hp]; exact Scheme.Hom.comp_apply _ _ _⟩
  obtain ⟨es, h1, h2, h3⟩ := exists_finset_basicOpen V hV hne
  refine ⟨es, hinj, h1, h2, fun e he R _ _ f hf hu => ?_, fun L _ _ f xF hx1 hx2 => ⟨?_, ?_⟩⟩
  · have hr : Set.range (spMap f ≫ g) ⊆ Set.range j := by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Hom.comp_apply]
      refine (h3 (spMap f p)).2 ⟨e, he, fun h => ?_⟩
      exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (show f e ∈ p.asIdeal from h) hu)
    let xF := IsOpenImmersion.lift j (spMap f ≫ g) hr
    have hx : xF ≫ j = spMap f ≫ g := IsOpenImmersion.lift_fac _ _ _
    have ht : xF ≫ t = spMap (algebraMap K R) := by
      rw [← cancel_mono (spMap (algebraMap O K)), Category.assoc, ← hjs, ← Category.assoc, hx, Category.assoc, hα,
        ← spMap_comp, ← spMap_comp, hf]
    refine ⟨⟨xF, ht, hx⟩, fun d hi hdu hs => ?_⟩
    have := isOpenImmersion_of_surj α f hf (e * d) (by rw [map_mul]; exact hu.mul hdu) hi hs
    have : IsOpenImmersion (xF ≫ j) := by rw [hx]; infer_instance
    have : IsOpenImmersion xF := IsOpenImmersion.of_comp xF j
    have : Smooth (spMap (algebraMap K R)) := by rw [← ht]; infer_instance
    exact RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)).1 this)
  · have : spMap (f.comp α) = spMap ((algebraMap K L).comp (algebraMap O K)) := by
      rw [spMap_comp, spMap_comp, ← hα, ← Category.assoc, ← hx2, ← hx1, Category.assoc, hjs, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  · obtain ⟨e, he, h⟩ := (h3 (spMap f (⊥ : PrimeSpectrum L))).1
      ⟨xF (⊥ : PrimeSpectrum L), (Scheme.Hom.comp_apply xF j _).symm.trans
        ((congrArg (fun φ : Sp L ⟶ X => φ (⊥ : PrimeSpectrum L)) hx2).trans (Scheme.Hom.comp_apply _ _ _))⟩
    exact ⟨e, he, fun h0 => h (show f e ∈ (⊥ : Ideal L) from h0)⟩

theorem moduli_basicOpens :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O c.F] [IsFractionRing O c.F] (Y : Model Xo c (algebraMap O c.F)) (M : MChart Y), ∃ (α : O →+* Γ(Y.X, M.U)) (es : Finset Γ(Y.X, M.U)), M.hU.fromSpec ≫ Y.s = spMap α ∧ α.FiniteType ∧ Function.Injective α ∧ es.Nonempty ∧ (∀ e ∈ es, e ≠ 0) ∧ (∀ e ∈ es, ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R), f.comp α = (algebraMap c.F R).comp (algebraMap O c.F) → IsUnit (f e) → (∃ xF : Sp R ⟶ Xo.XF c, xF ≫ pullback.snd _ _ = spMap (algebraMap c.F R) ∧ xF ≫ Y.j = spMap f ≫ M.hU.fromSpec) ∧ ∀ d : Γ(Y.X, M.U), Function.Injective f → IsUnit (f d) → (∀ r : R, ∃ (a : Γ(Y.X, M.U)) (k : c.F) (N : ℕ), r * f (e * d) ^ N = algebraMap c.F R k * f a) → Algebra.Smooth c.F R) ∧ ∀ (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L) (xF : Sp L ⟶ Xo.XF c), xF ≫ pullback.snd _ _ = spMap (algebraMap c.F L) → xF ≫ Y.j = spMap f ≫ M.hU.fromSpec → f.comp α = (algebraMap c.F L).comp (algebraMap O c.F) ∧ ∃ e ∈ es, f e ≠ 0 := by
  intro E _ _ _ H Dw l Xo c O _ _ _ _ _ Y M
  obtain ⟨α, h1, h2, -⟩ := (GlobalTheory.ModelPoints.model_points_charts E H Dw l Xo c O _ Y).2.2 M.U M.hU
  have := M.dom
  have := Y.flat
  have := Y.jQ_open
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have hg : IsOpenImmersion (X := Sp Γ(Y.X, M.U)) M.hU.fromSpec := inferInstanceAs (IsOpenImmersion M.hU.fromSpec)
  obtain ⟨es, h⟩ := chart_opens (A := Γ(Y.X, M.U)) Y.s M.hU.fromSpec α h1 h2
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) Y.jQ Y.jQ_dense Y.jQ_over
  exact ⟨α, es, h1, h2, h⟩

end GlobalTheory.Reg.ChartOpens
