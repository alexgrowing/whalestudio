import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecJets4
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalBasisDescription
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegers
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM GlobalTheory.CM.LieGlue

noncomputable section
namespace GlobalTheory.LieHt.SemiFib

theorem smoothDim_model {K : Type} [Field K] [NumberField K] (F : SemiFib K) :
    SmoothOfRelativeDimension F.P₀.g F.G.hom := by
  have := F.semi.smooth
  have := F.semi.geomConnected
  have : ConnectedSpace F.G.left := GeometricallyConnected.connectedSpace F.G.hom F.G.hom.isOpenMap
  let x : F.P₀.A.left := eSec F.P₀.A (default : PrimeSpectrum K)
  obtain ⟨n, hn⟩ := exists_dim_of_preconnected F.G.hom (F.φ.base x)
  have hn' : SmoothOfRelativeDimension n F.P₀.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback F.fib.1 hn
  rw [ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ F.P₀.smoothDim hn' x]
  exact hn

theorem exists_cover_lieLat {K : Type} [Field K] [NumberField K] (F : SemiFib K) :
    ∃ (n : ℕ) (r : Fin n → 𝓞 K) (M : Fin n → Matrix (Fin F.P₀.g) (Fin F.P₀.g) K),
      Ideal.span (Set.range r) = ⊤ ∧ (∀ i, r i ≠ 0 ∧ (M i).det ≠ 0) ∧
      ∀ c, c ∈ F.lieLat ↔ ∀ i, ∃ (k : ℕ) (a : Fin F.P₀.g → 𝓞 K), r i ^ k • c = ∑ j, a j • M i j := by
  have := F.semi.comm
  have := F.semi.separated
  have := F.P₀.isAb.comm
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective _ _
  obtain ⟨n, r, hr, hQ⟩ := exists_finite_cover _
    (GlobalTheory.LieLoc.lie_locally_free (𝓞 K) F.G F.P₀.g F.smoothDim_model)
  choose hr0 e he using hQ
  have hu : ∀ i, IsUnit (algebraMap (𝓞 K) K (r i)) := fun i => ((map_ne_zero_iff _ hinj).2 (hr0 i)).isUnit
  let g : ∀ i, Localization.Away (r i) →+* K := fun i => IsLocalization.Away.lift (r i) (hu i)
  have hg : ∀ i, (g i).comp (algebraMap (𝓞 K) _) = algebraMap (𝓞 K) K := fun i => IsLocalization.Away.lift_comp _ _
  have hφ := fun i => isGrpPullback_pullback F.G (spMap (algebraMap (𝓞 K) (Localization.Away (r i))))
  have hcomm := fun i => PolPull.isCommMonObj_of_isGrpPullback (hφ i)
  have hsm := fun i => MorphismProperty.of_isPullback (P := @Smooth) (hφ i).1 F.semi.smooth
  choose ψ hψφ hψ using fun i => exists_lift (hg i) (hφ i) F.fib
  choose M hdet hM using fun i => exists_matrix (hψ i) (hsm i) (he i) F.basis
  have alg := LieComb.lieComb_algebra K F.P₀.A _ F.v F.basis.1
  refine ⟨n, r, M, hr, fun i => ⟨hr0 i, hdet i⟩, fun c => ?_⟩
  simp only [← fun i => exists_comb_iff (r i) (g i) (hg i) (M i) c]
  constructor
  · intro hc i
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨u, hu, w, hw, hc⟩ := hc
      obtain ⟨t, ht, -⟩ := existsUnique_isVecOver (f := algebraMap (𝓞 K) (Localization.Away (r i)))
        (A' := (Over.pullback (spMap (algebraMap (𝓞 K) (Localization.Away (r i))))).obj F.G) (hφ i).1 u
      obtain ⟨a, ha, -⟩ := (he i).2 t (ht.isTangent (hφ i) hu)
      have h := EllComp.isVecOver_cancel (hφ i).1 (hψ i).1 ht (by rw [hg, hψφ]; exact hw)
      exact ⟨a, (F.basis.2 w (alg.2.1 _ _ hc)).unique hc ((isVecOver_iff (hψ i) F.basis (hM i) ha w).1 h)⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by simp [add_smul, Finset.sum_add_distrib]⟩
    | smul s x _ hx =>
      obtain ⟨a, rfl⟩ := hx
      refine ⟨fun j => algebraMap (𝓞 K) _ s * a j, ?_⟩
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, mul_smul, ← RingHom.comp_apply, hg, algebraMap_smul]
  · intro hc
    choose a ha using hc
    obtain ⟨w, hw, -⟩ := alg.1 c
    choose t ht using fun i => ((LieComb.lieComb_algebra _ _ _ (e i) (he i).1).1 (a i)).exists
    have hwt : ∀ i, IsVecOver (g i) (ψ i) (t i) w := fun i =>
      (isVecOver_iff (hψ i) F.basis (hM i) (ht i) w).2 (ha i ▸ hw)
    obtain ⟨u, hu⟩ := exists_glue _ hinj r hr g hg (w.left ≫ F.φ) (fun i => (t i).left ≫ pullback.fst _ _)
      (fun i => by rw [Category.assoc, (hφ i).1.w, ← Category.assoc, Over.w])
      (fun i => by rw [← Category.assoc, ← hwt i, Category.assoc, hψφ])
    exact Submodule.subset_span
      ⟨u, isTangent_of_isVecOver hinj F.fib hu.symm (alg.2.1 _ _ hw), w, hu.symm, hw⟩

theorem full_lieLat : ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K), Full F.lieLat := by
  intro K _ _ F
  obtain ⟨n, r, M, hr, hM, hL⟩ := F.exists_cover_lieLat
  exact GlobalTheory.CM.LieLattice.fg_and_span_eq_top F.lieLat r M hr (fun i => (hM i).2) hL

end GlobalTheory.LieHt.SemiFib
