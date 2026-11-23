import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnivChartOfStandardSmooth
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLieCoordinatesLieMultIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmTypeEigenMultiplicityOfDensePrimesStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.DetSpread

theorem exists_factor {S : Scheme.{0}} {R K : Type} [CommRing R] [Field K] (j : Sp R ⟶ S) [IsOpenImmersion j]
    (x : Sp K ⟶ S) (q : PrimeSpectrum R) (y : Sp K) (hy : x y = j q) :
    ∃ f : R →+* K, spMap f ≫ j = x ∧ RingHom.ker f = q.asIdeal := by
  have hsub : Set.range x ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    exact ⟨q, by rw [← hy, Subsingleton.elim z y]⟩
  have hx : IsOpenImmersion.lift j x hsub ≫ j = x := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg⟩ := Spec.map_surjective (IsOpenImmersion.lift j x hsub)
  rw [← hg] at hx
  have hq : Spec.map g y = q := by
    apply j.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hx, hy]
  refine ⟨g.hom, hx, ?_⟩
  rw [← hq]
  have hy0 : PrimeSpectrum.asIdeal y = ⊥ := by
    rcases Ideal.eq_bot_or_top (PrimeSpectrum.asIdeal (R := K) y) with e | e
    · exact e
    · exact absurd e (PrimeSpectrum.isPrime y).ne_top
  change _ = Ideal.comap g.hom (PrimeSpectrum.asIdeal y)
  rw [hy0]
  rfl

theorem eq_comp_of_spMap {S : Scheme.{0}} {o R K : Type} [CommRing o] [CommRing R] [CommRing K]
    {j : Sp R ⟶ S} {s : S ⟶ Sp o} {δ : o →+* R} (hδ : j ≫ s = spMap δ) {f : R →+* K} {β : o →+* K}
    (h : (spMap f ≫ j) ≫ s = spMap β) (a : o) : β a = f (δ a) := by
  rw [Category.assoc, hδ] at h
  have h' : CommRingCat.ofHom δ ≫ CommRingCat.ofHom f = CommRingCat.ofHom β :=
    Spec.map_injective ((Spec.map_comp _ _).trans h)
  exact (congrArg (fun z => z.hom a) h').symm

theorem detCond_of_basis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OAct (𝓞 E) G) {o : Type} [CommRing o] (s : S ⟶ Sp o) (ρ : o)
    (hρ : ρ ^ 2 = -(H.d : o))
    (hd : Dense {p : S | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S)
      (β : o →+* K), p ∈ Set.range x ∧ x ≫ s = spMap β ∧ DetCond D act x (β ρ)})
    {R : Type} [CommRing R] [IsReduced R] (j : Sp R ⟶ S) [IsOpenImmersion j]
    {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] (act' : OAct (𝓞 E) G') (hs : Smooth G'.hom)
    {n : ℕ} (v : Fin n → (epsR R ⟶ G')) (hv : IsLieBasis v)
    (h : ∀ (K : Type) [Field K] (y : Sp K ⟶ Sp R) (τ : 𝓞 E →+* K) (N : ℕ),
      LieMult act' y τ N ↔ LieMult act (y ≫ j) τ N)
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (f : R →+* K) (β : o →+* K)
    (hβ : (spMap f ≫ j) ≫ s = spMap β) : DetCond D act (spMap f ≫ j) (β ρ) := by
  obtain ⟨δ₀, hδ₀⟩ := Spec.map_surjective (j ≫ s)
  have hδ : j ≫ s = spMap δ₀.hom := hδ₀.symm
  obtain ⟨M, hM⟩ := GlobalTheory.exists_lie_coordinates_lieMult_iff (𝓞 E) R G' act' n v hs hv
  obtain ⟨M', hM', e⟩ := hM K f
  have hr : (δ₀.hom ρ) ^ 2 = -(H.d : R) := by
    have := congrArg δ₀.hom hρ
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  have main := GlobalTheory.T.cmType_eigenMultiplicity_of_dense_primes E H D.p D.q n R M (δ₀.hom ρ) hr (by
    refine (hd.preimage j.isOpenEmbedding.isOpenMap).mono ?_
    rintro q ⟨L, _, _, _, x, β', ⟨y, hy⟩, hx, hdet⟩
    obtain ⟨g, rfl, hg⟩ := exists_factor j x q y hy
    obtain ⟨N', hN', e'⟩ := hM L g
    refine ⟨L, inferInstance, inferInstance, inferInstance, g, N', hg, hN', fun τ => ?_⟩
    rw [← e', ← e', h, h, ← eq_comp_of_spMap hδ hx]
    exact hdet τ) K f M' hM'
  intro τ
  rw [← h, ← h, e, e, eq_comp_of_spMap hδ hβ]
  exact main τ

theorem detCond_of_dense : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) [IsReduced S] (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (act : OAct (𝓞 E) G) (o : Type) [CommRing o] (s : S ⟶ Sp o) (ρ : o), SmoothOfRelativeDimension g G.hom → ρ ^ 2 = -(H.d : o) → Dense {p : S | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S) (β : o →+* K), p ∈ Set.range x ∧ x ≫ s = spMap β ∧ DetCond D act x (β ρ)} → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : Sp K ⟶ S) (β : o →+* K), x ≫ s = spMap β → DetCond D act x (β ρ) := by
  intro E _ _ _ H D S _ G _ _ g act o _ s ρ hg hρ hd K _ _ _ x β hβ
  let y : Sp K := (default : PrimeSpectrum K)
  obtain ⟨U, hU, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := x y) trivial
  let j : Sp Γ(S, U) ⟶ S := hU.fromSpec
  have : IsOpenImmersion j := hU.isOpenImmersion_fromSpec
  obtain ⟨q, hq⟩ : x y ∈ Set.range j := hU.range_fromSpec.ge hs
  have hg₁ : SmoothOfRelativeDimension g ((Over.pullback j).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg
  obtain ⟨r, hr, v, hv⟩ := GlobalTheory.LieLoc.lie_locally_free Γ(S, U) ((Over.pullback j).obj G) g hg₁ q
  let a : Sp (Localization.Away r) ⟶ Sp Γ(S, U) := spMap (algebraMap Γ(S, U) (Localization.Away r))
  have : IsOpenImmersion a := IsOpenImmersion.of_isLocalization r
  obtain ⟨q', hq'⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap Γ(S, U) (Localization.Away r))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  obtain ⟨f, rfl, -⟩ := exists_factor (a ≫ j) x q' y (by
    rw [← hq, ← hq']
    rfl)
  obtain ⟨a₁, h₁⟩ := GlobalTheory.DetExtend.exists_oAct_pullback j act
  obtain ⟨a₂, h₂⟩ := GlobalTheory.DetExtend.exists_oAct_pullback a a₁
  have hg₂ : SmoothOfRelativeDimension g ((Over.pullback a).obj ((Over.pullback j).obj G)).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg₁
  refine detCond_of_basis D act s ρ hρ hd (a ≫ j) a₂ (SmoothOfRelativeDimension.smooth g _) v hv
    (fun L _ z τ N => ?_) K f β hβ
  rw [LiePull.lieMult_pull _ _ _ _ _ a _ a₁ a₂ (isGrpPullback_pullback _ a)
    (fun c => by rw [h₂]; exact pullback.lift_fst _ _ _) L z τ N,
    LiePull.lieMult_pull _ _ _ _ _ j _ act a₁ (isGrpPullback_pullback _ j)
    (fun c => by rw [h₁]; exact pullback.lift_fst _ _ _) L (z ≫ a) τ N, Category.assoc]

end GlobalTheory.DetSpread
