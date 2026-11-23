import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIsMaximalOfIsFractionRing
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoDeg

open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointChart (chartMono_notMem)
open GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionsNonzero (chartMono isMultiHomog_chartMono aeval_chartMono)
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds (homog_X mem_locRing_iff div_mem_locRing fracHom fracHom_eq_zero_iff isUnit_iff)

theorem aeval_ratio_mul_chartMono {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    (φ : MRing J →+* Ω) (c : ∀ k, J k) (hc : ∀ k, φ (X ⟨k, c k⟩) ≠ 0) (S : Subring Ω) (x : (Σ k, J k) → S)
    (hx : ∀ q, (x q : Ω) = φ (X q) / φ (X ⟨q.1, c q.1⟩)) {g : MRing J} {e : B → ℕ} (hg : IsMultiHomog g e) :
    ((aeval x g : S) : Ω) * φ (chartMono c e) = φ g := by
  classical
  let ψ : MRing J →+* Ω := S.subtype.comp (aeval x : MRing J →ₐ[ℤ] S).toRingHom
  have hψX : ∀ q, ψ (X q) = φ (X q) / φ (X ⟨q.1, c q.1⟩) := fun q => by
    show ((aeval x (X q) : S) : Ω) = _
    rw [aeval_X]
    exact hx q
  have hψC : ∀ a : ℤ, ψ (C a) = φ (C a) := fun a =>
    RingHom.congr_fun (RingHom.ext_int (ψ.comp C) (φ.comp C)) a
  show ψ g * φ (chartMono c e) = φ g
  rw [g.as_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∀ k, ∑ i, m ⟨k, i⟩ = e k := hg m hm
  have hchart : φ (chartMono c e) = ∏ q : (Σ k, J k), φ (X ⟨q.1, c q.1⟩) ^ m q := by
    rw [Fintype.prod_sigma]
    simp only [Finset.prod_pow_eq_pow_sum, hdeg]
    show φ (∏ k, X ⟨k, c k⟩ ^ e k) = _
    rw [map_prod]
    simp only [map_pow]
  have hne : ∏ q : (Σ k, J k), φ (X ⟨q.1, c q.1⟩) ^ m q ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun q _ => pow_ne_zero _ (hc q.1)
  rw [hchart, monomial_eq, map_mul, map_mul, hψC, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [map_prod, map_pow, hψX, div_pow, Finset.prod_div_distrib]
  rw [mul_assoc, div_mul_cancel₀ _ hne]

theorem essFiniteType_locRing : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime]
    (K : Type) [Field K] (w : (Σ k, J k) → K) (W : Ideal (MRing J)) (c : ∀ k, J k),
    (mCoordIdeal w).IsPrime → W.IsPrime → mCoordIdeal w ≤ W → (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) →
    ∀ [Algebra (ZMod p) (locRing (mCoordIdeal w) W)],
      Algebra.EssFiniteType (ZMod p) (locRing (mCoordIdeal w) W) := by
  intro B _ J _ p _ K _ w W c hP hW hle hcW _
  classical
  haveI : (mCoordIdeal w).IsPrime := hP
  haveI : W.IsPrime := hW
  have hXP : ∀ k, fracHom (mCoordIdeal w) (X ⟨k, c k⟩) ≠ 0 := fun k h =>
    hcW k (hle (fracHom_eq_zero_iff.1 h))
  have hchartP : ∀ a : B → ℕ, fracHom (mCoordIdeal w) (chartMono c a) ≠ 0 := fun a h =>
    chartMono_notMem hW hcW a (hle (fracHom_eq_zero_iff.1 h))
  let xS : (Σ k, J k) → locRing (mCoordIdeal w) W := fun q =>
    ⟨fracHom (mCoordIdeal w) (X q) / fracHom (mCoordIdeal w) (X ⟨q.1, c q.1⟩),
      div_mem_locRing hle (homog_X q.1 q.2) (homog_X q.1 (c q.1)) (hcW q.1)⟩
  let s : Finset (locRing (mCoordIdeal w) W) := Finset.univ.image xS
  have hsub : Set.range xS ⊆ (s : Set (locRing (mCoordIdeal w) W)) := by
    rintro _ ⟨q, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem xS (Finset.mem_univ q))
  have hmem : ∀ g : MRing J, aeval xS g ∈ Algebra.adjoin (ZMod p) (s : Set (locRing (mCoordIdeal w) W)) := by
    intro g
    refine Algebra.adjoin_mono hsub ?_
    induction g using MvPolynomial.induction_on
    next a =>
      rw [aeval_C, algebraMap_int_eq, Int.coe_castRingHom]
      exact intCast_mem _ a
    next f g hf hg =>
      rw [map_add]
      exact add_mem hf hg
    next f q hf =>
      rw [map_mul, aeval_X]
      exact mul_mem hf (Algebra.subset_adjoin ⟨q, rfl⟩)
  refine ⟨⟨s, ?_⟩⟩
  constructor
  constructor
  · intro y
    exact y.2
  · intro z
    obtain ⟨u, v, a, hu, hv, hvW, hz⟩ := (mem_locRing_iff hle).1 z.2
    have hA := aeval_ratio_mul_chartMono (fracHom (mCoordIdeal w)) c hXP _ xS (fun q => rfl) hu
    have hB := aeval_ratio_mul_chartMono (fracHom (mCoordIdeal w)) c hXP _ xS (fun q => rfl) hv
    have hBu : IsUnit (aeval xS v) :=
      (isUnit_iff hle (aeval xS v) hv (isMultiHomog_chartMono c a) (chartMono_notMem hW hcW a) hB).2 hvW
    refine ⟨(⟨aeval xS u, hmem u⟩, ⟨⟨aeval xS v, hmem v⟩, hBu⟩), ?_⟩
    apply Subtype.ext
    apply mul_right_cancel₀ (hchartP a)
    show ((z : FractionRing (MRing J ⧸ mCoordIdeal w)) * (aeval xS v : FractionRing (MRing J ⧸ mCoordIdeal w))) *
        fracHom (mCoordIdeal w) (chartMono c a) =
      (aeval xS u : FractionRing (MRing J ⧸ mCoordIdeal w)) * fracHom (mCoordIdeal w) (chartMono c a)
    rw [mul_assoc, hB, hA, hz]
  · intro x y h
    exact ⟨1, by rw [Subtype.ext h]⟩

end GlobalTheory.CompanionTheory.Ar.GeoDeg
