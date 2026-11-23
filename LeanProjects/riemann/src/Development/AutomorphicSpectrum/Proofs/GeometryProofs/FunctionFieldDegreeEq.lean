import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIsMaximalOfIsFractionRing
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CurveSemiAbelianConjecture
import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LengthFormulaSumValuationsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingEssFiniteTypeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricNumberZeroFinrankStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsMultihomogPrimeOfPlaceStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogPrimeMemDivisorSupportStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.GeoDeg
open MvPolynomial GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing

local notation "T_eft" => GlobalTheory.T.local_ring_ess_finite_type
local notation "T_geo" => GlobalTheory.T.geometric_number_zero_finrank
local notation "T_ex1" => GlobalTheory.T.exists_multihomog_prime_of_place
local notation "T_ex2" => GlobalTheory.T.multihomog_prime_mem_divisor_support

section
variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)]
variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K]

theorem exists_centre (w : (Σ k, J k) → K) (hbir : Birational w) (hw : ∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) (v : Place (ZMod p) K) (k : B) (c : J k)
    (hc : w ⟨k, c⟩ ≠ 0) (hlt : v.valuation (w ⟨k, c⟩) < (Finset.univ.sup fun i => v.valuation (w ⟨k, i⟩))) :
    ∃ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), Dom v w W := by
  classical
  have hch : ∀ k', ∃ c' : J k', w ⟨k', c'⟩ ≠ 0 ∧ ∀ i, v.valuation (w ⟨k', i⟩) ≤ v.valuation (w ⟨k', c'⟩) := by
    intro k'
    obtain ⟨c0, h0⟩ := hw k'
    haveI : Nonempty (J k') := ⟨c0⟩
    obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun i => v.valuation (w ⟨k', i⟩)) Finset.univ_nonempty
    refine ⟨m, ?_, fun i => hm i (Finset.mem_univ i)⟩
    intro h
    have h1 := hm c0 (Finset.mem_univ _)
    simp only [h, map_zero] at h1
    exact ((Valuation.ne_zero_iff _).2 h0) (le_zero_iff.1 h1)
  choose c' hc1 hc2 using hch
  obtain ⟨W, hWp, hWh, hVW, hcW, hD, hiff⟩ := T_ex1 B J p K w v c' hc1 hc2
  have hx : (X ⟨k, c⟩ : MRing J) ∈ W := by
    rw [hiff (Pi.single k 1) _ (GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds.homog_X k c)]
    have hs : (Finset.univ.sup fun i => v.valuation (w ⟨k, i⟩)) = v.valuation (w ⟨k, c' k⟩) :=
      le_antisymm (Finset.sup_le fun i _ => hc2 k i)
        (Finset.le_sup (f := fun i => v.valuation (w ⟨k, i⟩)) (Finset.mem_univ _))
    rw [hs] at hlt
    simpa [Pi.single_apply, pow_ite, Finset.prod_ite_eq'] using hlt
  exact ⟨W, ⟨T_ex2 B J p K w hbir W c' hWp hWh hVW hcW k c hc hx, fun k' => ⟨c' k', hcW k'⟩⟩, hD⟩

open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds (homog_X fracHom fracHom_apply fracHom_eq_zero_iff isLocalRing mem_maximalIdeal_iff isUnit_iff)

theorem local_term (w : (Σ k, J k) → K) (hbir : Birational w) (k : B) (c : J k) (hc : w ⟨k, c⟩ ≠ 0)
    (W : Ideal (MRing J)) (hWd : W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩)) (c' : ∀ k, J k)
    (hc' : ∀ k, (X ⟨k, c' k⟩ : MRing J) ∉ W) (b : Fin 0 → B → ℤ) :
    (multAt (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c⟩ : MRing J)}) W : ℤ) * geoNum 0 W b =
      ∑ᶠ v ∈ {v : Place (ZMod p) K | Dom v w W}, (v.deg : ℤ) * v.ord (w ⟨k, c⟩ / w ⟨k, c' k⟩) := by
  classical
  have hV : (mCoordIdeal w).IsPrime := RingHom.ker_isPrime _
  have hVh : IsMultiHomogIdeal (mCoordIdeal w) := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal w
  have hVW : mCoordIdeal w ≤ W := le_trans le_sup_left hWd.1.1.2
  have hWp : W.IsPrime := hWd.1.1.1
  haveI := hV
  haveI := hWp
  obtain ⟨ρ, hρ⟩ := exists_rho w W hV hWp hVW
  haveI hloc : IsLocalRing (locRing (mCoordIdeal w) W) := isLocalRing hVW
  letI : Algebra (locRing (mCoordIdeal w) W) K := ρ.toAlgebra
  haveI hfr : IsFractionRing (locRing (mCoordIdeal w) W) K := hρ.isFractionRing hbir hV hWp hVW hc'
  have hpK : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have hpA : CharP (locRing (mCoordIdeal w) W) p :=
    (RingHom.charP_iff (algebraMap (locRing (mCoordIdeal w) W) K) (IsFractionRing.injective _ _) p).2 hpK
  letI : Algebra (ZMod p) (locRing (mCoordIdeal w) W) := ZMod.algebra _ p
  haveI : IsScalarTower (ZMod p) (locRing (mCoordIdeal w) W) K :=
    IsScalarTower.of_algebraMap_eq fun x =>
      DFunLike.congr_fun (Subsingleton.elim (algebraMap (ZMod p) K)
        ((algebraMap (locRing (mCoordIdeal w) W) K).comp (algebraMap (ZMod p) (locRing (mCoordIdeal w) W)))) x
  haveI hE : Algebra.EssFiniteType (ZMod p) (locRing (mCoordIdeal w) W) :=
    T_eft B J p K w W c' hV hWp hVW hc'
  haveI hN : IsNoetherianRing (locRing (mCoordIdeal w) W) := Algebra.EssFiniteType.isNoetherianRing (ZMod p) _
  have hs : IsMultiHomog (X ⟨k, c⟩ : MRing J) (Pi.single k 1) := homog_X k c
  have ht : IsMultiHomog (X ⟨k, c' k⟩ : MRing J) (Pi.single k 1) := homog_X k (c' k)
  have hsV : (X ⟨k, c⟩ : MRing J) ∉ mCoordIdeal w := fun h => hc ((X_mem_iff w k c).1 h)
  have hproj : IsMultiProjPrime (mCoordIdeal w) :=
    ⟨hV, hVh, fun k => ⟨c' k, fun h => hc' k (hVW h)⟩⟩
  have ht0 : fracHom (mCoordIdeal w) (X ⟨k, c' k⟩) ≠ 0 := fun h => hc' k (hVW (fracHom_eq_zero_iff.1 h))
  have hy : (fracHom (mCoordIdeal w) (X ⟨k, c⟩) / fracHom (mCoordIdeal w) (X ⟨k, c' k⟩)) *
      fracHom (mCoordIdeal w) (X ⟨k, c' k⟩) = fracHom (mCoordIdeal w) (X ⟨k, c⟩) := div_mul_cancel₀ _ ht0
  obtain ⟨hym, hlen⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.regularityDehomogenization_holds B J (mCoordIdeal w) (X ⟨k, c⟩) (X ⟨k, c' k⟩)
    (Pi.single k 1) W _ hproj hs hsV hWd ht (hc' k) hy
  set f : locRing (mCoordIdeal w) W := ⟨_, hym⟩ with hfdef
  have hf1 := hρ f _ _ _ hs ht (hc' k) hy
  have hne : w ⟨k, c' k⟩ ≠ 0 := fun h => hc' k (hVW ((X_mem_iff w k _).2 h))
  have hf2 : ρ f = w ⟨k, c⟩ / w ⟨k, c' k⟩ := by
    rw [eq_div_iff hne]
    simpa using hf1
  have hf0 : f ≠ 0 := by
    intro h
    rw [h, map_zero] at hf2
    exact div_ne_zero hc hne hf2.symm
  have hxW : (X ⟨k, c⟩ : MRing J) ∈ W := hWd.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  have hnf : ¬ IsField (locRing (mCoordIdeal w) W) := by
    intro hF
    have hu : IsUnit f := by
      obtain ⟨g, hg⟩ := hF.mul_inv_cancel hf0
      exact IsUnit.of_mul_eq_one _ hg
    exact ((isUnit_iff hVW f hs ht (hc' k) hy).1 hu) hxW
  have key := GlobalTheory.T.length_formula_sum_valuations (ZMod p) K (locRing (mCoordIdeal w) W) hnf f hf0
  have hset : {v : Place (ZMod p) K | (∀ a : locRing (mCoordIdeal w) W, v.valuation (algebraMap _ K a) ≤ 1) ∧
      ∀ a ∈ maximalIdeal (locRing (mCoordIdeal w) W), v.valuation (algebraMap _ K a) < 1} =
      {v : Place (ZMod p) K | Dom v w W} := by
    ext v
    exact hρ.dom_iff hV hWp hVW v
  rw [hset] at key
  rw [hlen, locIdeal_eq_span hym, T_geo B J p K w hbir k c hc W hWd b]
  have : (algebraMap (locRing (mCoordIdeal w) W) K f) = w ⟨k, c⟩ / w ⟨k, c' k⟩ := hf2
  rw [this] at key
  rw [← key]
  push_cast
  rfl

theorem block_sum (local_term : ∀ (w : (Σ k, J k) → K), Birational w → ∀ (k : B) (c : J k), w ⟨k, c⟩ ≠ 0 →
      ∀ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), ∀ c' : ∀ k, J k, (∀ k, (X ⟨k, c' k⟩ : MRing J) ∉ W) → ∀ b : Fin 0 → B → ℤ,
      (multAt (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c⟩ : MRing J)}) W : ℤ) * geoNum 0 W b =
        ∑ᶠ v ∈ {v : Place (ZMod p) K | Dom v w W}, (v.deg : ℤ) * v.ord (w ⟨k, c⟩ / w ⟨k, c' k⟩))
    (exists_centre : ∀ (w : (Σ k, J k) → K), Birational w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → ∀ (v : Place (ZMod p) K) (k : B) (c : J k),
      w ⟨k, c⟩ ≠ 0 → v.valuation (w ⟨k, c⟩) < (Finset.univ.sup fun i => v.valuation (w ⟨k, i⟩)) →
      ∃ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), Dom v w W)
    (w : (Σ k, J k) → K) (hbir : Birational w) (hw : ∀ k, ∃ c, w ⟨k, c⟩ ≠ 0)
    (hfin : ∀ x : K, x ≠ 0 → {v : Place (ZMod p) K | v.valuation x ≠ 1}.Finite)
    (hprod : ∀ x : K, x ≠ 0 → ∑ᶠ v : Place (ZMod p) K, (v.deg : ℤ) * WithZero.log (v.valuation x) = 0)
    (k : B) (c : J k) (hc : w ⟨k, c⟩ ≠ 0) (b : Fin 0 → B → ℤ) :
    ∑ᶠ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩),
        (multAt (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c⟩ : MRing J)}) W : ℤ) * geoNum 0 W b =
      ∑ᶠ v : Place (ZMod p) K, (v.deg : ℤ) * WithZero.log (Finset.univ.sup fun i => v.valuation (w ⟨k, i⟩)) := by
  classical
  have hV : (mCoordIdeal w).IsPrime := RingHom.ker_isPrime _
  have hVh : IsMultiHomogIdeal (mCoordIdeal w) := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal w
  set S : Place (ZMod p) K → WithZero (Multiplicative ℤ) := fun v => Finset.univ.sup fun i => v.valuation (w ⟨k, i⟩) with hSdef
  set f : Place (ZMod p) K → ℤ := fun v =>
    (v.deg : ℤ) * (WithZero.log (S v) - WithZero.log (v.valuation (w ⟨k, c⟩))) with hf
  set T : Set (Place (ZMod p) K) := {v | v.valuation (w ⟨k, c⟩) < S v} with hTdef
  have hle : ∀ v : Place (ZMod p) K, v.valuation (w ⟨k, c⟩) ≤ S v := fun v =>
    Finset.le_sup (f := fun i => v.valuation (w ⟨k, i⟩)) (Finset.mem_univ c)
  set U : Set (Place (ZMod p) K) := ⋃ j ∈ {j : J k | w ⟨k, j⟩ ≠ 0}, {v | v.valuation (w ⟨k, j⟩) ≠ 1} with hUdef
  have hU : U.Finite := (Set.toFinite _).biUnion fun j hj => hfin _ hj
  have h1 : ∀ v ∉ U, ∀ j, w ⟨k, j⟩ ≠ 0 → v.valuation (w ⟨k, j⟩) = 1 := by
    intro v hv j hj
    by_contra h
    exact hv (Set.mem_biUnion (show j ∈ {j : J k | w ⟨k, j⟩ ≠ 0} from hj) h)
  have hS1 : ∀ v ∉ U, S v = 1 := by
    intro v hv
    apply le_antisymm
    · refine Finset.sup_le fun i _ => ?_
      by_cases hi : w ⟨k, i⟩ = 0
      · simp [hi]
      · exact (h1 v hv i hi).le
    · calc 1 = v.valuation (w ⟨k, c⟩) := (h1 v hv c hc).symm
        _ ≤ S v := hle v
  have hTU : T ⊆ U := by
    intro v hv
    by_contra hvU
    have h2 : S v = 1 := hS1 v hvU
    have h3 := h1 v hvU c hc
    have h4 : v.valuation (w ⟨k, c⟩) < S v := hv
    rw [h2, h3] at h4
    exact lt_irrefl _ h4
  have hTfin : T.Finite := hU.subset hTU
  have hmain : ∀ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩),
      (multAt (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c⟩ : MRing J)}) W : ℤ) * geoNum 0 W b =
        ∑ᶠ v ∈ {v : Place (ZMod p) K | Dom v w W}, f v := by
    intro W hW
    choose c' hc' using hW.2
    rw [local_term w hbir k c hc W hW c' hc' b]
    refine finsum_mem_congr rfl fun v hv => ?_
    have hVW : mCoordIdeal w ≤ W := le_trans le_sup_left hW.1.1.2
    have hne : w ⟨k, c' k⟩ ≠ 0 := fun h => hc' k (hVW ((X_mem_iff w k _).2 h))
    have hsup : S v = v.valuation (w ⟨k, c' k⟩) := Dom.sup_eq hv hc' k
    simp only [hf, hsup]
    rw [v.ord_div hc hne]
    simp only [Place.ord]
    ring
  have hset : ∀ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), {v : Place (ZMod p) K | Dom v w W} ⊆ T := by
    intro W hW v hv
    choose c' hc' using hW.2
    have hx : (X ⟨k, c⟩ : MRing J) ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have h2 : S v = v.valuation (w ⟨k, c' k⟩) := Dom.sup_eq hv hc' k
    show v.valuation (w ⟨k, c⟩) < S v
    rw [h2]
    exact Dom.lt_chart hv hc' k hx
  have hcover : T ⊆ ⋃ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), {v : Place (ZMod p) K | Dom v w W} := by
    intro v hv
    obtain ⟨W, hW, hD⟩ := exists_centre w hbir hw v k c hc hv
    exact Set.mem_biUnion hW hD
  have hdisj : (divSupp (mCoordIdeal w) (X ⟨k, c⟩)).PairwiseDisjoint
      (fun W => {v : Place (ZMod p) K | Dom v w W}) := by
    intro W hW W' hW' hne
    refine Set.disjoint_left.2 fun v hv hv' => hne (le_antisymm ?_ ?_)
    · choose c' hc' using hW.2
      exact Dom.le_of_dom hv hv' (isMultiHomogIdeal_of_mem_minimalPrimes hVh
        (GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds.homog_X k c) hW.1) hW.1.1.1 hc'
    · choose c' hc' using hW'.2
      exact Dom.le_of_dom hv' hv (isMultiHomogIdeal_of_mem_minimalPrimes hVh
        (GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds.homog_X k c) hW'.1) hW'.1.1.1 hc'
  have hsupp : T ∩ Function.support f = Set.univ ∩ Function.support f := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_univ, true_and, and_iff_right_iff_imp]
    intro hv
    by_contra hvT
    have h2 : S v = v.valuation (w ⟨k, c⟩) := le_antisymm (not_lt.1 hvT) (hle v)
    exact hv (by simp [hf, h2])
  have hF1 : (Function.support fun v : Place (ZMod p) K => (v.deg : ℤ) * WithZero.log (S v)).Finite := by
    refine hU.subset fun v hv => ?_
    by_contra hvU
    exact hv (by simp [hS1 v hvU])
  have hF2 : (Function.support fun v : Place (ZMod p) K => (v.deg : ℤ) * WithZero.log (v.valuation (w ⟨k, c⟩))).Finite := by
    refine (hfin _ hc).subset fun v hv => ?_
    intro h
    exact hv (by simp [h])
  calc _ = ∑ᶠ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), ∑ᶠ v ∈ {v : Place (ZMod p) K | Dom v w W}, f v :=
        finsum_mem_congr rfl hmain
    _ = ∑ᶠ v ∈ ⋃ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), {v : Place (ZMod p) K | Dom v w W}, f v :=
        (finsum_mem_biUnion hdisj (divSupp_finite _ _) fun W hW => hTfin.subset (hset W hW)).symm
    _ = ∑ᶠ v ∈ T, f v := by
        rw [Set.Subset.antisymm (Set.iUnion₂_subset hset) hcover]
    _ = ∑ᶠ v ∈ (Set.univ : Set (Place (ZMod p) K)), f v := finsum_mem_inter_support_eq f _ _ hsupp
    _ = ∑ᶠ v, f v := finsum_mem_univ f
    _ = ∑ᶠ v : Place (ZMod p) K, ((v.deg : ℤ) * WithZero.log (S v) - (v.deg : ℤ) * WithZero.log (v.valuation (w ⟨k, c⟩))) :=
        finsum_congr fun v => by simp only [hf]; ring
    _ = _ := by
        rw [finsum_sub_distrib hF1 hF2, hprod _ hc, sub_zero]

theorem degree_of_local (local_term : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K), Birational w → ∀ (k : B) (c : J k), w ⟨k, c⟩ ≠ 0 →
      ∀ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), ∀ c' : ∀ k, J k, (∀ k, (X ⟨k, c' k⟩ : MRing J) ∉ W) → ∀ b : Fin 0 → B → ℤ,
      (multAt (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c⟩ : MRing J)}) W : ℤ) * geoNum 0 W b =
        ∑ᶠ v ∈ {v : Place (ZMod p) K | Dom v w W}, (v.deg : ℤ) * v.ord (w ⟨k, c⟩ / w ⟨k, c' k⟩))
    (exists_centre : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K), Birational w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → ∀ (v : Place (ZMod p) K) (k : B) (c : J k),
      w ⟨k, c⟩ ≠ 0 → v.valuation (w ⟨k, c⟩) < (Finset.univ.sup fun i => v.valuation (w ⟨k, i⟩)) →
      ∃ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), Dom v w W) :
    ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [GroundTheory.FunctionField.IsFunctionField (ZMod p) K] (C : ACurve K) (w : (Σ k, J k) → K) (a : B → ℤ), IsFFCurve (ZMod p) C → Birational w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → geoNum 1 (mCoordIdeal w) (fun _ => a) = coordDeg C w a := by
  intro B _ J _ p _ K _ _ _ C w a hC hbir hw
  classical
  obtain ⟨e, he⟩ := hC
  have hfin : ∀ x : K, x ≠ 0 → {v : Place (ZMod p) K | v.valuation x ≠ 1}.Finite := by
    intro x hx
    refine ((C.fin x hx).image e).subset fun v hv => ⟨e.symm v, ?_, by simp⟩
    have := (he (e.symm v)).1
    simp only [Equiv.apply_symm_apply] at this
    simpa [this] using hv
  have hprod : ∀ x : K, x ≠ 0 → ∑ᶠ v : Place (ZMod p) K, (v.deg : ℤ) * WithZero.log (v.valuation x) = 0 := by
    intro x hx
    rw [← C.prod x hx, ← finsum_comp_equiv e]
    refine finsum_congr fun i => ?_
    rw [(he i).1, (he i).2]
  have hrel : IsRelevant (mCoordIdeal w) := fun k => by
    obtain ⟨c, hc⟩ := hw k
    exact ⟨c, fun h => hc ((X_mem_iff w k c).1 h)⟩
  show geoNum (0 + 1) (mCoordIdeal w) (fun _ => a) = _
  rw [geoNum, dif_pos hrel, coordDeg]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hck : w ⟨k, (hrel k).choose⟩ ≠ 0 := fun h => (hrel k).choose_spec ((X_mem_iff w k _).2 h)
  rw [block_sum (local_term B J p K) (exists_centre B J p K) w hbir hw hfin hprod k _ hck, ← finsum_comp_equiv e]
  congr 1
  refine finsum_congr fun i => ?_
  simp only [(he i).1, (he i).2]

theorem geoNum_one_eq_coordDeg : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [GroundTheory.FunctionField.IsFunctionField (ZMod p) K] (C : ACurve K) (w : (Σ k, J k) → K) (a : B → ℤ), IsFFCurve (ZMod p) C → Birational w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → geoNum 1 (mCoordIdeal w) (fun _ => a) = coordDeg C w a :=
  degree_of_local (fun _ _ _ _ _ _ _ _ _ _ w hbir k c hc W hW c' hc' b => local_term w hbir k c hc W hW c' hc' b)
    (fun _ _ _ _ _ _ _ _ _ _ w hbir hw v k c hc hlt => exists_centre w hbir hw v k c hc hlt)

end
end GlobalTheory.CompanionTheory.Ar.GeoDeg
