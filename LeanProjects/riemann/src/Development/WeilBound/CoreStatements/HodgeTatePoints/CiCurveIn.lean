import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CurveSemiAbelianConjecture
import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitIffUnitAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueCentreLocalHomStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuativeLiftExistsUniqueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePointStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.OfMem

set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Ci

section Alg

variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)]

def chartEval {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) (c : (k : B) → J k) : MRing J →ₐ[ℤ] Ω :=
  MvPolynomial.aeval fun q => y q / y ⟨q.1, c q.1⟩

theorem cone_step [DecidableEq B] {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) (c : (k : B) → J k)
    (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (q : Σ k, J k) :
    mConeMap y (MvPolynomial.X q * ∏ l ∈ Finset.univ.erase q.1, MvPolynomial.X ⟨l, c l⟩) =
      MvPolynomial.C (y q / y ⟨q.1, c q.1⟩) * mConeMap y (∏ l, MvPolynomial.X ⟨l, c l⟩) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ q.1), map_mul, map_mul, ← mul_assoc]
  congr 1
  simp only [mConeMap, MvPolynomial.aeval_X]
  rw [← mul_assoc, ← map_mul, div_mul_cancel₀ _ (hy _)]

theorem exists_homog {Ω K : Type} [Field Ω] [Field K] (y : (Σ k, J k) → Ω) (w : (Σ k, J k) → K)
    (c : (k : B) → J k) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (hw : ∀ k, w ⟨k, c k⟩ ≠ 0) (f : MRing J) :
    ∃ (N : ℕ) (g : MRing J),
      mConeMap y g = MvPolynomial.C (chartEval y c f) * mConeMap y (∏ l, MvPolynomial.X ⟨l, c l⟩) ^ N ∧
      mConeMap w g = MvPolynomial.C (chartEval w c f) * mConeMap w (∏ l, MvPolynomial.X ⟨l, c l⟩) ^ N := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨0, MvPolynomial.C a, by simp, by simp⟩
  | add f g hf hg =>
    obtain ⟨N, f', h1, h2⟩ := hf
    obtain ⟨M, g', h3, h4⟩ := hg
    refine ⟨N + M, f' * (∏ l, MvPolynomial.X ⟨l, c l⟩) ^ M + g' * (∏ l, MvPolynomial.X ⟨l, c l⟩) ^ N, ?_, ?_⟩
    · rw [map_add, map_mul, map_mul, map_pow, map_pow, h1, h3, map_add, map_add]; ring
    · rw [map_add, map_mul, map_mul, map_pow, map_pow, h2, h4, map_add, map_add]; ring
  | mul_X f q hf =>
    obtain ⟨N, f', h1, h2⟩ := hf
    refine ⟨N + 1, f' * (MvPolynomial.X q * ∏ l ∈ Finset.univ.erase q.1, MvPolynomial.X ⟨l, c l⟩), ?_, ?_⟩
    · rw [map_mul, cone_step y c hy, h1, map_mul, map_mul, chartEval, MvPolynomial.aeval_X]; ring
    · rw [map_mul, cone_step w c hw, h2, map_mul, map_mul, chartEval, MvPolynomial.aeval_X]; ring

theorem cone_X_eq_zero {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) (q : Σ k, J k) :
    mConeMap y (MvPolynomial.X q) = 0 ↔ y q = 0 := by
  simp [mConeMap]

theorem ne_zero_of_le {Ω K : Type} [Field Ω] [Field K] {y : (Σ k, J k) → Ω} {w : (Σ k, J k) → K}
    (h : mCoordIdeal y ≤ mCoordIdeal w) {q : Σ k, J k} (hq : w q ≠ 0) : y q ≠ 0 := fun h0 =>
  hq ((cone_X_eq_zero w q).1 (h ((cone_X_eq_zero y q).2 h0)))

theorem chartEval_ker {Ω K : Type} [Field Ω] [Field K] {y : (Σ k, J k) → Ω} {w : (Σ k, J k) → K}
    (h : mCoordIdeal y ≤ mCoordIdeal w) (c : (k : B) → J k) (hw : ∀ k, w ⟨k, c k⟩ ≠ 0) (f : MRing J)
    (hf : chartEval y c f = 0) : chartEval w c f = 0 := by
  obtain ⟨N, g, h1, h2⟩ := exists_homog y w c (fun k => ne_zero_of_le h (hw k)) hw f
  rw [hf, map_zero, zero_mul] at h1
  have h3 : mConeMap w g = 0 := h h1
  rw [h2, mul_eq_zero] at h3
  rcases h3 with h3 | h3
  · exact MvPolynomial.C_eq_zero.1 h3
  · have h4 := pow_eq_zero_iff'.1 h3
    rw [map_prod, Finset.prod_eq_zero_iff] at h4
    obtain ⟨⟨k, -, hk⟩, -⟩ := h4
    exact absurd ((cone_X_eq_zero w _).1 hk) (hw k)

omit [∀ k, Fintype (J k)] in
theorem segre_update [DecidableEq B] {Ω : Type} [Field Ω] {y : (Σ k, J k) → Ω} {c : (k : B) → J k}
    (h0 : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : B) (j : J k) :
    segre y (Function.update c k j) / segre y c = y ⟨k, j⟩ / y ⟨k, c k⟩ := by
  rw [Conj.segre, Conj.segre, ← Finset.prod_div_distrib, Finset.prod_eq_single k (fun l _ hl => by
    rw [Function.update_of_ne hl, div_self (h0 l)]) (by simp), Function.update_self]

theorem exists_chart_hom {Ω K : Type} [Field Ω] [Field K] {y : (Σ k, J k) → Ω} {w : (Σ k, J k) → K}
    (h : mCoordIdeal y ≤ mCoordIdeal w) (c : (k : B) → J k) (hw : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    ∃ ψ : Algebra.adjoin ℤ (Set.range fun j => segre y j / segre y c) →+* K,
      ∀ k j, ∃ hm, ψ ⟨y ⟨k, j⟩ / y ⟨k, c k⟩, hm⟩ = w ⟨k, j⟩ / w ⟨k, c k⟩ := by
  classical
  have hle : Algebra.adjoin ℤ (Set.range fun j => segre y j / segre y c) ≤ (chartEval y c).range := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    refine ⟨∏ k, MvPolynomial.X ⟨k, j k⟩, ?_⟩
    simp [chartEval, Conj.segre]
  let π := (chartEval y c).rangeRestrict.toRingHom
  have hπ : Function.Surjective π := (chartEval y c).rangeRestrict_surjective
  let ψ' := π.liftOfSurjective hπ ⟨(chartEval w c).toRingHom, fun f hf =>
    chartEval_ker h c hw f (congrArg Subtype.val hf)⟩
  have hψ' : ∀ f, ψ' (π f) = chartEval w c f := fun f => RingHom.liftOfSurjective_comp_apply _ _ _ _
  refine ⟨ψ'.comp (Subalgebra.inclusion hle).toRingHom, fun k j => ⟨Algebra.subset_adjoin
    ⟨Function.update c k j, segre_update (fun k => ne_zero_of_le h (hw k)) k j⟩, ?_⟩⟩
  refine Eq.trans (congrArg ψ' (Subtype.ext ?_)) ((hψ' (MvPolynomial.X ⟨k, j⟩)).trans ?_)
  · exact (MvPolynomial.aeval_X (fun q : Σ k, J k => y q / y ⟨q.1, c q.1⟩) ⟨k, j⟩).symm
  · exact MvPolynomial.aeval_X _ _

end Alg

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem isUnit_regAt {p : Cpt ξ} {a : regAt ξ p} (h : unitAt ξ p (a : Ω)) : IsUnit a :=
  IsUnit.of_mul_eq_one ⟨_, h.2.2⟩ (Subtype.ext (mul_inv_cancel₀ h.1))

theorem exists_point {κ : Type} {x : κ → Ω} (tie : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0) {K : Type} [Field K]
    (ψ : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* K) :
    ∃ z : Spec (CommRingCat.of K) ⟶ X,
      ∀ a : Algebra.adjoin ℤ (Set.range fun j => x j / x c), ValAt ξ z (a : Ω) (ψ a) := by
  have hI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  obtain ⟨p, ⟨hp, hu⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ ℤ κ x tie c hc _ hI
  have hle : ∀ a : Algebra.adjoin ℤ (Set.range fun j => x j / x c), (a : Ω) ∈ regAt ξ p := fun a =>
    (tie.ring c hc a).1 a.2 p hp
  let ι : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* regAt ξ p :=
    (Algebra.adjoin ℤ (Set.range fun j => x j / x c)).val.toRingHom.codRestrict _ hle
  let _ := ι.toAlgebra
  have hsurj : ∀ a : regAt ξ p, ∃ s t, s ∉ RingHom.ker ψ ∧ a * ι s = ι t := by
    intro a
    obtain ⟨s, hs, h1, h2⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x tie c p hp a).1 a.2
    exact ⟨⟨s, hs⟩, ⟨_, h2⟩, (hu _).2 h1, Subtype.ext (mul_comm _ _)⟩
  have hloc : IsLocalization (RingHom.ker ψ).primeCompl (regAt ξ p) := by
    refine (isLocalization_iff _ _).2 ⟨fun s => isUnit_regAt ((hu s).1 s.2), fun a => ?_, fun {a b} hab => ?_⟩
    · obtain ⟨s, t, hs, h⟩ := hsurj a
      exact ⟨⟨t, s, hs⟩, h⟩
    · exact ⟨1, by rw [show a = b from Subtype.ext (congrArg (fun u : regAt ξ p => (u : Ω)) hab)]⟩
  let φ : regAt ξ p →+* K := IsLocalization.lift (M := (RingHom.ker ψ).primeCompl) (g := ψ)
    fun s => IsUnit.mk0 _ s.2
  have hφ : ∀ a, φ (ι a) = ψ a := fun a => IsLocalization.lift_eq _ a
  have hl : IsLocalHom φ := ⟨fun a ha => by
    obtain ⟨s, t, hs, h⟩ := hsurj a
    have h1 := congrArg φ h
    rw [map_mul, hφ, hφ] at h1
    have ht : t ∉ RingHom.ker ψ := fun h0 => mul_ne_zero ha.ne_zero hs (h1.trans h0)
    exact isUnit_of_mul_isUnit_left (h ▸ isUnit_regAt (a := ι t) ((hu t).1 ht))⟩
  obtain ⟨z, ⟨-, hz⟩, -⟩ := GlobalTheory.T.existsUnique_centre_local_hom X Ω ξ tie.gen p K φ hl
  exact ⟨z, fun a => hφ a ▸ hz (ι a)⟩

theorem unitAt_of_val (hξ : IsCptGen ξ) {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}
    (h : genPt ξ ⤳ centre z) {a : Ω} {r : R} (ha : ValAt ξ z a r) : IsUnit r ↔ unitAt ξ ⟨centre z, h⟩ a := by
  obtain ⟨φ, h1, h2⟩ := ValHom.exists_valAt_hom X Ω ξ R z h hξ
  obtain ⟨hm, rfl⟩ := (h1 a r).1 ha
  exact h2 _

theorem inFibre_of_zero (hξ : IsCptGen ξ) {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z) {p : ℕ} (hp : (p : R) = 0) :
    InFibre ξ p ⟨centre z, h⟩ := fun hu =>
  not_isUnit_zero (hp ▸ (unitAt_of_val hξ h ⟨h, (p : X.presheaf.stalk (centre z)), map_natCast _ _,
    map_natCast _ _⟩).2 hu)

theorem exists_chart_fun {κ : Type} {x : κ → Ω} (tie : CoordTie ℤ ξ x) {c : κ} {p : Cpt ξ} (hp : InChart ξ x c p)
    {U : X.Opens} (hU : p.1 ∈ U) : ∃ a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), unitAt ξ p a ∧
      ∀ q : Cpt ξ, InChart ξ x c q → unitAt ξ q a → q.1 ∈ U := by
  obtain ⟨W, hW, hm⟩ := tie.affine c hp.1
  have hmem : ∀ q : Cpt ξ, InChart ξ x c q → q.1 ∈ W := fun q hq => (hm q.1).2 ⟨q.2, hq⟩
  obtain ⟨f, hf1, hf2⟩ := hW.exists_basicOpen_le (V := U) ⟨p.1, hU⟩ (hmem p hp)
  have hg : genPt ξ ∈ W := p.2.mem_open W.2 (hmem p hp)
  have key : ∀ (q : Cpt ξ) (hq : q.1 ∈ W), genMap ξ q (X.presheaf.germ W q.1 hq f) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ W (genPt ξ) hg f) := fun q hq =>
    congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_stalkSpecializes_apply hq q.2 f)
  refine ⟨_, (tie.ring c hp.1 _).2 fun q hq => ⟨_, key q (hmem q hq)⟩, ?_, fun q hq hu => hf1 ?_⟩
  · rw [← key p (hmem p hp), ← ValHom.isUnit_iff_unitAt ξ tie.gen]
    exact (X.mem_basicOpen f p.1 (hmem p hp)).1 hf2
  · rw [← key q (hmem q hq), ← ValHom.isUnit_iff_unitAt ξ tie.gen] at hu
    exact (X.mem_basicOpen f q.1 (hmem q hq)).2 hu

theorem curve_in_cpt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (segre y) → ∀ (K : Type) [Field K] (C : ACurve K) (w : (Σ k, J k) → K), mCoordIdeal y ≤ mCoordIdeal w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → ∃ (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)), CoordsAt ξ y z w ∧ ∀ p : ℕ, (p : K) = 0 → InFibre ξ p ⟨centre z, h₀⟩ ∧ ∀ i, InFibre ξ p ⟨centre (Y.x i), h i⟩ := by
  intro X Ω _ ξ B _ J _ y tie K _ C w hle hw
  classical
  have hξ := tie.gen
  choose c hc using hw
  have hy := fun k => ne_zero_of_le hle (hc k)
  have hsc : segre y c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
  obtain ⟨ψ, hψ⟩ := exists_chart_hom hle c hc
  obtain ⟨z, hz⟩ := exists_point tie hsc ψ
  have h₀ : genPt ξ ⤳ centre z := (hz 0).1
  have hmem : ∀ j, segre y j / segre y c ∈ Algebra.adjoin ℤ (Set.range fun j => segre y j / segre y c) :=
    fun j => Algebra.subset_adjoin ⟨j, rfl⟩
  have hch : InChart ξ (segre y) c ⟨centre z, h₀⟩ := ⟨hsc, fun j => Val.mem (hz ⟨_, hmem j⟩) h₀⟩
  choose x hx using fun i => (GlobalTheory.T.valuative_lift_existsUnique X Ω ξ _ _ tie K (C.v i).valuationSubring z h₀).exists
  have hgen : ∀ i, Spec.map (CommRingCat.ofHom (C.v i).valuationSubring.subtype) ≫ x i = z := fun i => (hx i).2
  have hunit : ∀ i (a : Ω) (r : K), a ∈ regAt ξ ⟨centre (x i), (hx i).1⟩ → ValAt ξ z a r → C.v i r = 1 →
      unitAt ξ ⟨centre (x i), (hx i).1⟩ a := by
    intro i a r ha hr hv
    obtain ⟨ρ, hρ⟩ := Val.of_mem ha
    have h1 := LieTangent.valAt_base hξ (C.v i).valuationSubring.subtype hρ
    rw [hgen i] at h1
    refine (unitAt_of_val hξ _ hρ).1 ?_
    have h2 : (ρ : K) = r := LieTangent.valAt_unique hξ h1 hr
    have h3 : r ≠ 0 := fun h0 => by simp [h0] at hv
    refine IsUnit.of_mul_eq_one ⟨r⁻¹, ?_⟩ (Subtype.ext ?_)
    · change C.v i r⁻¹ ≤ 1
      rw [map_inv₀, hv, inv_one]
    · change (ρ : K) * r⁻¹ = 1
      rw [h2, mul_inv_cancel₀ h3]
  have hF : (⋃ j : {j // ψ ⟨_, hmem j⟩ ≠ 0}, {i | C.v i (ψ ⟨_, hmem j.1⟩) ≠ 1}).Finite :=
    Set.finite_iUnion fun j => C.fin _ j.2
  have hgood : ∀ i, i ∉ (⋃ j : {j // ψ ⟨_, hmem j⟩ ≠ 0}, {i | C.v i (ψ ⟨_, hmem j.1⟩) ≠ 1}) →
      InChart ξ (segre y) c ⟨centre (x i), (hx i).1⟩ := by
    intro i hi
    obtain ⟨d, hd⟩ := tie.cover ⟨centre (x i), (hx i).1⟩
    obtain ⟨ρ, hρ⟩ := Val.of_mem (hd.2 c)
    have h1 := LieTangent.valAt_base hξ (C.v i).valuationSubring.subtype hρ
    rw [hgen i] at h1
    have h2 := Val.mul h1 (hz ⟨_, hmem d⟩)
    change ValAt ξ z (segre y c / segre y d * (segre y d / segre y c)) _ at h2
    rw [div_mul_div_cancel₀ hd.1, div_self hsc] at h2
    have h3 := LieTangent.valAt_unique hξ h2 (Val.one h₀)
    have h4 : C.v i (ψ ⟨_, hmem d⟩) = 1 := by
      by_contra hcon
      exact hi (Set.mem_iUnion.2 ⟨⟨d, right_ne_zero_of_mul_eq_one h3⟩, hcon⟩)
    have h5 := congrArg (C.v i) h3
    rw [map_mul, h4, mul_one, map_one] at h5
    have h6 := hunit i _ _ (hd.2 c) h1 h5
    refine ⟨hsc, fun j => ?_⟩
    have h7 := mul_mem (hd.2 j) h6.2.2
    rwa [inv_div, div_mul_div_cancel₀ hd.1] at h7
  refine ⟨z, ⟨x, hgen, fun U hU => ?_⟩, h₀, fun i => (hx i).1, ⟨fun k => ⟨c k, IsUnit.mk0 _ (hc k)⟩,
    fun k d hd => ⟨ne_zero_of_le hle hd.ne_zero, fun j => ?_⟩⟩, fun p hp => ⟨inFibre_of_zero hξ h₀ hp, fun i =>
      inFibre_of_zero hξ _ (Subtype.ext (by simpa using hp))⟩⟩
  · obtain ⟨a, ha, hu, hq⟩ := exists_chart_fun tie hch hU
    have ha0 : ψ ⟨a, ha⟩ ≠ 0 := ((unitAt_of_val hξ h₀ (hz ⟨a, ha⟩)).2 hu).ne_zero
    refine (hF.union (C.fin _ ha0)).subset fun i hi => ?_
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    have h1 := hgood i hcon.1
    exact hi (hq _ h1 (hunit i a _ ((tie.ring c hsc a).1 ha _ h1) (hz ⟨a, ha⟩) (not_not.1 hcon.2)))
  · obtain ⟨m1, e1⟩ := hψ k d
    obtain ⟨m2, e2⟩ := hψ k j
    have v1 : ValAt ξ z (y ⟨k, d⟩ / y ⟨k, c k⟩) (w ⟨k, d⟩ / w ⟨k, c k⟩) := e1 ▸ hz ⟨_, m1⟩
    have v2 : ValAt ξ z (y ⟨k, j⟩ / y ⟨k, c k⟩) (w ⟨k, j⟩ / w ⟨k, c k⟩) := e2 ▸ hz ⟨_, m2⟩
    have hu := (unitAt_of_val hξ h₀ v1).1 (IsUnit.mk0 _ (div_ne_zero hd.ne_zero (hc k)))
    have hr := mul_mem (Val.mem v2 h₀) hu.2.2
    rw [inv_div, div_mul_div_cancel₀ (hy k)] at hr
    obtain ⟨r, hr⟩ := Val.of_mem hr
    refine ⟨r, hr, ?_⟩
    have h1 := Val.mul hr v1
    rw [div_mul_div_cancel₀ (ne_zero_of_le hle hd.ne_zero)] at h1
    have h2 := LieTangent.valAt_unique hξ h1 v2
    rw [← mul_div_assoc, div_left_inj' (hc k)] at h2
    exact h2.symm

end PositivityTheory.HtPt.Ci
