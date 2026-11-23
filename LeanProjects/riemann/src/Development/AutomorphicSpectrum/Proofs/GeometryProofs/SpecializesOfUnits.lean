import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkSpecializes
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TiePrimes

open MvPolynomial

section Forms

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem homog_mul {a b : MRing J} {da db : K → ℕ} (ha : IsMultiHomog a da) (hb : IsMultiHomog b db) :
    IsMultiHomog (a * b) (da + db) := by
  classical
  intro m hm k
  obtain ⟨m1, h1, m2, h2, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul a b hm)
  simp [Finset.sum_add_distrib, ha m1 h1 k, hb m2 h2 k]

theorem homog_add {a b : MRing J} {d : K → ℕ} (ha : IsMultiHomog a d) (hb : IsMultiHomog b d) :
    IsMultiHomog (a + b) d := by
  classical
  intro m hm k
  rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
  · exact ha m h k
  · exact hb m h k

theorem homog_C (n : ℤ) : IsMultiHomog (C n : MRing J) (0 : K → ℕ) := by
  classical
  intro m hm k
  have : m = 0 := by
    have h := MvPolynomial.support_monomial_subset (by rwa [C_apply] at hm)
    simpa using h
  simp [this]

theorem homog_X [DecidableEq K] (p : Σ k, J k) : IsMultiHomog (X p : MRing J) (Pi.single p.1 1) := by
  classical
  intro m hm k
  have : m = Finsupp.single p 1 := by
    have h := MvPolynomial.support_X (R := ℤ) (n := p) ▸ hm
    simpa using h
  subst this
  obtain ⟨j, i⟩ := p
  by_cases hk : k = j
  · subst hk
    simp [Finsupp.single_apply]
  · have : ∀ x : J k, (Finsupp.single (⟨j, i⟩ : Σ k, J k) 1 : (Σ k, J k) →₀ ℕ) ⟨k, x⟩ = 0 := by
      intro x
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hk (congrArg Sigma.fst h).symm
    simp [this, Pi.single_apply, hk]

def cMon (c : ∀ k, J k) (d : K → ℕ) : MRing J := ∏ k, X ⟨k, c k⟩ ^ d k

theorem homog_pow {a : MRing J} {d : K → ℕ} (ha : IsMultiHomog a d) (n : ℕ) :
    IsMultiHomog (a ^ n) (n • d) := by
  induction n with
  | zero =>
    simpa using homog_C (J := J) 1
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact homog_mul ih ha

theorem homog_cMon (c : ∀ k, J k) (d : K → ℕ) : IsMultiHomog (cMon c d) d := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing J) ^ d k)
      (∑ k ∈ s, d k • (Pi.single k 1 : K → ℕ)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using homog_C (J := J) 1
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact homog_mul (homog_pow (homog_X _) _) ih
  have e : (∑ k, d k • (Pi.single k 1 : K → ℕ)) = d := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [e] at this

theorem exists_form (c : ∀ k, J k) (f : MRing J) :
    ∃ (D : K → ℕ) (F : MRing J), IsMultiHomog F D ∧
      ∀ (R : Type) [CommRing R] (r : (Σ k, J k) → R), (∀ k, r ⟨k, c k⟩ = 1) → aeval r F = aeval r f := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, homog_C a, fun _ _ _ _ => rfl⟩
  | add f g hf hg =>
    obtain ⟨D₁, F₁, h₁, e₁⟩ := hf
    obtain ⟨D₂, F₂, h₂, e₂⟩ := hg
    refine ⟨D₁ + D₂, F₁ * cMon c D₂ + F₂ * cMon c D₁, homog_add (homog_mul h₁ (homog_cMon c D₂)) ?_, ?_⟩
    · have := homog_mul h₂ (homog_cMon c D₁)
      rwa [add_comm] at this
    · intro R _ r hr
      have hm : ∀ D, aeval r (cMon c D) = 1 := fun D => by
        simp [cMon, hr]
      simp [hm, e₁ R r hr, e₂ R r hr]
  | mul_X f p hf =>
    obtain ⟨D, F, h, e⟩ := hf
    exact ⟨D + Pi.single p.1 1, F * X p, homog_mul h (homog_X p), fun R _ r hr => by simp [e R r hr]⟩

end Forms

section Ratios

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

def dh (y : (Σ k, J k) → Ω) (c : ∀ k, J k) : MRing J →ₐ[ℤ] Ω :=
  aeval fun p => y p / y ⟨p.1, c p.1⟩

theorem aeval_eq_dh_mul (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {g : MRing J}
    {d : K → ℕ} (hg : IsMultiHomog g d) :
    aeval y g = dh y c g * ∏ k, y ⟨k, c k⟩ ^ d k := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hg m hm
  simp only [dh, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [_root_.mul_assoc]
  congr 1
  simp only [div_pow, Finset.prod_div_distrib]
  have hX : (∏ p : Σ k, J k, y ⟨p.1, c p.1⟩ ^ m p) = ∏ k, y ⟨k, c k⟩ ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, y ⟨k, c k⟩ ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hdeg k]
  rw [hX, div_mul_cancel₀]
  exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)

theorem eval₂_eq_dh_mul (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {g : MRing J}
    {d : K → ℕ} (hg : IsMultiHomog g d) :
    eval₂ (Int.castRingHom Ω) y g = dh y c g * ∏ k, y ⟨k, c k⟩ ^ d k := by
  rw [← aeval_eq_dh_mul y c hc hg, aeval_def, algebraMap_int_eq]

theorem dh_X_self (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : K) :
    dh y c (X ⟨k, c k⟩) = 1 := by
  simp [dh, hc k]

theorem dh_cMon (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (d : K → ℕ) :
    dh y c (cMon c d) = 1 := by
  simp [cMon, dh_X_self y c hc]

theorem mem_coord_iff (y : (Σ k, J k) → Ω) {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    g ∈ mCoordIdeal y ↔ aeval y g = 0 := by
  refine ⟨fun h => ?_, GroundTheory.Heights₂.Heights.LowerBoundFree.mem_mCoordIdeal_of_aeval_eq_zero y hg⟩
  have h0 : mConeMap y g = 0 := h
  erw [GroundTheory.Heights₂.Heights.LowerBoundFree.mConeMap_of_isMultiHomog y hg] at h0
  have hX : (∏ k, (X k : MvPolynomial K Ω) ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)
  exact MvPolynomial.C_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right hX)

theorem mem_coord_iff' (y : (Σ k, J k) → Ω) {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    g ∈ mCoordIdeal y ↔ eval₂ (Int.castRingHom Ω) y g = 0 := by
  rw [mem_coord_iff y hg, aeval_def, algebraMap_int_eq]

theorem ideal_le_of_forms {P Q : Ideal (MRing J)} (hP : IsMultiHomogIdeal P)
    (h : ∀ (g : MRing J) (d : K → ℕ), IsMultiHomog g d → g ∈ P → g ∈ Q) : P ≤ Q := by
  obtain ⟨S, hS, rfl⟩ := hP
  refine Ideal.span_le.2 fun s hs => ?_
  obtain ⟨a, ha⟩ := hS s hs
  exact h s a ha (Ideal.subset_span hs)

end Ratios

end GlobalTheory.CompanionTheory.Ar.TiePrimes

namespace GlobalTheory.CompanionTheory.Ar.TiePrimes

open MvPolynomial

section Local

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)

instance isLocalRing_regAt (p : Cpt ξ) : IsLocalRing (regAt ξ p) := by
  haveI : Nontrivial (regAt ξ p) := (regAt ξ p).toSubsemiring.nontrivial
  exact IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective

theorem isUnit_iff (p : Cpt ξ) (a : regAt ξ p) : IsUnit a ↔ unitAt ξ p (a : Ω) := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 h
    have hab : (a : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
    have h0 : (a : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one hab
    refine ⟨h0, a.2, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right hab]
    exact b.2
  · rintro ⟨h0, -, hi⟩
    exact isUnit_iff_exists_inv.2 ⟨⟨(a : Ω)⁻¹, hi⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

theorem residue_eq_zero_iff (p : Cpt ξ) (a : regAt ξ p) :
    IsLocalRing.residue (regAt ξ p) a = 0 ↔ ¬ unitAt ξ p (a : Ω) := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff]

variable {ξ}

theorem unitAt_mul {p : Cpt ξ} {a b : Ω} (ha : unitAt ξ p a) (hb : unitAt ξ p b) : unitAt ξ p (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩

theorem unitAt_inv {p : Cpt ξ} {a : Ω} (ha : unitAt ξ p a) : unitAt ξ p a⁻¹ :=
  ⟨inv_ne_zero ha.1, ha.2.2, by simpa using ha.2.1⟩

theorem unitAt_one (p : Cpt ξ) : unitAt ξ p 1 :=
  ⟨one_ne_zero, one_mem _, by simpa using one_mem _⟩

theorem unitAt_pow {p : Cpt ξ} {a : Ω} (ha : unitAt ξ p a) (n : ℕ) : unitAt ξ p (a ^ n) := by
  induction n with
  | zero => simpa using unitAt_one p
  | succ n ih => rw [pow_succ]; exact unitAt_mul ih ha

theorem unitAt_prod {p : Cpt ξ} {I : Type} (s : Finset I) (f : I → Ω) (h : ∀ i ∈ s, unitAt ξ p (f i)) :
    unitAt ξ p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using unitAt_one p
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact unitAt_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem unitAt_mul_iff {p : Cpt ξ} {a u : Ω} (ha : a ∈ regAt ξ p) (hu : unitAt ξ p u) :
    unitAt ξ p (a * u) ↔ unitAt ξ p a := by
  refine ⟨fun h => ?_, fun h => unitAt_mul h hu⟩
  have e : a = (a * u) * u⁻¹ := by field_simp [hu.1]
  rw [e]
  exact unitAt_mul h (unitAt_inv hu)

theorem specializes_of_units (hg : IsCptGen ξ) {U : X.Opens} (hU : IsAffineOpen U) {p q : Cpt ξ}
    (hp : p.1 ∈ U) (hq : q.1 ∈ U)
    (h : ∀ a : Ω, (∀ r : Cpt ξ, r.1 ∈ U → a ∈ regAt ξ r) → unitAt ξ q a → unitAt ξ p a) : p.1 ⤳ q.1 := by
  have hgp : genPt ξ ∈ U := q.2.mem_open U.2 hq
  let gp : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  have val : ∀ (r : Cpt ξ) (hr : r.1 ∈ U) (t : Γ(X, U)),
      genMap ξ r ((X.presheaf.germ U r.1 hr).hom t) = genMap ξ gp ((X.presheaf.germ U gp.1 hgp).hom t) :=
    fun r hr t => (RegAtMono.genMap_germ_eq ξ r gp r.2 U hr hgp t).symm
  rw [specializes_iff_forall_open]
  intro V hV hqV
  obtain ⟨f, hfV, hqf⟩ := hU.exists_basicOpen_le (V := ⟨V, hV⟩) ⟨q.1, hqV⟩ hq
  refine hfV ?_
  set a := genMap ξ gp ((X.presheaf.germ U gp.1 hgp).hom f) with ha
  have hreg : ∀ r : Cpt ξ, r.1 ∈ U → a ∈ regAt ξ r := fun r hr => ⟨_, val r hr f⟩
  have hqu : unitAt ξ q a := by
    rw [ha, ← val q hq f]
    exact RegAtMono.unitAt_of_isUnit ξ q (by
      have := (Scheme.mem_basicOpen X f q.1 hq).1 hqf
      exact this)
  have hpu := h a hreg hqu
  obtain ⟨s, hs⟩ := hpu.2.2
  have hpa : genMap ξ p ((X.presheaf.germ U p.1 hp).hom f) = a := val p hp f
  have e : (X.presheaf.germ U p.1 hp).hom f * s = 1 := by
    apply hg.inj p
    rw [map_mul, map_one, hpa]
    have hs' : genMap ξ p s = a⁻¹ := hs
    rw [hs', mul_inv_cancel₀ hpu.1]
  exact (Scheme.mem_basicOpen X f p.1 hp).2 (IsUnit.of_mul_eq_one _ e)

end Local

end GlobalTheory.CompanionTheory.Ar.TiePrimes

namespace GlobalTheory.CompanionTheory.Ar.TiePrimes

open MvPolynomial

section Chart

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

abbrev seg (y : (Σ k, J k) → Ω) : ((k : K) → J k) → Ω := fun c' => ∏ k, y ⟨k, c' k⟩

omit [∀ k, Fintype (J k)] in
theorem ne_of_seg {y : (Σ k, J k) → Ω} {c : ∀ k, J k} (h : seg y c ≠ 0) (k : K) : y ⟨k, c k⟩ ≠ 0 :=
  Finset.prod_ne_zero_iff.1 h k (Finset.mem_univ k)

omit [∀ k, Fintype (J k)] in
theorem seg_ne {y : (Σ k, J k) → Ω} {c : ∀ k, J k} (h : ∀ k, y ⟨k, c k⟩ ≠ 0) : seg y c ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => h k

omit [∀ k, Fintype (J k)] in
theorem seg_div (y : (Σ k, J k) → Ω) (c j : ∀ k, J k) :
    seg y j / seg y c = ∏ k, y ⟨k, j k⟩ / y ⟨k, c k⟩ :=
  by rw [Finset.prod_div_distrib]

omit [∀ k, Fintype (J k)] in
theorem ratio_eq [DecidableEq K] {y : (Σ k, J k) → Ω} {c : ∀ k, J k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (q : Σ k, J k) :
    y q / y ⟨q.1, c q.1⟩ = seg y (Function.update c q.1 q.2) / seg y c := by
  rw [seg_div, Finset.prod_eq_single q.1]
  · simp
  · intro k _ hk
    simp [Function.update_of_ne hk, hc k]
  · simp

theorem adjoin_eq {y : (Σ k, J k) → Ω} {c : ∀ k, J k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Algebra.adjoin ℤ (Set.range fun j => seg y j / seg y c) = (dh y c).range := by
  classical
  have e : (dh y c).range = Algebra.adjoin ℤ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) :=
    (Algebra.adjoin_range_eq_range_aeval ℤ _).symm
  rw [e]
  refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_)
  · rintro _ ⟨j, rfl⟩
    show seg y j / seg y c ∈ _
    rw [seg_div]
    exact Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨k, j k⟩, rfl⟩
  · rintro _ ⟨q, rfl⟩
    show y q / y ⟨q.1, c q.1⟩ ∈ _
    rw [ratio_eq hc]
    exact Algebra.subset_adjoin ⟨_, rfl⟩

theorem exists_form_dh {y : (Σ k, J k) → Ω} {c : ∀ k, J k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (f : MRing J) :
    ∃ (D : K → ℕ) (F : MRing J), IsMultiHomog F D ∧ dh y c F = dh y c f := by
  obtain ⟨D, F, hF, e⟩ := exists_form c f
  exact ⟨D, F, hF, e Ω _ fun k => div_self (hc k)⟩

variable {Sc : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ Sc} {y : (Σ k, J k) → Ω}

theorem ratio_mem {c : ∀ k, J k} {p : Cpt ξ} (h : InChart ξ (seg y) c p) (q : Σ k, J k) :
    y q / y ⟨q.1, c q.1⟩ ∈ regAt ξ p := by
  classical
  rw [ratio_eq (ne_of_seg h.1)]
  exact h.2 _

def dhP {c : ∀ k, J k} {p : Cpt ξ} (h : InChart ξ (seg y) c p) : MRing J →+* regAt ξ p :=
  eval₂Hom (Int.castRingHom _) fun q => ⟨_, ratio_mem h q⟩

theorem coe_dhP {c : ∀ k, J k} {p : Cpt ξ} (h : InChart ξ (seg y) c p) (f : MRing J) :
    (dhP h f : Ω) = dh y c f := by
  have e : ((regAt ξ p).subtype).comp (dhP h) = (dh y c : MRing J →+* Ω) :=
    MvPolynomial.ringHom_ext (fun a => by simp [dhP]) (fun q => by simp [dhP, dh])
  exact RingHom.congr_fun e f

theorem dh_mem {c : ∀ k, J k} {p : Cpt ξ} (h : InChart ξ (seg y) c p) (f : MRing J) :
    dh y c f ∈ regAt ξ p := by
  rw [← coe_dhP h]
  exact (dhP h f).2

def rv {c : ∀ k, J k} {p : Cpt ξ} (h : InChart ξ (seg y) c p) :
    (Σ k, J k) → IsLocalRing.ResidueField (regAt ξ p) :=
  fun q => IsLocalRing.residue _ ⟨_, ratio_mem h q⟩

theorem eval₂_rv {c : ∀ k, J k} {p : Cpt ξ} (h : InChart ξ (seg y) c p) (f : MRing J) :
    eval₂ (Int.castRingHom _) (rv h) f = IsLocalRing.residue _ (dhP h f) := by
  have e : eval₂Hom (Int.castRingHom _) (rv h) = (IsLocalRing.residue (regAt ξ p)).comp (dhP h) :=
    MvPolynomial.ringHom_ext (fun a => by simp [dhP]) (fun q => by simp [dhP, rv])
  exact RingHom.congr_fun e f

theorem mem_rv_iff {c : ∀ k, J k} {p : Cpt ξ} (h : InChart ξ (seg y) c p) {g : MRing J} {d : K → ℕ}
    (hg : IsMultiHomog g d) : g ∈ mCoordIdeal (rv h) ↔ ¬ unitAt ξ p (dh y c g) := by
  rw [mem_coord_iff' _ hg, eval₂_rv, residue_eq_zero_iff, coe_dhP]

theorem unit_ratio {c c' : ∀ k, J k} {p : Cpt ξ} (h : InChart ξ (seg y) c p)
    (h' : InChart ξ (seg y) c' p) (k : K) : unitAt ξ p (y ⟨k, c k⟩ / y ⟨k, c' k⟩) := by
  refine ⟨div_ne_zero (ne_of_seg h.1 k) (ne_of_seg h'.1 k), ratio_mem h' ⟨k, c k⟩, ?_⟩
  rw [inv_div]
  exact ratio_mem h ⟨k, c' k⟩

theorem unit_dh_iff {c c' : ∀ k, J k} {p : Cpt ξ} (h : InChart ξ (seg y) c p)
    (h' : InChart ξ (seg y) c' p) {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    unitAt ξ p (dh y c' g) ↔ unitAt ξ p (dh y c g) := by
  have hc := ne_of_seg h.1
  have hc' := ne_of_seg h'.1
  have e : dh y c' g = dh y c g * ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ d k := by
    have e1 := aeval_eq_dh_mul y c hc hg
    have e2 := aeval_eq_dh_mul y c' hc' hg
    have h0 : (∏ k, y ⟨k, c' k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc' k)
    simp only [div_pow, Finset.prod_div_distrib]
    rw [← mul_div_assoc, ← e1, e2, mul_div_cancel_right₀ _ h0]
  rw [e]
  exact unitAt_mul_iff (dh_mem h g) (unitAt_prod _ _ fun k _ => unitAt_pow (unit_ratio h h' k) _)

variable (tie : CoordTie ℤ ξ (seg y))

include tie in
theorem exists_chart (p : Cpt ξ) : ∃ c, InChart ξ (seg y) c p := tie.cover p

def Wp (p : Cpt ξ) : Ideal (MRing J) :=
  mCoordIdeal (rv (Classical.choose_spec (exists_chart tie p)))

theorem mem_Wp_iff {c : ∀ k, J k} {p : Cpt ξ} (h : InChart ξ (seg y) c p) {g : MRing J} {d : K → ℕ}
    (hg : IsMultiHomog g d) : g ∈ Wp tie p ↔ ¬ unitAt ξ p (dh y c g) := by
  rw [Wp, mem_rv_iff _ hg, unit_dh_iff h (Classical.choose_spec (exists_chart tie p)) hg]

theorem Wp_homog (p : Cpt ξ) : IsMultiHomogIdeal (Wp tie p) :=
  GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal _

theorem X_notMem {c : ∀ k, J k} {p : Cpt ξ} (h : InChart ξ (seg y) c p) (k : K) :
    (X ⟨k, c k⟩ : MRing J) ∉ Wp tie p := by
  classical
  rw [mem_Wp_iff tie h (homog_X _), dh_X_self y c (ne_of_seg h.1), not_not]
  exact unitAt_one p

theorem Wp_isMultiProjPrime (p : Cpt ξ) : IsMultiProjPrime (Wp tie p) := by
  obtain ⟨c, h⟩ := tie.cover p
  exact ⟨RingHom.ker_isPrime _, Wp_homog tie p, fun k => ⟨c k, X_notMem tie h k⟩⟩

theorem coord_le_Wp (p : Cpt ξ) : mCoordIdeal y ≤ Wp tie p := by
  obtain ⟨c, h⟩ := tie.cover p
  have hc := ne_of_seg h.1
  refine ideal_le_of_forms (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal y) fun g d hg hgP => ?_
  rw [mem_Wp_iff tie h hg]
  intro hu
  have e := aeval_eq_dh_mul y c hc hg
  rw [(mem_coord_iff y hg).1 hgP] at e
  have h0 : (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  exact mul_ne_zero hu.1 h0 e.symm

theorem inChart_iff (p : Cpt ξ) (c : ∀ k, J k) :
    InChart ξ (seg y) c p ↔ ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ Wp tie p := by
  classical
  refine ⟨fun h k => X_notMem tie h k, fun h => ?_⟩
  obtain ⟨c₀, h₀⟩ := tie.cover p
  have hc₀ := ne_of_seg h₀.1
  have hu : ∀ k, unitAt ξ p (y ⟨k, c k⟩ / y ⟨k, c₀ k⟩) := fun k => by
    have := h k
    rw [mem_Wp_iff tie h₀ (homog_X _), not_not] at this
    simpa [dh] using this
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => by
    have := (hu k).1
    exact left_ne_zero_of_mul (by simpa [div_eq_mul_inv] using this)
  refine ⟨seg_ne hc, fun j => ?_⟩
  rw [seg_div]
  refine prod_mem fun k _ => ?_
  have e : y ⟨k, j k⟩ / y ⟨k, c k⟩ =
      (y ⟨k, j k⟩ / y ⟨k, c₀ k⟩) * (y ⟨k, c k⟩ / y ⟨k, c₀ k⟩)⁻¹ := by
    have := hc₀ k
    have := hc k
    field_simp
  rw [e]
  exact mul_mem (ratio_mem h₀ ⟨k, j k⟩) (hu k).2.2

theorem specializes_iff (p q : Cpt ξ) : p.1 ⤳ q.1 ↔ Wp tie p ≤ Wp tie q := by
  constructor
  · intro h
    obtain ⟨c, hq⟩ := tie.cover q
    have mono := ((RegAtMono.regAt_mono Sc Ω ξ q p h).1)
    have hp : InChart ξ (seg y) c p := ⟨hq.1, fun c' => mono (hq.2 c')⟩
    refine ideal_le_of_forms (Wp_homog tie p) fun g d hg hgp => ?_
    rw [mem_Wp_iff tie hq hg]
    exact fun hu => (mem_Wp_iff tie hp hg).1 hgp ⟨hu.1, mono hu.2.1, mono hu.2.2⟩
  · intro h
    obtain ⟨c, hq⟩ := tie.cover q
    have hp : InChart ξ (seg y) c p :=
      (inChart_iff tie p c).2 fun k hX => (inChart_iff tie q c).1 hq k (h hX)
    have hc := ne_of_seg hq.1
    obtain ⟨U, hU, hmem⟩ := tie.affine c hq.1
    refine specializes_of_units tie.gen hU ((hmem _).2 ⟨p.2, hp⟩) ((hmem _).2 ⟨q.2, hq⟩) fun a ha hu => ?_
    have haA : a ∈ Algebra.adjoin ℤ (Set.range fun j => seg y j / seg y c) :=
      (tie.ring c hq.1 a).2 fun r hr => ha r ((hmem _).2 ⟨r.2, hr⟩)
    rw [adjoin_eq hc] at haA
    obtain ⟨f, rfl⟩ := haA
    obtain ⟨D, F, hF, e⟩ := exists_form_dh hc f
    change unitAt ξ p (dh y c f)
    change unitAt ξ q (dh y c f) at hu
    rw [← e] at hu ⊢
    by_contra hn
    exact (mem_Wp_iff tie hq hF).1 (h ((mem_Wp_iff tie hp hF).2 hn)) hu

theorem regAt_iff (p : Cpt ξ) (a : Ω) :
    a ∈ regAt ξ p ↔ ∃ (d : K → ℕ) (g h : MRing J), IsMultiHomog g d ∧ IsMultiHomog h d ∧
      h ∉ Wp tie p ∧ aeval y g = a * aeval y h := by
  obtain ⟨c, hp⟩ := tie.cover p
  have hc := ne_of_seg hp.1
  have h0 : ∀ d : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0 := fun d =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  constructor
  · intro ha
    obtain ⟨s, hs, hu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization Sc Ω ξ ℤ _ (seg y) tie c p hp a).1 ha
    rw [adjoin_eq hc] at hs hsa
    obtain ⟨f₁, rfl⟩ := hs
    obtain ⟨f₂, e₂⟩ := hsa
    obtain ⟨D₁, F₁, hF₁, e₁⟩ := exists_form_dh hc f₁
    obtain ⟨D₂, F₂, hF₂, e₃⟩ := exists_form_dh hc f₂
    change dh y c f₂ = _ at e₂
    change unitAt ξ p (dh y c f₁) at hu
    have hg : IsMultiHomog (F₂ * cMon c D₁) (D₁ + D₂) := by
      have := homog_mul hF₂ (homog_cMon c D₁)
      rwa [add_comm] at this
    have hh : IsMultiHomog (F₁ * cMon c D₂) (D₁ + D₂) := homog_mul hF₁ (homog_cMon c D₂)
    have d₁ : dh y c (F₁ * cMon c D₂) = dh y c f₁ := by rw [map_mul, dh_cMon y c hc, _root_.mul_one, e₁]
    have d₂ : dh y c (F₂ * cMon c D₁) = dh y c f₁ * a := by
      rw [map_mul, dh_cMon y c hc, _root_.mul_one, e₃, e₂]
      rfl
    refine ⟨D₁ + D₂, _, _, hg, hh, ?_, ?_⟩
    · rw [mem_Wp_iff tie hp hh, d₁, not_not]
      exact hu
    · rw [aeval_eq_dh_mul y c hc hg, aeval_eq_dh_mul y c hc hh, d₁, d₂]
      ring
  · rintro ⟨d, g, h, hg, hh, hW, e⟩
    rw [mem_Wp_iff tie hp hh, not_not] at hW
    rw [aeval_eq_dh_mul y c hc hg, aeval_eq_dh_mul y c hc hh, ← _root_.mul_assoc] at e
    have e' := mul_right_cancel₀ (h0 d) e
    have : a = dh y c g * (dh y c h)⁻¹ := by
      rw [e', _root_.mul_assoc, mul_inv_cancel₀ hW.1, _root_.mul_one]
    rw [this]
    exact mul_mem (dh_mem hp g) hW.2.2

theorem inFibre_iff (p : Cpt ξ) (r : ℕ) : InFibre ξ r p ↔ (r : MRing J) ∈ Wp tie p := by
  obtain ⟨c, hp⟩ := tie.cover p
  have hr : IsMultiHomog (r : MRing J) (0 : K → ℕ) := by
    have := homog_C (J := J) (r : ℤ)
    simpa using this
  rw [mem_Wp_iff tie hp hr, map_natCast]
  rfl

end Chart

end GlobalTheory.CompanionTheory.Ar.TiePrimes

namespace GlobalTheory.CompanionTheory.Ar.TiePrimes

open MvPolynomial

section Points

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
variable {Sc : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ Sc} {y : (Σ k, J k) → Ω}

theorem exists_point (tie : CoordTie ℤ ξ (seg y)) {W : Ideal (MRing J)} (hW : IsMultiProjPrime W)
    (hPW : mCoordIdeal y ≤ W) : ∃ p : Cpt ξ, Wp tie p = W := by
  classical
  obtain ⟨hWp, hWh, hWr⟩ := hW
  choose c hcX using hWr
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hcX k (hPW ((mem_coord_iff y (homog_X _)).2 (by simpa using h0)))
  have hx : seg y c ≠ 0 := seg_ne hc
  haveI : IsDomain (MRing J ⧸ W) := Ideal.Quotient.isDomain W
  let F := FractionRing (MRing J ⧸ W)
  let y' : (Σ k, J k) → F := fun q => algebraMap (MRing J ⧸ W) F (Ideal.Quotient.mk W (X q))
  have ae : ∀ f : MRing J, eval₂ (Int.castRingHom F) y' f =
      algebraMap (MRing J ⧸ W) F (Ideal.Quotient.mk W f) := by
    intro f
    have e : eval₂Hom (Int.castRingHom F) y' =
        (algebraMap (MRing J ⧸ W) F).comp (Ideal.Quotient.mk W) :=
      MvPolynomial.ringHom_ext (fun a => by simp) (fun q => by simp [y'])
    exact RingHom.congr_fun e f
  have hzero : ∀ f : MRing J, eval₂ (Int.castRingHom F) y' f = 0 ↔ f ∈ W := by
    intro f
    rw [ae, map_eq_zero_iff _ (IsFractionRing.injective (MRing J ⧸ W) F), Ideal.Quotient.eq_zero_iff_mem]
  have hc' : ∀ k, y' ⟨k, c k⟩ ≠ 0 := fun k h0 => hcX k ((hzero _).1 (by simpa using h0))
  have memW : ∀ (g : MRing J) (d : K → ℕ), IsMultiHomog g d → (g ∈ W ↔ dh y' c g = 0) := by
    intro g d hg
    have h0 : (∏ k, y' ⟨k, c k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc' k)
    rw [← hzero, eval₂_eq_dh_mul y' c hc' hg, mul_eq_zero, or_iff_left h0]
  let A := Algebra.adjoin ℤ (Set.range fun j => seg y j / seg y c)
  have hdhA : ∀ f, dh y c f ∈ A := fun f => by
    show dh y c f ∈ Algebra.adjoin ℤ _
    rw [adjoin_eq hc]
    exact ⟨f, rfl⟩
  let φ : MRing J →+* A := ((dh y c).codRestrict A hdhA : MRing J →ₐ[ℤ] A).toRingHom
  have hφ : ∀ f, ((φ f : A) : Ω) = dh y c f := fun f => rfl
  have hsurj : Function.Surjective φ := by
    rintro ⟨a, ha⟩
    have ha' : a ∈ (dh y c).range := by
      rw [← adjoin_eq hc]
      exact ha
    obtain ⟨f, rfl⟩ := ha'
    exact ⟨f, Subtype.ext rfl⟩
  let Q : Ideal (MRing J) := RingHom.ker (dh y' c : MRing J →+* F)
  haveI hQ : Q.IsPrime := RingHom.ker_isPrime _
  have hker : RingHom.ker φ ≤ Q := by
    intro f hf
    have hf0 : dh y c f = 0 := by
      rw [← hφ, RingHom.mem_ker.1 hf]
      rfl
    obtain ⟨D, G, hG, e⟩ := exists_form c f
    have e₁ : dh y c G = dh y c f := e Ω _ fun k => div_self (hc k)
    have e₂ : dh y' c G = dh y' c f := e F _ fun k => div_self (hc' k)
    have hGP : G ∈ W := hPW ((mem_coord_iff y hG).2 (by
      rw [aeval_eq_dh_mul y c hc hG, e₁, hf0, zero_mul]))
    show dh y' c f = 0
    rw [← e₂]
    exact (memW G D hG).1 hGP
  let I : Ideal A := Q.map φ
  have hI : I.IsPrime := Ideal.map_isPrime_of_surjective hsurj hker
  obtain ⟨p, ⟨hin, hunit⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point Sc Ω ξ ℤ _ (seg y) tie c hx I hI
  have hI' : ∀ g : MRing J, φ g ∈ I ↔ g ∈ Q := by
    intro g
    refine ⟨fun h => ?_, Ideal.mem_map_of_mem φ⟩
    obtain ⟨x, hx', e⟩ := (Ideal.mem_map_iff_of_surjective φ hsurj).1 h
    have : g - x ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, map_sub, e, sub_self]
    have h2 := Q.add_mem (hker this) hx'
    simpa using h2
  have key : ∀ (g : MRing J) (d : K → ℕ), IsMultiHomog g d → (g ∈ Wp tie p ↔ g ∈ W) := by
    intro g d hg
    rw [mem_Wp_iff tie hin hg, memW g d hg, ← hφ, ← hunit (φ g), not_not, hI' g]
    rfl
  exact ⟨p, le_antisymm (ideal_le_of_forms (Wp_homog tie p) fun g d hg h => (key g d hg).1 h)
    (ideal_le_of_forms hWh fun g d hg h => (key g d hg).2 h)⟩

end Points

theorem points_equiv_primes : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∃ e : Cpt ξ ≃ {W : Ideal (MRing J) // IsMultiProjPrime W ∧ mCoordIdeal y ≤ W}, (∀ p q : Cpt ξ, p.1 ⤳ q.1 ↔ (e p).1 ≤ (e q).1) ∧ (∀ (p : Cpt ξ) (c : (k : K) → J k), InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p ↔ ∀ k, (MvPolynomial.X ⟨k, c k⟩ : MRing J) ∉ (e p).1) ∧ (∀ (p : Cpt ξ) (a : Ω), a ∈ regAt ξ p ↔ ∃ (d : K → ℕ) (g h : MRing J), IsMultiHomog g d ∧ IsMultiHomog h d ∧ h ∉ (e p).1 ∧ MvPolynomial.aeval y g = a * MvPolynomial.aeval y h) ∧ ∀ (p : Cpt ξ) (r : ℕ), InFibre ξ r p ↔ (r : MRing J) ∈ (e p).1 := by
  intro X Ω _ ξ K _ J _ y tie
  have hinj : Function.Injective (fun p : Cpt ξ =>
      (⟨Wp tie p, Wp_isMultiProjPrime tie p, coord_le_Wp tie p⟩ :
        {W : Ideal (MRing J) // IsMultiProjPrime W ∧ mCoordIdeal y ≤ W})) := by
    intro p q h
    have h' : Wp tie p = Wp tie q := congrArg Subtype.val h
    have h1 := (specializes_iff tie p q).2 h'.le
    have h2 := (specializes_iff tie q p).2 h'.ge
    exact Subtype.ext (h1.antisymm h2).eq
  have hsurj : Function.Surjective (fun p : Cpt ξ =>
      (⟨Wp tie p, Wp_isMultiProjPrime tie p, coord_le_Wp tie p⟩ :
        {W : Ideal (MRing J) // IsMultiProjPrime W ∧ mCoordIdeal y ≤ W})) := by
    rintro ⟨W, hW, hPW⟩
    obtain ⟨p, rfl⟩ := exists_point tie hW hPW
    exact ⟨p, rfl⟩
  exact ⟨Equiv.ofBijective _ ⟨hinj, hsurj⟩, specializes_iff tie, fun p c => inChart_iff tie p c,
    regAt_iff tie, inFibre_iff tie⟩

end GlobalTheory.CompanionTheory.Ar.TiePrimes
