import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsCoordsAtOfCoordTie
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ZarhinBundleKernelFirstCoordEquations
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsVBOneOfChartGenerators

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ProjectiveLinePlaces

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]

theorem centre_specializes (z : Spec (CommRingCat.of R) ⟶ X) (φ : R →+* S) :
    centre (Spec.map (CommRingCat.ofHom φ) ≫ z) ⤳ centre z :=
  (IsLocalRing.specializes_closedPoint (R := R) _).map z.continuous

theorem stalk_square {x y : X} (hs : y ⤳ x) {A B : CommRingCat.{0}} (g : X.presheaf.stalk x ⟶ A)
    (g' : X.presheaf.stalk y ⟶ B) (φ : A ⟶ B)
    (h : Spec.map g' ≫ X.fromSpecStalk y = Spec.map φ ≫ Spec.map g ≫ X.fromSpecStalk x) :
    X.presheaf.stalkSpecializes hs ≫ g' = g ≫ φ := by
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecStalk x), Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk, h]

theorem genMap_specializes {x y : X} (hs : y ⤳ x) (h0 : genPt ξ ⤳ y) (h1 : genPt ξ ⤳ x)
    (s : X.presheaf.stalk x) :
    genMap ξ ⟨y, h0⟩ ((X.presheaf.stalkSpecializes hs).hom s) = genMap ξ ⟨x, h1⟩ s := by
  have h := X.presheaf.stalkSpecializes_comp h0 hs
  have h2 : X.presheaf.stalkSpecializes hs ≫ (X.presheaf.stalkSpecializes h0 ≫ Scheme.stalkClosedPointTo ξ) =
      X.presheaf.stalkSpecializes h1 ≫ Scheme.stalkClosedPointTo ξ :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ Scheme.stalkClosedPointTo ξ) h)
  exact congrArg (fun g => g.hom s) h2

theorem valAt_restrict {z : Spec (CommRingCat.of R) ⟶ X} (φ : R →+* S) {y : Spec (CommRingCat.of S) ⟶ X}
    (hy : Spec.map (CommRingCat.ofHom φ) ≫ z = y) (h0 : genPt ξ ⤳ centre y) {a : Ω} {r : R}
    (h : ValAt ξ z a r) : ValAt ξ y a (φ r) := by
  obtain ⟨hz, s, rfl, rfl⟩ := h
  have hs : centre y ⤳ centre z := hy ▸ centre_specializes z φ
  refine ⟨h0, (X.presheaf.stalkSpecializes hs).hom s, genMap_specializes hs h0 hz s, ?_⟩
  have key := stalk_square hs (Scheme.stalkClosedPointTo z) (Scheme.stalkClosedPointTo y)
    (CommRingCat.ofHom φ) ((Scheme.Spec_stalkClosedPointTo_fromSpecStalk y).trans (hy.symm.trans
      (congrArg (Spec.map (CommRingCat.ofHom φ) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z)).symm))
  exact congrArg (fun g => g.hom s) key

theorem valAt_of_unit {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z) {a : Ω}
    (ha : unitAt ξ ⟨centre z, h⟩ a) : ∃ r : Rˣ, ValAt ξ z a r := by
  obtain ⟨s, hs, rfl⟩ := (CptModel.unitAt_iff ξ _ a).1 ha
  obtain ⟨r, hr⟩ := hs.map (Scheme.stalkClosedPointTo z).hom
  exact ⟨r, h, s, rfl, hr.symm⟩

theorem unitAt_div {L : Lat ξ Ω} {p : Cpt ξ} {s t : Ω} (hs : L.IsGenAt p s) (ht : L.IsGenAt p t) :
    unitAt ξ p (s / t) := by
  have key : ∀ s t : Ω, L.IsGenAt p s → L.IsGenAt p t → s / t ∈ regAt ξ p := by
    intro s t hs ht
    have : s ∈ Submodule.span (regAt ξ p) {t} := ht.2 ▸ hs.2 ▸ Submodule.mem_span_singleton_self s
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 this
    rw [show c • t = (c : Ω) * t from rfl, mul_div_cancel_right₀ _ ht.1]
    exact c.2
  exact ⟨div_ne_zero hs.1 ht.1, key s t hs ht, by rw [inv_div]; exact key t s ht hs⟩

theorem valAt_push {Y : Scheme.{0}} {η : Spec (CommRingCat.of Ω) ⟶ Y} {z : Spec (CommRingCat.of R) ⟶ Y}
    (f : Y ⟶ X) [IsOpenImmersion f] {a : Ω} {r : R} (h : ValAt η z a r) : ValAt (η ≫ f) (z ≫ f) a r := by
  obtain ⟨hz, s, rfl, rfl⟩ := h
  have hb : Function.Bijective (f.stalkMap (centre z)).hom := ConcreteCategory.bijective_of_isIso _
  obtain ⟨t, rfl⟩ := hb.2 s
  refine ⟨(ProjCoord.push η f ⟨centre z, hz⟩).2, t, ?_, ?_⟩
  · exact DFunLike.congr_fun (ProjCoord.genMap_push η f ⟨centre z, hz⟩) t
  · exact congrArg (fun g => g.hom t) (Scheme.stalkClosedPointTo_comp z f)

theorem valAt_affine {A : Type} [CommRing A] (φ : A →+* Ω) (hφ : Function.Injective φ) (χ : A →+* R) (a : A) :
    ValAt (CptModel.pt φ) (Spec.map (CommRingCat.ofHom χ)) (φ a) (χ a) := by
  refine ⟨ProjCoord.specializes_of_injective φ hφ _, CptModel.tS _ a,
    CptModel.genMap_toStalk φ ⟨_, ProjCoord.specializes_of_injective φ hφ _⟩ a, ?_⟩
  have h1 := Scheme.germ_stalkClosedPointTo_Spec (R := CommRingCat.of A) (S := CommRingCat.of R)
    (CommRingCat.ofHom χ)
  have h3 := (congrArg ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ ·) h1).trans (Iso.inv_hom_id_assoc _ _)
  exact congrArg (fun f => f.hom a) h3

theorem valAt_chart {A : Type} [CommRing A] (φ : A →+* Ω) (hφ : Function.Injective φ)
    (f : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion f] (e : ξ = CptModel.pt φ ≫ f) (χ : A →+* R) (a : A) :
    ValAt ξ (Spec.map (CommRingCat.ofHom χ) ≫ f) (φ a) (χ a) :=
  e ▸ valAt_push f (valAt_affine φ hφ χ a)

end General

section Line

open IsDedekindDomain Polynomial Crv.Inhab
open scoped Classical

variable (k : Type) [Field k]

theorem projective_line_place_degree_pos (i : (projLine k).I) : 0 < (projLine k).w i := by
  rcases i with _ | q
  · exact one_pos
  · change 0 < (Submodule.IsPrincipal.generator q.asIdeal).natDegree
    have hg := Ideal.span_singleton_generator q.asIdeal
    refine natDegree_pos_iff_degree_pos.2 (degree_pos_of_ne_zero_of_nonunit (fun h => q.ne_bot ?_) fun h => ?_)
    · rw [← hg, h]; simp
    · exact q.isPrime.ne_top (hg ▸ Ideal.span_singleton_eq_top.2 h)

theorem projective_line_place_trivial_on_constants (i : (projLine k).I) (a : k) (ha : a ≠ 0) : (projLine k).v i (algebraMap k (RatFunc k) a) = 1 := by
  rcases i with _ | q
  · change RatFunc.inftyValuation k _ = 1
    exact Valuation.IsTrivialOn.eq_one a ha
  · change q.valuation (RatFunc k) _ = 1
    rw [IsScalarTower.algebraMap_apply k k[X] (RatFunc k), HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h ((IsUnit.mk0 a ha).map _))

theorem projective_line_places_all_valuations (W : ValuationSubring (RatFunc k)) (hW : W ≠ ⊤) (hk : ∀ a : k, algebraMap k (RatFunc k) a ∈ W) :
    ∃! i, ((projLine k).v i).valuationSubring = W := by
  have ex : ∃ i, ((projLine k).v i).valuationSubring = W := by
    haveI : W.valuation.IsTrivialOn k := ⟨fun a ha => by
      have a1 := (W.valuation_le_one_iff _).2 (hk a)
      have a2 := (W.valuation_le_one_iff _).2 (hk a⁻¹)
      rw [map_inv₀, map_inv₀, inv_le_one₀ (by simpa [zero_lt_iff] using ha)] at a2
      exact le_antisymm a1 a2⟩
    rcases lt_or_ge 1 (W.valuation RatFunc.X) with hlt | hle
    · refine ⟨none, ?_⟩
      have := RatFunc.valuation_isEquiv_inftyValuation_of_one_lt_valuation_X hlt
      rw [Valuation.isEquiv_iff_valuationSubring, W.valuationSubring_valuation] at this
      exact this.symm
    · haveI : W.valuation.IsNontrivial := by
        obtain ⟨y, hy⟩ : ∃ y, y ∉ W := by
          by_contra h
          push Not at h
          exact hW (eq_top_iff.2 fun y _ => h y)
        refine ⟨y, ?_, ?_⟩
        · intro h; exact hy ((W.valuation_le_one_iff _).1 (by rw [h]; exact zero_le_one))
        · intro h; exact hy ((W.valuation_le_one_iff _).1 h.le)
      let q := RatFunc.valuationIdeal hle
      refine ⟨some q, ?_⟩
      have hp : ∀ a : k[X], W.valuation (algebraMap k[X] (RatFunc k) a) ≤ 1 :=
        Polynomial.valuation_le_one_of_valuation_X_le_one k hle
      have hq : ∀ a ∈ q.asIdeal, W.valuation (algebraMap k[X] (RatFunc k) a) < 1 := by
        intro a ha
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
        rw [map_mul, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hp c)) (RatFunc.valuation_uniformizingPolynomial_lt_one hle)
      have hle' : (q.valuation (RatFunc k)).valuationSubring ≤ W := by
        intro x hx
        obtain ⟨n, d, h⟩ := q.exists_primeCompl_mul_eq_of_integer x hx
        have hd : W.valuation (algebraMap k[X] (RatFunc k) d) = 1 := by
          by_contra hne
          obtain ⟨y, i, hi, e⟩ := q.isMaximal.exists_inv d.2
          have h1 : W.valuation (algebraMap k[X] (RatFunc k) (y * d)) < 1 := by
            rw [map_mul, map_mul]
            exact lt_of_le_of_lt (mul_le_of_le_one_left' (hp y)) (lt_of_le_of_ne (hp d) hne)
          have h2 := W.valuation.map_add_lt h1 (hq i hi)
          rw [← map_add, e, map_one, map_one] at h2
          exact lt_irrefl _ h2
        have h3 := hp n
        rw [← h, map_mul, hd, mul_one] at h3
        exact (W.valuation_le_one_iff _).1 h3
      rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at hle'
      exact (HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring q).symm.trans
        (ValuationSubring.eq_of_le_of_ne_top _ hle' hW)
  obtain ⟨i, hi⟩ := ex
  refine ⟨i, hi, fun j hj => ?_⟩
  have e : ((projLine k).v j).IsEquiv ((projLine k).v i) := by
    rw [Valuation.isEquiv_iff_valuationSubring, hi, hj]
  rcases i with _ | p <;> rcases j with _ | q
  · rfl
  · exact absurd e (RatFunc.adicValuation_not_isEquiv_infty_valuation q)
  · exact absurd e.symm (RatFunc.adicValuation_not_isEquiv_infty_valuation p)
  · exact congrArg some (HeightOneSpectrum.eq_of_valuation_isEquiv_valuation e)

theorem ratFunc_fg : (⊤ : IntermediateField k (RatFunc k)).FG := by
  refine ⟨{RatFunc.X}, ?_⟩
  simpa using RatFunc.adjoin_X (K := k)

theorem ratFunc_trdeg : Algebra.trdeg k (RatFunc k) = 1 := by
  haveI : Algebra.IsAlgebraic k[X] (RatFunc k) := IsLocalization.isAlgebraic _ (nonZeroDivisors k[X])
  have := trdeg_add_eq k k[X] (A := RatFunc k)
  rw [Polynomial.trdeg_of_isDomain, trdeg_eq_zero, add_zero] at this
  exact this.symm

end Line

section Proj

open MvPolynomial HomogeneousLocalization ProjCoord

attribute [local instance] MvPolynomial.gradedAlgebra

variable {o κ Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem coordTie_charts (x : κ → Ω) (hx : ∀ c, x c ≠ 0) (c₀ : κ)
    (hinj : ∀ (n : ℕ) (g : MvPolynomial κ o), g.IsHomogeneous n → aeval x g = 0 → g = 0)
    (hgen : ∀ a : Ω, ∃ u ∈ Algebra.adjoin o (Set.range fun j => x j / x c₀),
      ∃ v ∈ Algebra.adjoin o (Set.range fun j => x j / x c₀), v ≠ 0 ∧ a * v = u) :
    ∃ ξ : Spec (CommRingCat.of Ω) ⟶ Proj (homogeneousSubmodule κ o), CoordTie o ξ x ∧ ∀ c,
      ξ = CptModel.pt (chartEval x c (hx c)) ≫ Proj.awayι _ (X c) (X_mem c) one_pos := by
  obtain ⟨ξ, e⟩ : ∃ ξ : Spec (CommRingCat.of Ω) ⟶ Proj (homogeneousSubmodule κ o), ∀ c,
      ξ = CptModel.pt (chartEval x c (hx c)) ≫ Proj.awayι _ (X c) (X_mem c) one_pos :=
    ⟨CptModel.pt (chartEval x c₀ (hx c₀)) ≫ Proj.awayι _ (X c₀) (X_mem c₀) one_pos, fun c =>
      pt_awayι_eq _ _ (X_mem c₀) (X_mem c) one_pos one_pos _ _⟩
  have hi := fun c => chartEval_injective x c (hx c) hinj
  have ch := fun c => chart ξ _ (hi c) _ (e c)
  have hr : ∀ c (q : Proj (homogeneousSubmodule κ o)), q ∈ Proj.basicOpen _ (X c) →
      ∃ p, Proj.awayι _ (X c) (X_mem c) one_pos p = q := fun c q hq => by
    rw [← Proj.opensRange_awayι _ _ (X_mem c) one_pos] at hq
    exact hq
  have hr' : ∀ c p, Proj.awayι (homogeneousSubmodule κ o) (X c) (X_mem c) one_pos p ∈
      Proj.basicOpen _ (X c) := fun c p => by
    rw [← Proj.opensRange_awayι _ _ (X_mem c) one_pos]
    exact ⟨p, rfl⟩
  have hreg : ∀ c p h a, a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) →
      a ∈ regAt ξ ⟨Proj.awayι (homogeneousSubmodule κ o) (X c) (X_mem c) one_pos p, h⟩ := by
    intro c p h a ha
    obtain ⟨z, rfl⟩ := (mem_range_chartEval x c (hx c) a).2 ha
    obtain ⟨_, -, h2⟩ := ch c p
    exact (h2 _).2 ⟨z, 1, (Ideal.ne_top_iff_one _).1 p.2.ne_top, by simp, by simp⟩
  have hin : ∀ c (p : Cpt ξ), InChart ξ x c p ↔ p.1 ∈ Proj.basicOpen _ (X c) := by
    rintro c ⟨q, h⟩
    constructor
    · rintro ⟨-, hc⟩
      obtain ⟨d, hd⟩ := exists_mem_basicOpen q
      obtain ⟨p, rfl⟩ := hr d q hd
      obtain ⟨_, -, h2⟩ := ch d p
      obtain ⟨a, s, hs, -, eq⟩ := (h2 _).1 (hc d)
      have h3 := Proj.awayι_preimage_basicOpen (homogeneousSubmodule κ o) (X_mem d) one_pos
        (X_mem c) one_pos
      have h4 : s = a * Away.isLocalizationElem (X_mem d) (X_mem c) := by
        apply hi d
        have h5 : chartEval x d (hx d) (Away.isLocalizationElem (X_mem (o := o) d) (X_mem c)) =
            x c / x d := (chartEval_mk x d (hx d) 1 _ _).trans (by simp)
        rw [map_mul, h5, ← eq]
        have := hx c
        have := hx d
        field_simp
      have h6 : p ∈ Proj.awayι (homogeneousSubmodule κ o) (X d) (X_mem d) one_pos ⁻¹ᵁ
          Proj.basicOpen _ (X c) := by
        rw [h3]
        intro hm
        exact hs (h4 ▸ Ideal.mul_mem_left _ a hm)
      exact h6
    · intro hq
      obtain ⟨p, rfl⟩ := hr c q hq
      exact ⟨hx c, fun j => hreg c p h _ (Algebra.subset_adjoin ⟨j, rfl⟩)⟩
  have hinjall : ∀ p : Cpt ξ, Function.Injective (genMap ξ p) := by
    rintro ⟨q, h⟩
    obtain ⟨d, hd⟩ := exists_mem_basicOpen q
    obtain ⟨p, rfl⟩ := hr d q hd
    exact (ch d p).2.1
  refine ⟨ξ, ⟨⟨?_, hinjall⟩, fun p => ?_, fun c _ => ?_, fun c _ a => ⟨fun ha => ?_, fun ha => ?_⟩⟩, e⟩
  · rw [← CptModel.genMap_self]
    refine ⟨hinjall _, fun a => ?_⟩
    obtain ⟨u, hu, v, hv, h0, huv⟩ := hgen a
    have hs : CptModel.self ξ = ⟨Proj.awayι (homogeneousSubmodule κ o) (X c₀) (X_mem c₀) one_pos
        (genPt (CptModel.pt (chartEval x c₀ (hx c₀)))), (ch c₀ _).1⟩ :=
      Subtype.ext (congrArg genPt (e c₀))
    change a ∈ regAt ξ (CptModel.self ξ)
    rw [hs]
    obtain ⟨u, rfl⟩ := (mem_range_chartEval x c₀ (hx c₀) _).2 hu
    obtain ⟨v, rfl⟩ := (mem_range_chartEval x c₀ (hx c₀) _).2 hv
    refine ((ch c₀ _).2.2 _).2 ⟨u, v, ?_, h0, huv⟩
    rw [CptModel.genPt_asIdeal]
    exact h0
  · obtain ⟨d, hd⟩ := exists_mem_basicOpen p.1
    exact ⟨d, (hin d p).2 hd⟩
  · refine ⟨Proj.basicOpen _ (X c), Proj.isAffineOpen_basicOpen _ _ (X_mem c) one_pos,
      fun q => ⟨fun hq => ?_, fun ⟨h, hq⟩ => (hin c ⟨q, h⟩).1 hq⟩⟩
    obtain ⟨p, rfl⟩ := hr c q hq
    exact ⟨(ch c p).1, (hin c ⟨_, (ch c p).1⟩).2 hq⟩
  · rintro ⟨q, h⟩ hq
    obtain ⟨p, rfl⟩ := hr c q ((hin c ⟨q, h⟩).1 hq)
    exact hreg c p h a ha
  · refine (mem_range_chartEval x c (hx c) a).1 (mem_range_of_forall _ a fun p => ?_)
    obtain ⟨h, -, h2⟩ := ch c p
    exact (h2 a).1 (ha ⟨_, h⟩ ((hin c ⟨_, h⟩).2 (hr' c p)))

def ratio (c j : κ) : Away (homogeneousSubmodule κ o) (X c : MvPolynomial κ o) :=
  Away.mk _ (X_mem c) 1 (X j) (X_mem j)

theorem chartEval_ratio (x : κ → Ω) (c j : κ) (hc : x c ≠ 0) :
    chartEval (o := o) x c hc (ratio c j) = x j / x c := (chartEval_mk x c hc 1 _ _).trans (by simp)

def cst (c : κ) (a : o) : Away (homogeneousSubmodule κ o) (X c : MvPolynomial κ o) :=
  Away.mk _ (X_mem c) 0 (C a) (isHomogeneous_C κ a)

theorem chartEval_cst (x : κ → Ω) (c : κ) (hc : x c ≠ 0) (a : o) :
    chartEval (o := o) x c hc (cst c a) = algebraMap o Ω a := (chartEval_mk x c hc 0 _ _).trans (by simp)

theorem valAt_pow {Y : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ Y} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ Y} {a : Ω} {r : R} (h : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  obtain ⟨hz, t, rfl, rfl⟩ := h
  exact ⟨hz, t ^ n, map_pow _ _ _, map_pow _ _ _⟩

theorem mem_regAt_of_valAt {Y : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ Y} {R : Type} [CommRing R]
    [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ Y} {a : Ω} {r : R} (h : ValAt ξ z a r)
    (h0 : genPt ξ ⤳ centre z) : a ∈ regAt ξ ⟨centre z, h0⟩ := by
  obtain ⟨hz, t, rfl, rfl⟩ := h
  exact ⟨t, rfl⟩

end Proj

end GlobalTheory.CompanionTheory.Ar.Flat.ProjectiveLinePlaces
