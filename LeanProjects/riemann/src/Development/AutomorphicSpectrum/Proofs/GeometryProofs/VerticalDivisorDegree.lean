import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPts
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomogeneousFormNonvanishingPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InjectiveOfIsCptGen
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionsNonzero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.VertForm

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

variable {K : Type} [Fintype K] [DecidableEq K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

abbrev segCo (y : (Σ k, J k) → Ω) : ((k : K) → J k) → Ω := fun c' => ∏ k, y ⟨k, c' k⟩

abbrev chartA (y : (Σ k, J k) → Ω) (c : (k : K) → J k) : Subalgebra ℤ Ω :=
  Algebra.adjoin ℤ (Set.range fun j => segCo y j / segCo y c)

def ym (y : (Σ k, J k) → Ω) (c : (k : K) → J k) (d : K → ℕ) : Ω := ∏ k, y ⟨k, c k⟩ ^ d k

variable {y : (Σ k, J k) → Ω} {c : (k : K) → J k}

theorem aeval_xpow (y : (Σ k, J k) → Ω) (c : (k : K) → J k) (d : K → ℕ) :
    MvPolynomial.aeval y (xpow c d) = ym y c d := by
  simp [xpow, ym, map_prod]

theorem ym_add (y : (Σ k, J k) → Ω) (c : (k : K) → J k) (d e : K → ℕ) :
    ym y c (d + e) = ym y c d * ym y c e := by
  simp [ym, pow_add, Finset.prod_mul_distrib]

theorem ym_ne_zero (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (d : K → ℕ) : ym y c d ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)

theorem xpow_notMem {W : Ideal (MRing J)} [hW : W.IsPrime] (hc : ∀ k, (MvPolynomial.X ⟨k, c k⟩ : MRing J) ∉ W)
    (d : K → ℕ) : xpow c d ∉ W := by
  intro h
  obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff).1 h
  exact hc k (hW.mem_of_pow_mem _ hk)

theorem mh_add {f g : MRing J} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem mh_sub {f g : MRing J} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  rw [sub_eq_add_neg]
  refine mh_add hf fun m hm k => hg m ?_ k
  rwa [MvPolynomial.support_neg] at hm

def IsRep (y : (Σ k, J k) → Ω) (c : (k : K) → J k) (s : Ω) (d : K → ℕ) (G : MRing J) : Prop :=
  IsMultiHomog G d ∧ MvPolynomial.aeval y G = s * ym y c d

theorem IsRep.mul {s s' : Ω} {d d' : K → ℕ} {G G' : MRing J} (h : IsRep y c s d G) (h' : IsRep y c s' d' G') :
    IsRep y c (s * s') (d + d') (G * G') :=
  ⟨ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul h.1 h'.1, by rw [map_mul, h.2, h'.2, ym_add]; ring⟩

theorem IsRep.add {s s' : Ω} {d d' : K → ℕ} {G G' : MRing J} (h : IsRep y c s d G) (h' : IsRep y c s' d' G') :
    IsRep y c (s + s') (d + d') (G * xpow c d' + G' * xpow c d) :=
  ⟨mh_add (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul h.1 (isMultiHomog_xpow c d'))
      (by rw [add_comm d d']; exact ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul h'.1 (isMultiHomog_xpow c d)),
    by rw [map_add, map_mul, map_mul, aeval_xpow, aeval_xpow, h.2, h'.2, ym_add]; ring⟩

theorem exists_rep (hc : segCo y c ≠ 0) {s : Ω} (hs : s ∈ chartA y c) : ∃ d G, IsRep y c s d G := by
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨1, xpow j 1, isMultiHomog_xpow _ _, ?_⟩
    have e : ∀ c', ym y c' 1 = segCo y c' := fun c' => by simp [ym, segCo]
    rw [aeval_xpow, e, e, div_mul_cancel₀ _ hc]
  | algebraMap n => exact ⟨0, MvPolynomial.C n, isMultiHomog_C_zero n, by simp [ym]⟩
  | add a b _ _ ha hb =>
    obtain ⟨d, G, h⟩ := ha
    obtain ⟨d', G', h'⟩ := hb
    exact ⟨_, _, h.add h'⟩
  | mul a b _ _ ha hb =>
    obtain ⟨d, G, h⟩ := ha
    obtain ⟨d', G', h'⟩ := hb
    exact ⟨_, _, h.mul h'⟩

theorem IsRep.mem_of_mem {W : Ideal (MRing J)} [hW : W.IsPrime] (hP : mCoordIdeal y ≤ W)
    (hc : ∀ k, (MvPolynomial.X ⟨k, c k⟩ : MRing J) ∉ W) {s : Ω} {d d' : K → ℕ} {G G' : MRing J}
    (h : IsRep y c s d G) (h' : IsRep y c s d' G') (hG : G ∈ W) : G' ∈ W := by
  have h0 : G * xpow c d' - G' * xpow c d ∈ mCoordIdeal y := by
    refine mem_mCoordIdeal_of_aeval_eq_zero y (d := d + d')
      (mh_sub (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul h.1 (isMultiHomog_xpow c d'))
        (by rw [add_comm d d']; exact ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul h'.1 (isMultiHomog_xpow c d))) ?_
    rw [map_sub, map_mul, map_mul, aeval_xpow, aeval_xpow, h.2, h'.2]
    ring
  have h1 : G' * xpow c d ∈ W := by
    have := W.sub_mem (W.mul_mem_right (xpow c d') hG) (hP h0)
    simpa using this
  exact (hW.mem_or_mem h1).resolve_right (xpow_notMem hc d)

theorem exists_prime (hsc : segCo y c ≠ 0) {W : Ideal (MRing J)} [hW : W.IsPrime] (hP : mCoordIdeal y ≤ W)
    (hc : ∀ k, (MvPolynomial.X ⟨k, c k⟩ : MRing J) ∉ W) :
    ∃ I : Ideal (chartA y c), I.IsPrime ∧
      ∀ s : chartA y c, s ∈ I ↔ ∃ d G, IsRep y c (s : Ω) d G ∧ G ∈ W := by
  let I : Ideal (chartA y c) :=
    { carrier := {s | ∃ d G, IsRep y c (s : Ω) d G ∧ G ∈ W}
      add_mem' := by
        rintro a b ⟨d, G, h, hG⟩ ⟨d', G', h', hG'⟩
        exact ⟨d + d', _, h.add h', W.add_mem (W.mul_mem_right _ hG) (W.mul_mem_right _ hG')⟩
      zero_mem' := ⟨0, 0, ⟨fun m hm => by simp at hm, by simp⟩, W.zero_mem⟩
      smul_mem' := by
        rintro r a ⟨d, G, h, hG⟩
        obtain ⟨e, R, hR⟩ := exists_rep hsc r.2
        exact ⟨e + d, R * G, hR.mul h, W.mul_mem_left _ hG⟩ }
  refine ⟨I, Ideal.isPrime_iff.2 ⟨fun ht => ?_, fun {a b} hab => ?_⟩, fun s => Iff.rfl⟩
  · have h1 : (1 : chartA y c) ∈ I := ht ▸ Submodule.mem_top
    obtain ⟨d, G, h, hG⟩ := h1
    have h2 : IsRep y c ((1 : chartA y c) : Ω) 0 1 := ⟨ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_one, by simp [ym]⟩
    exact hW.ne_top ((Ideal.eq_top_iff_one W).2 (h.mem_of_mem hP hc h2 hG))
  · obtain ⟨d, G, h, hG⟩ := hab
    obtain ⟨e, A, hA⟩ := exists_rep hsc a.2
    obtain ⟨e', B, hB⟩ := exists_rep hsc b.2
    have h3 : A * B ∈ W := h.mem_of_mem hP hc (hA.mul hB) hG
    rcases hW.mem_or_mem h3 with h4 | h4
    · exact Or.inl ⟨e, A, hA, h4⟩
    · exact Or.inr ⟨e', B, hB, h4⟩

theorem unitAt_mul {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {q : Cpt ξ} {a b : Ω}
    (ha : unitAt ξ q a) (hb : unitAt ξ q b) : unitAt ξ q (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩

theorem exists_frac {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hT : CoordTie ℤ ξ (segCo y))
    (hc : InChart ξ (segCo y) c (CptModel.self ξ)) (e : Ω) :
    ∃ (d : K → ℕ) (F G : MRing J), IsMultiHomog F d ∧ IsMultiHomog G d ∧ MvPolynomial.aeval y G ≠ 0 ∧
      MvPolynomial.aeval y F = e * MvPolynomial.aeval y G := by
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ k)
  obtain ⟨s, hs, hu, hse⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ _ (segCo y) hT c (CptModel.self ξ) hc e).1
    (by rw [CptModel.regAt_self hT.gen]; trivial)
  obtain ⟨d, G, hG⟩ := exists_rep hc.1 hs
  obtain ⟨d', F, hF⟩ := exists_rep hc.1 hse
  refine ⟨d' + d, F * xpow c d, G * xpow c d', ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hF.1 (isMultiHomog_xpow _ _),
    by rw [add_comm]; exact ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hG.1 (isMultiHomog_xpow _ _), ?_, ?_⟩
  · rw [map_mul, aeval_xpow, hG.2]
    exact mul_ne_zero (mul_ne_zero hu.1 (ym_ne_zero hy _)) (ym_ne_zero hy _)
  · rw [map_mul, map_mul, aeval_xpow, aeval_xpow, hG.2, hF.2]
    ring

theorem zpow_ym (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (a : K → ℤ) :
    (∏ k, y ⟨k, c k⟩ ^ a k) * ym y c (fun k => (-a k).toNat) = ym y c (fun k => (a k).toNat) := by
  rw [ym, ym, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hy k)]
  congr 1
  omega

theorem unit_off {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : ℕ} {Δ : Lat ξ Ω} {a : K → ℤ} {e₀ : Ω}
    (hT : CoordTie ℤ ξ (segCo y)) (hDeg : Δ.IsDegOn Set.univ y a e₀)
    (hΔ : ∀ q, ¬ InFibre ξ p q → Δ q = Submodule.span (regAt ξ q) {1}) {f g : MRing J} {bf bg : K → ℕ}
    (hf : IsMultiHomog f bf) (hg : IsMultiHomog g bg) (hb : ∀ k, (bf k : ℤ) - bg k = - a k)
    (hfg : MvPolynomial.aeval y f = e₀ * MvPolynomial.aeval y g) (W : Ideal (MRing J)) (hW : W.IsPrime)
    (hP : mCoordIdeal y ≤ W) (hrel : IsRelevant W) (hp : (MvPolynomial.C (p : ℤ) : MRing J) ∉ W) :
    ∃ u v : MRing J, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ mCoordIdeal y := by
  choose c hc using hrel
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hc k (hP (mem_mCoordIdeal_of_aeval_eq_zero y
    (isMultiHomog_X' k (c k)) (by simpa using h0)))
  have hsc : segCo y c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
  obtain ⟨I, hI, hmem⟩ := exists_prime hsc hP hc
  obtain ⟨q, ⟨hq, hu⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ ℤ _ (segCo y) hT c hsc I hI
  have hpI : (p : chartA y c) ∉ I := fun h => by
    obtain ⟨d, G, hr, hG⟩ := (hmem _).1 h
    have h2 : IsRep y c (((p : chartA y c)) : Ω) 0 (MvPolynomial.C (p : ℤ)) :=
      ⟨isMultiHomog_C_zero _, by simp [ym]⟩
    exact hp (hr.mem_of_mem hP hc h2 hG)
  have hpu : unitAt ξ q (p : Ω) := by simpa using (hu _).1 hpI
  have hΔ1 := hΔ q (fun hf' => hf' hpu)
  have hΔ2 := hDeg.2 q trivial c hq
  obtain ⟨s, hs⟩ : ∃ s, s = (∏ k, y ⟨k, c k⟩ ^ a k) * e₀ := ⟨_, rfl⟩
  rw [smul_eq_mul, ← hs] at hΔ2
  have hs1 : s ∈ Submodule.span (regAt ξ q) {(1 : Ω)} := by
    rw [← hΔ1, hΔ2]; exact Submodule.mem_span_singleton_self _
  have h1s : (1 : Ω) ∈ Submodule.span (regAt ξ q) {s} := by
    rw [← hΔ2, hΔ1]; exact Submodule.mem_span_singleton_self _
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hs1
  obtain ⟨r', hr'⟩ := Submodule.mem_span_singleton.1 h1s
  have hr2 : (r : Ω) = s := by simpa [Subring.smul_def] using hr
  have hr3 : (r' : Ω) * s = 1 := by simpa [Subring.smul_def] using hr'
  have hsu : unitAt ξ q s := ⟨right_ne_zero_of_mul_eq_one hr3, hr2 ▸ r.2, by
    rw [← eq_inv_of_mul_eq_one_left hr3]; exact r'.2⟩
  obtain ⟨t, ht, hut, hts⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ _ (segCo y) hT c q hq s).1 hsu.2.1
  have hv : (⟨t, ht⟩ : chartA y c) ∉ I := (hu _).2 hut
  have hu' : (⟨t * s, hts⟩ : chartA y c) ∉ I := (hu _).2 (unitAt_mul hut hsu)
  obtain ⟨dv, V, hV⟩ := exists_rep hsc ht
  obtain ⟨du, U, hU⟩ := exists_rep hsc hts
  have hVW : V ∉ W := fun h => hv ((hmem _).2 ⟨dv, V, hV, h⟩)
  have hUW : U ∉ W := fun h => hu' ((hmem _).2 ⟨du, U, hU, h⟩)
  have hZ := zpow_ym hy a
  refine ⟨V * xpow c (du + fun k => (a k).toNat), U * xpow c (dv + fun k => (-a k).toNat),
    fun h => (hW.mem_or_mem h).elim hVW (xpow_notMem hc _),
    fun h => (hW.mem_or_mem h).elim hUW (xpow_notMem hc _), ?_⟩
  refine mem_mCoordIdeal_of_aeval_eq_zero y (d := dv + (du + fun k => (a k).toNat) + bf)
    (mh_sub (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hV.1 (isMultiHomog_xpow _ _)) hf) ?_) ?_
  · have e : dv + (du + fun k => (a k).toNat) + bf = du + (dv + fun k => (-a k).toNat) + bg := by
      funext k
      have := hb k
      simp only [Pi.add_apply]
      omega
    rw [e]
    exact ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hU.1 (isMultiHomog_xpow _ _)) hg
  · rw [map_sub, map_mul, map_mul, map_mul, map_mul, aeval_xpow, aeval_xpow, hV.2, hU.2, hfg, ym_add, ym_add,
      ← hZ, hs]
    ring

end GlobalTheory.CompanionTheory.Ar.VertForm

theorem GlobalTheory.CompanionTheory.Ar.VertForm.exists_vertical : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (p : ℕ) (Δ : Lat ξ Ω) (a : K → ℤ) (e₀ : Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ q : X, genPt ξ ⤳ q) → Δ.IsDegOn Set.univ y a e₀ → (∀ q, ¬ InFibre ξ p q → Δ q = Submodule.span (regAt ξ q) {1}) → ∃ f g : MRing J, IsVerticalDivisorAt (mCoordIdeal y) p (-a) f g ∧ MvPolynomial.aeval y g ≠ 0 ∧ MvPolynomial.aeval y f / MvPolynomial.aeval y g = e₀ := by
  intro X Ω _ ξ K _ J _ y p Δ a e₀ hT _ hDeg hΔ
  classical
  obtain ⟨c, hc⟩ := hT.cover (CptModel.self ξ)
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ k)
  obtain ⟨d, F, G, hF, hG, hG0, hFG⟩ :=
    GlobalTheory.CompanionTheory.Ar.VertForm.exists_frac (y := y) hT hc (e₀ * ∏ k, y ⟨k, c k⟩ ^ a k)
  have hZ := GlobalTheory.CompanionTheory.Ar.VertForm.zpow_ym hy a
  have hg0 : MvPolynomial.aeval y (G * ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.xpow c fun k => (a k).toNat) ≠ 0 := by
    rw [map_mul, GlobalTheory.CompanionTheory.Ar.VertForm.aeval_xpow]
    exact mul_ne_zero hG0 (GlobalTheory.CompanionTheory.Ar.VertForm.ym_ne_zero hy _)
  have hfg : MvPolynomial.aeval y (F * ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.xpow c fun k => (-a k).toNat) =
      e₀ * MvPolynomial.aeval y (G * ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.xpow c fun k => (a k).toNat) := by
    rw [map_mul, map_mul, GlobalTheory.CompanionTheory.Ar.VertForm.aeval_xpow, GlobalTheory.CompanionTheory.Ar.VertForm.aeval_xpow, hFG, ← hZ]
    ring
  have hb : ∀ k, (((d + fun k => (-a k).toNat) k : ℕ) : ℤ) - ((d + fun k => (a k).toNat) k : ℕ) = -a k := by
    intro k
    simp only [Pi.add_apply]
    omega
  have hFm := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hF (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_xpow c fun k => (-a k).toNat)
  have hGm := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hG (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_xpow c fun k => (a k).toNat)
  refine ⟨_, _, ⟨⟨_, _, hFm, hGm, funext hb⟩, fun h => ?_, fun h => ?_, fun W hW hP hrel hp => ?_⟩, hg0, ?_⟩
  · exact mul_ne_zero hDeg.1 hg0 (hfg ▸ SegreChart.aeval_eq_zero_of_mem y h)
  · exact hg0 (SegreChart.aeval_eq_zero_of_mem y h)
  · exact GlobalTheory.CompanionTheory.Ar.VertForm.unit_off hT hDeg hΔ hFm hGm hb hfg W hW hP hrel hp
  · rw [hfg, mul_div_cancel_right₀ _ hg0]
