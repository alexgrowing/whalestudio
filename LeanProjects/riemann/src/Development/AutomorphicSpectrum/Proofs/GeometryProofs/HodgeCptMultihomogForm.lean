import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFormNotInCoordIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAbelianLocus
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.RangeJSubsetAbLocus
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.HInterior

open GlobalTheory.CompanionTheory.Ar.Flat.CptIn.Intr GlobalTheory.CompanionTheory.Ar.Flat.UnitChart

section Noeth

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {κ : Type} [Finite κ]

theorem isNoetherianRing_chart (ξ : Spec (CommRingCat.of Ω) ⟶ X) (x : κ → Ω) (hT : CoordTie ℤ ξ x) (c : κ)
    (hc : x c ≠ 0) (U : X.Opens) (hU : IsAffineOpen U)
    (hUm : ∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩) (hη : genPt ξ ∈ U) :
    IsNoetherianRing Γ(X, U) := by
  have sp : ∀ q : X, q ∈ U → genPt ξ ⤳ q := fun q hq => ((hUm q).1 hq).1
  let A : Subalgebra ℤ Ω := Algebra.adjoin ℤ (Set.range fun j => x j / x c)
  have hreg : ∀ a : Ω, a ∈ A ↔ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
    intro a
    refine (hT.ring c hc a).trans (forall_congr' fun q => imp_congr ?_ Iff.rfl)
    exact ⟨fun hq => (hUm q.1).2 ⟨q.2, hq⟩, fun hq => ((hUm q.1).1 hq).2⟩
  let ρ : Γ(X, U) →+* A := (ev ξ U hη).codRestrict A
    fun s => (hreg _).2 fun q hq => ⟨_, genMap_germ hη q hq s⟩
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_zero]
    intro s hs
    have h0 : ev ξ U hη s = 0 := congrArg Subtype.val hs
    refine TopCat.Presheaf.section_ext X.sheaf U s 0 fun q hq => ?_
    apply hT.gen.inj ⟨q, sp q hq⟩
    have h1 := genMap_germ hη ⟨q, sp q hq⟩ hq s
    rw [h0] at h1
    refine h1.trans ?_
    simp only [map_zero]
    exact (map_zero (genMap ξ ⟨q, sp q hq⟩)).symm
  have hsurj : Function.Surjective ρ := by
    rintro ⟨a, ha⟩
    obtain ⟨s, hs⟩ := exists_ev_eq hU hη sp a ((hreg a).1 ha)
    exact ⟨s, Subtype.ext hs⟩
  haveI : Algebra.FiniteType ℤ A :=
    (Subalgebra.fg_iff_finiteType A).1 (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  exact isNoetherianRing_of_ringEquiv A (RingEquiv.ofBijective ρ ⟨hinj, hsurj⟩).symm

theorem isLocallyNoetherian_of_coordTie (ξ : Spec (CommRingCat.of Ω) ⟶ X) (x : κ → Ω) (hT : CoordTie ℤ ξ x)
    (hall : ∀ q : X, genPt ξ ⤳ q) : IsLocallyNoetherian X := by
  have key : ∀ p : X, ∃ U : X.affineOpens, p ∈ U.1 ∧ IsNoetherianRing Γ(X, U.1) := by
    intro p
    obtain ⟨c, hch⟩ := hT.cover ⟨p, hall p⟩
    obtain ⟨U, hU, hUm⟩ := hT.affine c hch.1
    have hp : p ∈ U := (hUm p).2 ⟨hall p, hch⟩
    exact ⟨⟨U, hU⟩, hp, isNoetherianRing_chart ξ x hT c hch.1 U hU hUm ((hall p).mem_open U.isOpen hp)⟩
  choose S hS hN using key
  exact isLocallyNoetherian_of_affine_cover (S := S)
    (top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hS p⟩) hN

end Noeth

section Form

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem exists_homog_form_point (ξ : Spec (CommRingCat.of Ω) ⟶ X) (y : (Σ k, J k) → Ω)
    (hT : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) (V : X.Opens) (hV : genPt ξ ∈ V) :
    ∃ (f : MRing J) (d : K → ℕ), IsMultiHomog f d ∧ f ∉ mCoordIdeal y ∧ ∀ w ∈ mcPts (mCoordIdeal y), evC w f ≠ 0 →
      ∃ z : Spec (CommRingCat.of ℂ) ⟶ X, CoordsAt ξ y z w ∧ centre z ∈ V := by
  classical
  obtain ⟨c, hch⟩ := hT.cover ⟨genPt ξ, specializes_rfl⟩
  have hcx := hch.1
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hcx k (Finset.mem_univ k)
  obtain ⟨U, hU, hUm⟩ := hT.affine c hcx
  have hη : genPt ξ ∈ U := (hUm _).2 ⟨specializes_rfl, hch⟩
  have sp : ∀ q : X, q ∈ U → genPt ξ ⤳ q := fun q hq => ((hUm q).1 hq).1
  have hreg : ∀ a : Ω, a ∈ chartRingZ y c ↔ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
    intro a
    have h := hT.ring c hcx a
    rw [show (Algebra.adjoin ℤ (Set.range fun j : (∀ k, J k) => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)) =
      chartRingZ y c from segre_chart y c hc] at h
    refine h.trans (forall_congr' fun q => imp_congr ?_ Iff.rfl)
    exact ⟨fun hq => (hUm q.1).2 ⟨q.2, hq⟩, fun hq => ((hUm q.1).1 hq).2⟩
  let ρ : Γ(X, U) →+* chartRingZ y c := (ev ξ U hη).codRestrict (chartRingZ y c)
    fun s => (hreg _).2 fun q hq => ⟨_, genMap_germ hη q hq s⟩
  obtain ⟨s, hsV, hsη⟩ := hU.exists_basicOpen_le (V := V) ⟨genPt ξ, hV⟩ hη
  have ha0 : ev ξ U hη s ≠ 0 :=
    (((Scheme.mem_basicOpen X s _ hη).1 hsη).map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  obtain ⟨g₀, hg₀⟩ := ratMap_surjective y c (ρ s)
  obtain ⟨m, G₀, hG₀, eG⟩ := exists_form c g₀
  have hy₀ : aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) g₀ = ev ξ U hη s := by
    rw [← ratMap_coe, hg₀]
    rfl
  have hf0 : aeval y (G₀ * cMon c 1) ≠ 0 := by
    rw [map_mul, aeval_cMon, ← eG Ω y hc, hy₀]
    exact mul_ne_zero (mul_ne_zero ha0 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)))
      (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))
  refine ⟨G₀ * cMon c 1, m + 1, homog_mul hG₀ (homog_cMon c 1), fun hmem => hf0 ?_, fun w hw hne => ?_⟩
  · have h := aeval_scaled y (fun _ => 1) (G₀ * cMon c 1)
    have h0 : mConeMap y (G₀ * cMon c 1) = 0 := hmem
    rw [h0, map_zero] at h
    simpa only [mul_one] using h
  have hne' : aeval w (G₀ * cMon c 1) ≠ 0 := by
    rw [← evC_eq_aeval]
    exact hne
  rw [map_mul, aeval_cMon] at hne'
  have hwc : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => by
    have := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hne') k (Finset.mem_univ k)
    simpa using this
  obtain ⟨e, he⟩ := exists_chartEval y c hc w hw hwc
  obtain ⟨z, hz, hval⟩ := exists_pt hU (e.comp ρ)
  have hval' : ∀ k i, ∃ s : Γ(X, U), ev ξ U hη s = y ⟨k, i⟩ / y ⟨k, c k⟩ ∧
      (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U _ hz s) = w ⟨k, i⟩ / w ⟨k, c k⟩ := by
    intro k i
    have hm : y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ chartRingZ y c := Algebra.subset_adjoin ⟨⟨k, i⟩, rfl⟩
    obtain ⟨s, hs⟩ := exists_ev_eq hU hη sp _ ((hreg _).1 hm)
    refine ⟨s, hs, ?_⟩
    have e1 : ρ s = ratMap y c (MvPolynomial.X ⟨k, i⟩) := Subtype.ext (by rw [ratMap_coe, aeval_X]; exact hs)
    rw [hval]
    change e (ρ s) = _
    rw [e1, he, aeval_X]
  have hs0 : (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U _ hz s) ≠ 0 := by
    rw [hval]
    change e (ρ s) ≠ 0
    rw [← hg₀, he]
    intro h0
    apply left_ne_zero_of_mul hne'
    rw [← eG ℂ w hwc, h0, zero_mul]
  refine ⟨z, ⟨fun k => ⟨c k, (IsUnit.mk0 _ (hwc k))⟩, fun k c₀ hu => ?_⟩, hsV ?_⟩
  · have hw0 : w ⟨k, c₀⟩ ≠ 0 := hu.ne_zero
    obtain ⟨sv, hsv, hev⟩ := hval' k c₀
    have hev0 : (Scheme.stalkClosedPointTo z).hom (X.presheaf.germ U _ hz sv) ≠ 0 := by
      rw [hev]
      exact div_ne_zero hw0 (hwc k)
    have hy0 : y ⟨k, c₀⟩ ≠ 0 := by
      intro h0
      apply hev0
      have h1 : ρ sv = 0 := Subtype.ext (by
        change ev ξ U hη sv = 0
        rw [hsv, h0, zero_div])
      rw [hval]
      change e (ρ sv) = 0
      rw [h1, map_zero]
    refine ⟨hy0, fun i => ?_⟩
    obtain ⟨su, hsu, heu⟩ := hval' k i
    refine ⟨w ⟨k, i⟩ / w ⟨k, c₀⟩, ?_, by field_simp⟩
    have h := valAt_quot hη sp z hz su sv hev0
    rw [hsu, hsv, heu, hev, div_div_div_cancel_right₀ (hc k), div_div_div_cancel_right₀ (hwc k)] at h
    exact h
  · exact (Scheme.mem_basicOpen X s _ hz).2
      (isUnit_of_map_unit (Scheme.stalkClosedPointTo z).hom _ (IsUnit.mk0 _ hs0))

end Form

end GlobalTheory.CompanionTheory.Ar.Cmp.HInterior

theorem GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.exists_form_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (A : HodgeCpt Y S y) (x : Sp Ω ⟶ Xo.XF c), A.ξ ≫ A.f = x ≫ Y.j → Mono (spMap β) → ∃ (b : MRing ι) (d : K → ℕ), IsMultiHomog b d ∧ b ∉ mCoordIdeal y ∧ ∀ w ∈ mcPts (mCoordIdeal y), evC w b ≠ 0 → ∃ z : Spec (CommRingCat.of ℂ) ⟶ A.X, CoordsAt A.ξ y z w ∧ A.Interior z := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ ι _ y A x hx _
  haveI : IsLocallyNoetherian A.X := GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.isLocallyNoetherian_of_coordTie A.ξ _ A.tie A.all
  let V : A.X.Opens := ⟨abLocus A.t.G, GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian A.t.G A.t.semi⟩
  have hV : genPt A.ξ ∈ V := by
    refine (ReciprocityTheory.ChartRestriction.G.Geo.Tor.abLocus_pullback abLocusOne Y.t.semi A.m.cart.1 (genPt A.ξ)).1 ?_
    have h1 : A.f (genPt A.ξ) = Y.j (x (IsLocalRing.closedPoint Ω)) := by
      have := congrArg (fun g : Sp Ω ⟶ Y.X => g (IsLocalRing.closedPoint Ω)) hx
      exact (Scheme.Hom.comp_apply _ _ _).symm.trans (this.trans (Scheme.Hom.comp_apply _ _ _))
    rw [h1]
    exact GlobalTheory.ModelScope.range_j_subset_abLocus Y ⟨_, rfl⟩
  obtain ⟨b, d, hb, hbI, hw⟩ := GlobalTheory.CompanionTheory.Ar.Cmp.HInterior.exists_homog_form_point A.ξ y A.tie V hV
  refine ⟨b, d, hb, hbI, fun w hwm hne => ?_⟩
  obtain ⟨z, hz, hzV⟩ := hw w hwm hne
  exact ⟨z, hz, hzV⟩
