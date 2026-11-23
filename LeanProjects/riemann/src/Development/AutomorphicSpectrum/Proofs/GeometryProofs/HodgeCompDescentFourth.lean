import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChgUnit

theorem mem_regAt_of_valAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {R : Type}
    [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r : R} (h : ValAt ξ z a r) (p : Cpt ξ)
    (hp : p.1 = centre z) : a ∈ regAt ξ p := by
  obtain ⟨x, hx⟩ := p
  dsimp only at hp
  subst hp
  obtain ⟨_, s, hs, -⟩ := h
  exact ⟨s, hs⟩

theorem inChart_of_coordsAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type}
    [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ X} {w : (Σ k, J k) → R} (hw : CoordsAt ξ y z w) (c : (k : K) → J k)
    (hc : ∀ k, IsUnit (w ⟨k, c k⟩)) (p : Cpt ξ) (hp : p.1 = centre z) :
    InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p := by
  refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => (hw.2 k _ (hc k)).1, fun c' => ?_⟩
  show (∏ k, y ⟨k, c' k⟩) / (∏ k, y ⟨k, c k⟩) ∈ regAt ξ p
  rw [← Finset.prod_div_distrib]
  refine prod_mem fun k _ => ?_
  obtain ⟨r, hr, -⟩ := (hw.2 k _ (hc k)).2 (c' k)
  exact mem_regAt_of_valAt hr p hp

theorem exists_unit_of_span_eq {Ω : Type} [Field Ω] (R : Subring Ω) {a b : Ω} (ha : a ≠ 0)
    (h : Submodule.span R {a} = Submodule.span R {b}) : ∃ u : Ω, u ∈ R ∧ u⁻¹ ∈ R ∧ a = u * b := by
  have h1 : a ∈ Submodule.span R {b} := h ▸ Submodule.mem_span_singleton_self a
  have h2 : b ∈ Submodule.span R {a} := h ▸ Submodule.mem_span_singleton_self b
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 h2
  have hr' : (r : Ω) * b = a := hr
  have ht' : (t : Ω) * a = b := ht
  have hrt : (r : Ω) * t = 1 := by
    apply mul_right_cancel₀ ha
    rw [_root_.mul_assoc, ht', hr', _root_.one_mul]
  refine ⟨r, r.2, ?_, hr'.symm⟩
  rw [inv_eq_of_mul_eq_one_right hrt]
  exact t.2

theorem zpow_mem_of_inv_mem {Ω : Type} [Field Ω] (R : Subring Ω) {u : Ω} (h : u ∈ R) (h' : u⁻¹ ∈ R) (n : ℤ) :
    u ^ n ∈ R := by
  cases n with
  | ofNat m => simpa using pow_mem h m
  | negSucc m =>
    rw [zpow_negSucc, ← inv_pow]
    exact pow_mem h' _

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem tens_unit_eq {Λ : Lat ξ Ω} {p : Cpt ξ} {s : Ω} (hs : Λ.IsGenAt p s) (n : ℤ) :
    Lat.tens (fun _ : Unit => Λ) (fun _ => n) p = Submodule.span (regAt ξ p) {s ^ n} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro t ⟨s', hs', rfl⟩
    have h' := hs' ()
    obtain ⟨u, hu, hu', e⟩ := exists_unit_of_span_eq (regAt ξ p) h'.1 (h'.2.symm.trans hs.2)
    refine Submodule.mem_span_singleton.2 ⟨⟨u ^ n, zpow_mem_of_inv_mem _ hu hu' n⟩, ?_⟩
    show u ^ n * s ^ n = _
    simp [e, mul_zpow]
  · refine Submodule.span_le.2 ?_
    rintro t rfl
    exact Submodule.subset_span ⟨fun _ => s, fun _ => hs, by simp⟩

theorem exists_gen_of_tens {Λ : Lat ξ Ω} {p : Cpt ξ} {g : Ω} {n : ℤ} (hg : g ≠ 0)
    (h : Lat.tens (fun _ : Unit => Λ) (fun _ => n) p = Submodule.span (regAt ξ p) {g}) : ∃ s, Λ.IsGenAt p s := by
  by_contra hn
  have hempty : {t | ∃ s : Unit → Ω, (∀ i, Λ.IsGenAt p (s i)) ∧ t = ∏ i, s i ^ (fun _ => n) i} = ∅ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨s, hs, -⟩
    exact hn ⟨_, hs ()⟩
  have h0 : Lat.tens (fun _ : Unit => Λ) (fun _ => n) p = ⊥ := by
    show Submodule.span _ _ = ⊥
    rw [hempty, Submodule.span_empty]
  have hm : g ∈ Submodule.span (regAt ξ p) {g} := Submodule.mem_span_singleton_self g
  rw [← h, h0] at hm
  exact hg ((Submodule.mem_bot _).1 hm)

theorem exists_value_of_unit (hξ : IsCptGen ξ) (z : Spec (CommRingCat.of ℂ) ⟶ X) (hz : genPt ξ ⤳ centre z) {f : Ω}
    (hf : f ≠ 0) (h1 : f ∈ regAt ξ ⟨centre z, hz⟩) (h2 : f⁻¹ ∈ regAt ξ ⟨centre z, hz⟩) :
    ∃ u : ℂ, u ≠ 0 ∧ ValAt ξ z f u := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  have hst : s * t = 1 := hξ.inj ⟨centre z, hz⟩ (by rw [map_mul, hs, ht, map_one, mul_inv_cancel₀ hf])
  refine ⟨(Scheme.stalkClosedPointTo z).hom s, fun h0 => ?_, hz, s, hs, rfl⟩
  exact ((IsUnit.of_mul_eq_one t hst).map (Scheme.stalkClosedPointTo z).hom).ne_zero h0

theorem comparison_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀) (r : CMType H × Fin (D.p + D.q)), Function.Injective β → CharZero Ω → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → GenPull Fl₀ Fl i hd → (Fl₀.rootLat r).IsDegOn Set.univ y₀ a₀ e₀ → (Fl.rootLat r).IsDegOn Set.univ y a e → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → unitAt 𝔐.ξ p (i a) → unitAt 𝔐₀.ξ (pushCpt hd p) a) → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → CoordsAt 𝔐₀.ξ y₀ (z ≫ h) (fun p => w (blkV bk bx p))) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → ∀ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) → ∃ u : ℂ, u ≠ 0 ∧ ValAt 𝔐.ξ z (i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) u := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl bk bx a a₀ e e₀ r hβ hΩ
    hy hgen hdeg₀ hdeg hunit hreg hco z w hw cc c₀ hc hc₀
  haveI := hΩ
  have hz : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  let q : Cpt 𝔐.ξ := ⟨centre z, hz⟩
  let q₀ : Cpt 𝔐₀.ξ := pushCpt hd q
  have hw₀ := hco z w hw
  have huc : ∀ k, IsUnit (w ⟨k, cc k⟩) := fun k => IsUnit.mk0 _ (hc k)
  have huc₀ : ∀ k, IsUnit ((fun p => w (blkV bk bx p)) (⟨k, c₀ k⟩ : Σ k, J₀ k)) := fun k => IsUnit.mk0 _ (hc₀ k)
  have hq₀c : q₀.1 = centre (z ≫ h) := rfl
  have hq : (Fl.rootLat r) q = Submodule.span (regAt 𝔐.ξ q) {(∏ k, y ⟨k, cc k⟩ ^ a k) * e} :=
    hdeg.2 q trivial cc (inChart_of_coordsAt hw cc huc q rfl)
  have hq₀ : (Fl₀.rootLat r) q₀ = Submodule.span (regAt 𝔐₀.ξ q₀) {(∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀} :=
    hdeg₀.2 q₀ trivial c₀ (inChart_of_coordsAt hw₀ c₀ huc₀ q₀ hq₀c)
  have hg : (∏ k, y ⟨k, cc k⟩ ^ a k) * e ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw.2 k _ (huc k)).1) hdeg.1
  have hg₀ : (∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀ ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw₀.2 k _ (huc₀ k)).1) hdeg₀.1
  obtain ⟨s₀, hs₀⟩ := exists_gen_of_tens
    (Λ := (𝔐₀.V (HodgeCpt.rootIdx D r).1).gr (Fl₀.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2)
    (n := HodgeCpt.rootSgn D r) hg₀ hq₀
  have e₁ := tens_unit_eq hs₀ (HodgeCpt.rootSgn D r)
  obtain ⟨u₀, hu₀, hu₀', hgu⟩ := exists_unit_of_span_eq (regAt 𝔐₀.ξ q₀) hg₀ (hq₀.symm.trans e₁)
  have hs : ((𝔐.V (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2).IsGenAt q
      (i s₀) := hgen q (fun p hp => not_inFibre 𝔐.ξ z hz hp) _ _ s₀ hs₀
  have e₂ := tens_unit_eq hs (HodgeCpt.rootSgn D r)
  obtain ⟨v, hv, hv', hgv⟩ := exists_unit_of_span_eq (regAt 𝔐.ξ q) (zpow_ne_zero _ hs.1) (e₂.symm.trans hq)
  have hfe : i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, cc k⟩ ^ a k) * e) = i u₀ * v := by
    rw [hgu, map_mul, map_zpow₀, hgv, ← _root_.mul_assoc (i u₀) v]
    exact mul_div_cancel_right₀ _ hg
  have hf : i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, cc k⟩ ^ a k) * e) ≠ 0 :=
    div_ne_zero ((map_ne_zero i).2 hg₀) hg
  refine exists_value_of_unit 𝔐.tie.gen z hz hf ?_ ?_
  · rw [hfe]
    exact mul_mem (hreg q _ hu₀) hv
  · rw [hfe, mul_inv, ← map_inv₀]
    exact mul_mem (hreg q _ hu₀') hv'

end GlobalTheory.CompanionTheory.Ar.ChgUnit
