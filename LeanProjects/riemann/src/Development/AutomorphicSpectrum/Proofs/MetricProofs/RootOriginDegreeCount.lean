import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumFundCoMulSumIic
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCoordField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgebraicElementHomogRelation
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.RepAt

section Val

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {z : Spec (CommRingCat.of ℂ) ⟶ X}

def evalHom (z : Spec (CommRingCat.of ℂ) ⟶ X) : X.presheaf.stalk (centre z) →+* ℂ :=
  (Scheme.stalkClosedPointTo z).hom

theorem valAt_iff {a : Ω} {r : ℂ} : ValAt ξ z a r ↔ ∃ (h : genPt ξ ⤳ centre z) (s : X.presheaf.stalk (centre z)),
    genMap ξ ⟨centre z, h⟩ s = a ∧ evalHom z s = r := Iff.rfl

theorem valAt_add {a b : Ω} {r s : ℂ} (ha : ValAt ξ z a r) (hb : ValAt ξ z b s) : ValAt ξ z (a + b) (r + s) := by
  obtain ⟨h, g, hg, hr⟩ := valAt_iff.1 ha
  obtain ⟨h', g', hg', hs⟩ := valAt_iff.1 hb
  exact valAt_iff.2 ⟨h, g + g', by rw [map_add, hg, hg'], by rw [map_add, hr, hs]⟩

theorem valAt_mul {a b : Ω} {r s : ℂ} (ha : ValAt ξ z a r) (hb : ValAt ξ z b s) : ValAt ξ z (a * b) (r * s) := by
  obtain ⟨h, g, hg, hr⟩ := valAt_iff.1 ha
  obtain ⟨h', g', hg', hs⟩ := valAt_iff.1 hb
  exact valAt_iff.2 ⟨h, g * g', by rw [map_mul, hg, hg'], by rw [map_mul, hr, hs]⟩

theorem valAt_intCast (h : genPt ξ ⤳ centre z) (n : ℤ) : ValAt ξ z (n : Ω) (n : ℂ) :=
  valAt_iff.2 ⟨h, (n : X.presheaf.stalk (centre z)), map_intCast _ n, map_intCast _ n⟩

theorem value_ne_zero (hg : IsCptGen ξ) {a : Ω} {r : ℂ} (ha : ValAt ξ z a r)
    (hu : ∀ h : genPt ξ ⤳ centre z, unitAt ξ ⟨centre z, h⟩ a) : r ≠ 0 := by
  obtain ⟨h, g, hga, hr⟩ := valAt_iff.1 ha
  obtain ⟨h0, -, hi⟩ := hu h
  obtain ⟨t, ht⟩ := hi
  have h1 : g * t = 1 := hg.inj ⟨centre z, h⟩ (by rw [map_mul, map_one, ht, hga, mul_inv_cancel₀ h0])
  intro hr0
  have := congrArg (evalHom z) h1
  rw [map_mul, map_one, hr, hr0, zero_mul] at this
  exact zero_ne_one this

theorem not_inFibre (h : genPt ξ ⤳ centre z) {r : ℕ} (hr : r.Prime) : ¬ InFibre ξ r ⟨centre z, h⟩ := by
  intro hf
  apply hf
  have hz : (Scheme.stalkClosedPointTo z).hom (r : X.presheaf.stalk (centre z)) = (r : ℂ) := map_natCast _ r
  have hu : IsUnit (r : X.presheaf.stalk (centre z)) := GlobalTheory.CompanionTheory.Ar.CxVal.isUnit _ (by
    rw [hz]; exact_mod_cast hr.ne_zero)
  obtain ⟨t, ht⟩ := hu.exists_right_inv
  have e : (r : Ω) * genMap ξ ⟨centre z, h⟩ t = 1 := by
    have := congrArg (genMap ξ ⟨centre z, h⟩) ht
    rwa [map_mul, map_natCast, map_one] at this
  have h0 : (r : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one e
  refine ⟨h0, natCast_mem _ r, ⟨t, ?_⟩⟩
  exact eq_inv_of_mul_eq_one_right e

theorem valAt_prod {σ : Type} (hz : genPt ξ ⤳ centre z) (s : Finset σ) {a : σ → Ω} {r : σ → ℂ}
    (h : ∀ i, ValAt ξ z (a i) (r i)) : ValAt ξ z (∏ i ∈ s, a i) (∏ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using CxVal.one hz
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact CxVal.mul (h i) ih

end Val

section Forms

open GlobalTheory.CompanionTheory.Ar.AlgPoly

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

open Classical in
theorem form_X (k : K) (i : J k) : IsMultiHomog (X ⟨k, i⟩ : MRing J) (Pi.single k 1) := by
  intro m hm k'
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · simp [Finsupp.single_apply, Pi.single_apply, h, Ne.symm h]

theorem form_pow {f : MRing J} {a : K → ℕ} (h : IsMultiHomog f a) (n : ℕ) : IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using form_one
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact form_mul ih h

theorem form_prod {σ : Type} (s : Finset σ) (f : σ → MRing J) (a : σ → K → ℕ)
    (h : ∀ x ∈ s, IsMultiHomog (f x) (a x)) : IsMultiHomog (∏ x ∈ s, f x) (∑ x ∈ s, a x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using form_one
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    exact form_mul (h x (Finset.mem_insert_self x s)) (ih fun x' h' => h x' (Finset.mem_insert_of_mem h'))

theorem form_C (n : ℤ) : IsMultiHomog (C n : MRing J) (0 : K → ℕ) := by
  classical
  intro m hm k
  have h0 : m = 0 := by
    have := MvPolynomial.support_monomial_subset hm
    simpa using this
  simp [h0]

def mono (c : ∀ k, J k) (e : K → ℕ) : MRing J := ∏ k, X ⟨k, c k⟩ ^ e k

theorem form_mono (c : ∀ k, J k) (e : K → ℕ) : IsMultiHomog (mono c e) e := by
  classical
  have h := form_prod (J := J) Finset.univ (fun k => (X ⟨k, c k⟩ : MRing J) ^ e k)
    (fun k => e k • Pi.single k 1) fun k _ => form_pow (form_X k (c k)) (e k)
  have e1 : (∑ k, e k • (Pi.single k 1 : K → ℕ)) = e := by
    funext k'
    simp [Finset.sum_apply, Pi.single_apply]
  rw [e1] at h
  exact h

theorem aeval_mono {S : Type} [CommRing S] (v : (Σ k, J k) → S) (c : ∀ k, J k) (e : K → ℕ) :
    aeval v (mono c e) = ∏ k, v ⟨k, c k⟩ ^ e k := by
  simp [mono, map_prod, map_pow, aeval_X]

end Forms

end GlobalTheory.CompanionTheory.Ar.Small.RepAt

namespace GlobalTheory.CompanionTheory.Ar.Small.RepAt

section Chart

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar.AlgPoly

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {z : Spec (CommRingCat.of ℂ) ⟶ X} {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  {y : (Σ k, J k) → Ω} {w : (Σ k, J k) → ℂ}

theorem inChart_of_coords (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) (c : ∀ k, J k)
    (hc : ∀ k, IsUnit (w ⟨k, c k⟩)) : InChart ξ (fun c' : ∀ k, J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre z, hz⟩ := by
  refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => (hw.2 k (c k) (hc k)).1, fun c' => ?_⟩
  show (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩ ∈ _
  rw [← Finset.prod_div_distrib]
  refine prod_mem fun k _ => ?_
  obtain ⟨r, ⟨_, s, hs, -⟩, -⟩ := (hw.2 k (c k) (hc k)).2 (c' k)
  exact ⟨s, hs⟩

theorem exists_form_of_mem (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) (c : ∀ k, J k)
    (hc : ∀ k, IsUnit (w ⟨k, c k⟩)) {b : Ω}
    (hb : b ∈ Algebra.adjoin ℤ (Set.range fun c' : ∀ k, J k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩)) :
    ∃ (r : ℂ) (d : ℕ) (F : MRing J), ValAt ξ z b r ∧ IsMultiHomog F (fun _ => d) ∧
      aeval y F = b * (∏ k, y ⟨k, c k⟩) ^ d ∧ aeval w F = r * (∏ k, w ⟨k, c k⟩) ^ d := by
  have hM : ∏ k, y ⟨k, c k⟩ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => (hw.2 k (c k) (hc k)).1
  induction hb using Algebra.adjoin_induction with
  | mem b hb =>
    obtain ⟨c', rfl⟩ := hb
    choose r hr hr' using fun k => (hw.2 k (c k) (hc k)).2 (c' k)
    refine ⟨∏ k, r k, 1, mono c' fun _ => 1, ?_, form_mono c' _, ?_, ?_⟩
    · show ValAt ξ z ((∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) _
      rw [← Finset.prod_div_distrib]
      exact valAt_prod hz _ hr
    · rw [aeval_mono, pow_one]
      simp only [pow_one]
      exact (div_mul_cancel₀ _ hM).symm
    · rw [aeval_mono, pow_one, ← Finset.prod_mul_distrib]
      simp only [pow_one]
      exact Finset.prod_congr rfl fun k _ => hr' k
  | algebraMap n =>
    refine ⟨(n : ℂ), 0, C n, ?_, form_C n, ?_, ?_⟩
    · rw [eq_intCast]
      exact valAt_intCast hz n
    · simp
    · simp
  | add a b _ _ ha hb =>
    obtain ⟨r₁, d₁, F₁, v₁, f₁, y₁, w₁⟩ := ha
    obtain ⟨r₂, d₂, F₂, v₂, f₂, y₂, w₂⟩ := hb
    have e₂ : (fun _ : K => d₂) + (fun _ : K => d₁) = fun _ : K => d₁ + d₂ := by
      funext k
      simp [add_comm]
    refine ⟨r₁ + r₂, d₁ + d₂, F₁ * mono c (fun _ => d₂) + F₂ * mono c (fun _ => d₁), valAt_add v₁ v₂,
      form_add (form_mul f₁ (form_mono c _)) ?_, ?_, ?_⟩
    · rw [← e₂]
      exact form_mul f₂ (form_mono c _)
    · simp only [map_add, map_mul, y₁, y₂, aeval_mono, Finset.prod_pow]
      ring
    · simp only [map_add, map_mul, w₁, w₂, aeval_mono, Finset.prod_pow]
      ring
  | mul a b _ _ ha hb =>
    obtain ⟨r₁, d₁, F₁, v₁, f₁, y₁, w₁⟩ := ha
    obtain ⟨r₂, d₂, F₂, v₂, f₂, y₂, w₂⟩ := hb
    refine ⟨r₁ * r₂, d₁ + d₂, F₁ * F₂, CxVal.mul v₁ v₂, form_mul f₁ f₂, ?_, ?_⟩
    · simp only [map_mul, y₁, y₂]
      ring
    · simp only [map_mul, w₁, w₂]
      ring

theorem exists_forms_of_regAt (tie : CoordTie ℤ ξ fun c' : ∀ k, J k => ∏ k, y ⟨k, c' k⟩)
    (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) (c : ∀ k, J k) (hc : ∀ k, IsUnit (w ⟨k, c k⟩))
    (a : K → ℤ) (ε : Ω) (hρ : ε * ∏ k, y ⟨k, c k⟩ ^ (-a k) ∈ regAt ξ ⟨centre z, hz⟩) :
    ∃ (dg dh : K → ℕ) (G Hf : MRing J), IsMultiHomog G dg ∧ IsMultiHomog Hf dh ∧
      (∀ k, (dg k : ℤ) = dh k + a k) ∧ aeval y G = ε * aeval y Hf ∧ aeval y Hf ≠ 0 ∧ aeval w Hf ≠ 0 := by
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (hc k)).1
  have hM : ∏ k, y ⟨k, c k⟩ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
  have hW : ∏ k, w ⟨k, c k⟩ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => (hc k).ne_zero
  obtain ⟨s, hs, hsu, hsρ⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ _ _ tie c ⟨centre z, hz⟩
    (inChart_of_coords hz hw c hc) _).1 hρ
  obtain ⟨r, d, S, hr, fS, yS, wS⟩ := exists_form_of_mem hz hw c hc hs
  obtain ⟨-, e, G₀, -, fG, yG, -⟩ := exists_form_of_mem hz hw c hc hsρ
  have hr0 : r ≠ 0 := value_ne_zero tie.gen hr fun _ => hsu
  have ep : ∀ k, y ⟨k, c k⟩ ^ (-a k) * y ⟨k, c k⟩ ^ (a k).toNat = y ⟨k, c k⟩ ^ (-a k).toNat := by
    intro k
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hy k)]
    congr 1
    omega
  have ep' : (∏ k, y ⟨k, c k⟩ ^ (-a k)) * ∏ k, y ⟨k, c k⟩ ^ (a k).toNat = ∏ k, y ⟨k, c k⟩ ^ (-a k).toNat := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => ep k
  refine ⟨(fun _ => e) + (fun _ => d) + fun k => (a k).toNat, (fun _ => d) + (fun _ => e) + fun k => (-a k).toNat,
    G₀ * mono c (fun _ => d) * mono c (fun k => (a k).toNat),
    S * mono c (fun _ => e) * mono c (fun k => (-a k).toNat),
    form_mul (form_mul fG (form_mono c _)) (form_mono c _), form_mul (form_mul fS (form_mono c _)) (form_mono c _),
    fun k => ?_, ?_, ?_, ?_⟩
  · simp only [Pi.add_apply]
    push_cast
    have h1 : (((a k).toNat : ℕ) : ℤ) - (((-a k).toNat : ℕ) : ℤ) = a k := by omega
    linarith
  · simp only [map_mul, yG, yS, aeval_mono, Finset.prod_pow]
    rw [← ep']
    ring
  · simp only [map_mul, yS, aeval_mono, Finset.prod_pow]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hsu.1 (pow_ne_zero _ hM)) (pow_ne_zero _ hM))
      (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k))
  · simp only [map_mul, wS, aeval_mono, Finset.prod_pow]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hr0 (pow_ne_zero _ hW)) (pow_ne_zero _ hW))
      (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k).ne_zero)

end Chart

section Ident

theorem zpow_sum₀ {F σ : Type} [Field F] {u : F} (hu : u ≠ 0) (s : Finset σ) (f : σ → ℤ) :
    u ^ (∑ i ∈ s, f i) = ∏ i ∈ s, u ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ hu, ih]

theorem section_ident {K R F : Type} [Fintype K] [Fintype R] [Field F] (Y : K → F) (hY : ∀ k, Y k ≠ 0)
    (x : R → K → ℤ) (A : K → ℤ) (e : R → F) (n : R → ℤ) (q : ℕ) (k₀ : K)
    (hA : A k₀ = 1 ∧ ∀ k, k ≠ k₀ → A k = 0) (a : K → ℤ)
    (ha : ∀ k, a k = -(q : ℤ) * A k + ∑ r, -n r * x r k) (B : F) :
    B * (∏ r, e r ^ n r) * ∏ k, Y k ^ (-a k) = B * Y k₀ ^ q / ∏ r, ((∏ k, Y k ^ x r k) * e r) ^ (-n r) := by
  have h1 : ∀ k, Y k ^ (-a k) = (Y k ^ A k) ^ q * ∏ r, (Y k ^ x r k) ^ n r := by
    intro k
    have : -a k = A k * q + ∑ r, x r k * n r := by
      rw [ha k, neg_add, Finset.sum_congr rfl (fun r _ => show x r k * n r = -(-n r * x r k) by ring), Finset.sum_neg_distrib]
      ring
    rw [this, zpow_add₀ (hY k), zpow_mul, zpow_natCast, zpow_sum₀ (hY k)]
    simp only [zpow_mul]
  have h2 : ∏ k, (Y k ^ A k) ^ q = Y k₀ ^ q := by
    rw [Finset.prod_eq_single k₀ (fun k _ hk => by rw [hA.2 k hk]; simp) (by simp), hA.1, zpow_one]
  have h3 : ∏ k, Y k ^ (-a k) = Y k₀ ^ q * ∏ r, (∏ k, Y k ^ x r k) ^ n r := by
    simp only [h1, Finset.prod_mul_distrib]
    rw [h2, Finset.prod_comm]
    simp only [Finset.prod_zpow]
  rw [h3]
  simp only [zpow_neg, Finset.prod_inv_distrib, div_inv_eq_mul, mul_zpow, Finset.prod_mul_distrib]
  ring

end Ident

end GlobalTheory.CompanionTheory.Ar.Small.RepAt

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem origin_section_rep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (n₀ : Option (RootIx D) → ℤ) (N₀ : ℕ), (∀ r, n₀ (some r) = -Fx.n r) → n₀ none = -(Fx.q' : ℤ) → ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) ≠ 0 → ∀ w ∈ mcPts (mCoordIdeal RM.y), ∃ (dg dh : RM.K → ℕ) (G Hf : MRing RM.ι), IsMultiHomog G dg ∧ IsMultiHomog Hf dh ∧ (∀ k, (dg k : ℤ) = dh k + (combLine (RM.line 1) n₀).a k) ∧ aeval RM.y G = ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) * aeval RM.y Hf ∧ aeval RM.y Hf ≠ 0 ∧ aeval w Hf ≠ 0 := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or n₀ N₀ hn hnone hε w hw
  obtain ⟨z, hz, hco⟩ := (mem_mcPts_iff_exists_coordsAt Or.𝔐.X RM.Ω Or.𝔐.ξ RM.K RM.ι RM.y Or.𝔐.tie w).1 hw
  choose cc hcc using hco.1
  have hch := RepAt.inChart_of_coords hz hco cc hcc
  have hy : ∀ k, RM.y ⟨k, cc k⟩ ≠ 0 := fun k => (hco.2 k (cc k) (hcc k)).1
  refine RepAt.exists_forms_of_regAt Or.𝔐.tie hz hco cc hcc _ _ ?_
  have gens : ∀ r, (Or.Fl.rootLat r).IsGenAt ⟨centre z, hz⟩ ((∏ k, RM.y ⟨k, cc k⟩ ^ RM.xdeg r k) • Or.e r) :=
    fun r => ⟨smul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) (Or.lines r).1,
      (Or.lines r).2 _ trivial cc hch⟩
  have ht := GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.tens_isGenAt (fun r => -Fx.n r) gens
  have ya : Or.g (Fx.yf (Or.ix.symm (cc Or.k₀))) = RM.y ⟨Or.k₀, cc Or.k₀⟩ := by
    rw [← Or.y_eq, Equiv.apply_symm_apply]
  have hchi : InChart Or.𝔐.ξ (fun i' => Or.g (Fx.yf i')) (Or.ix.symm (cc Or.k₀)) ⟨centre z, hz⟩ := by
    refine ⟨?_, fun j => ?_⟩
    · show Or.g (Fx.yf (Or.ix.symm (cc Or.k₀))) ≠ 0
      rw [ya]; exact hy _
    · show Or.g (Fx.yf j) / Or.g (Fx.yf (Or.ix.symm (cc Or.k₀))) ∈ _
      rw [ya, ← Or.y_eq]
      exact Lat.block_ratio_mem hch Or.k₀ (Or.ix j)
  have heff := (Or.eff ⟨centre z, hz⟩ (fun r hr => RepAt.not_inFibre hz hr) _ _ hchi ht).1
  have hid := RepAt.section_ident (fun k => RM.y ⟨k, cc k⟩) hy RM.xdeg RM.A.a Or.e Fx.n Fx.q' Or.k₀ Or.A_deg
    (combLine (RM.line 1) n₀).a (fun k => ?_) ((N₀ : RM.Ω) * Or.g Fx.sE)
  · have key : ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) * ∏ k, RM.y ⟨k, cc k⟩ ^ (-(combLine (RM.line 1) n₀).a k) =
        (N₀ : RM.Ω) * (Or.g Fx.sE * Or.g (Fx.yf (Or.ix.symm (cc Or.k₀))) ^ Fx.q' /
          ∏ r, ((∏ k, RM.y ⟨k, cc k⟩ ^ RM.xdeg r k) • Or.e r) ^ (-Fx.n r)) := by
      rw [ya]
      simp only [smul_eq_mul]
      rw [hid, mul_assoc (N₀ : RM.Ω), mul_div_assoc, mul_div_assoc]
    rw [key]
    exact mul_mem (natCast_mem _ N₀) heff
  · show (∑ j, n₀ j • (RM.line 1 j).a) k = _
    rw [Finset.sum_apply, Fintype.sum_option]
    simp only [Pi.smul_apply, smul_eq_mul, hnone, hn]
    show -(Fx.q' : ℤ) * RM.A.a k + ∑ r, -Fx.n r * (RM.x 1 r).a k = _
    simp only [RM.x_deg]

end GlobalTheory.CompanionTheory.Ar.Small
