import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.EvalPt

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem aeval_div_mul_prod {F : Type} [Field F] (v : (Σ k, J k) → F) (t : K → F) (ht : ∀ k, t k ≠ 0)
    {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    aeval (fun p => v p / t p.1) g * ∏ k, t k ^ d k = aeval v g := by
  simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mul_assoc]
  congr 1
  have key : ∏ k, t k ^ d k = ∏ p : (Σ k, J k), t p.1 ^ m p := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  rw [key, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (ht p.1))]

theorem map_aeval_int {σ S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (s : σ → S) (f : MvPolynomial σ ℤ) :
    φ (aeval s f) = aeval (fun i => φ (s i)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem norm_evC_of_specializes {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {y : (Σ k, J k) → Ω} {z : Spec (CommRingCat.of ℂ) ⟶ X} {w : (Σ k, J k) → ℂ} {A : HermLine J} {c₀ : Ω} {C : ℝ}
    {g h : MRing J} {dg dh : K → ℕ} (hz : genPt ξ ⤳ centre z) (hco : CoordsAt ξ y z w)
    (hyp : ∀ (cc : (k : K) → J k) (u : ℂ), (∀ k, w ⟨k, cc k⟩ ≠ 0) →
      ValAt ξ z (c₀ / ∏ k, y ⟨k, cc k⟩ ^ A.a k) u → ‖u‖ * ∏ k, ‖w ⟨k, cc k⟩‖ ^ A.a k = C * A.h w)
    (hg : IsMultiHomog g dg) (hh : IsMultiHomog h dh) (hd : ∀ k, (dg k : ℤ) - dh k = A.a k)
    (he : aeval y g = c₀ * aeval y h) (hw : evC w h ≠ 0) :
    ‖evC w g‖ = C * A.h w * ‖evC w h‖ := by
  classical
  obtain ⟨hcov, hco2⟩ := hco
  choose cc hcc using hcov
  have hw0 : ∀ k, w ⟨k, cc k⟩ ≠ 0 := fun k => (hcc k).ne_zero
  have hy0 : ∀ k, y ⟨k, cc k⟩ ≠ 0 := fun k => (hco2 k (cc k) (hcc k)).1
  have hr : ∀ p : (Σ k, J k), ∃ s : X.presheaf.stalk (centre z),
      genMap ξ ⟨centre z, hz⟩ s = y p / y ⟨p.1, cc p.1⟩ ∧
      w p = (Scheme.stalkClosedPointTo z).hom s * w ⟨p.1, cc p.1⟩ := by
    rintro ⟨k, i⟩
    obtain ⟨r, ⟨h', s, hs1, hs2⟩, hwr⟩ := (hco2 k (cc k) (hcc k)).2 i
    exact ⟨s, hs1, by rw [hwr, ← hs2]⟩
  choose s hs1 hs2 using hr
  have hφ1 : ∀ f : MRing J, genMap ξ ⟨centre z, hz⟩ (aeval s f) =
      aeval (fun p => y p / y ⟨p.1, cc p.1⟩) f := by
    intro f
    rw [map_aeval_int]
    simp only [hs1]
  have hwr : ∀ p : (Σ k, J k), w p / w ⟨p.1, cc p.1⟩ = (Scheme.stalkClosedPointTo z).hom (s p) := fun p => by
    rw [hs2 p, mul_div_cancel_right₀ _ (hw0 p.1)]
  have hφ2 : ∀ f : MRing J, (Scheme.stalkClosedPointTo z).hom (aeval s f) =
      aeval (fun p => w p / w ⟨p.1, cc p.1⟩) f := by
    intro f
    refine (map_aeval_int (Scheme.stalkClosedPointTo z).hom s f).trans ?_
    simp only [← hwr]
    try rfl
  have hev : ∀ f : MRing J, evC w f = aeval w f := fun f => by
    simp only [evC, MvPolynomial.eval_map, MvPolynomial.aeval_def, algebraMap_int_eq]
  have hg1 : aeval (fun p => w p / w ⟨p.1, cc p.1⟩) g * ∏ k, w ⟨k, cc k⟩ ^ dg k = aeval w g :=
    aeval_div_mul_prod w (fun k => w ⟨k, cc k⟩) hw0 hg
  have hh1 : aeval (fun p => w p / w ⟨p.1, cc p.1⟩) h * ∏ k, w ⟨k, cc k⟩ ^ dh k = aeval w h :=
    aeval_div_mul_prod w (fun k => w ⟨k, cc k⟩) hw0 hh
  have hg2 : aeval (fun p => y p / y ⟨p.1, cc p.1⟩) g * ∏ k, y ⟨k, cc k⟩ ^ dg k = aeval y g :=
    aeval_div_mul_prod y (fun k => y ⟨k, cc k⟩) hy0 hg
  have hh2 : aeval (fun p => y p / y ⟨p.1, cc p.1⟩) h * ∏ k, y ⟨k, cc k⟩ ^ dh k = aeval y h :=
    aeval_div_mul_prod y (fun k => y ⟨k, cc k⟩) hy0 hh
  rw [hev, hev] at *
  set Pg := aeval (fun p => w p / w ⟨p.1, cc p.1⟩) g with hPg
  set Ph := aeval (fun p => w p / w ⟨p.1, cc p.1⟩) h with hPh
  set Qg := aeval (fun p => y p / y ⟨p.1, cc p.1⟩) g with hQg
  set Qh := aeval (fun p => y p / y ⟨p.1, cc p.1⟩) h with hQh
  have hTg : ∏ k, w ⟨k, cc k⟩ ^ dg k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hw0 k)
  have hTh : ∏ k, w ⟨k, cc k⟩ ^ dh k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hw0 k)
  have hYg : ∏ k, y ⟨k, cc k⟩ ^ dg k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy0 k)
  have hYh : ∏ k, y ⟨k, cc k⟩ ^ dh k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy0 k)
  have hPh0 : Ph ≠ 0 := by
    intro h0
    apply hw
    rw [← hh1, h0, zero_mul]
  have hunit : IsUnit (aeval s h : X.presheaf.stalk (centre z)) :=
    isUnit_of_map_unit (Scheme.stalkClosedPointTo z).hom _ (by rw [hφ2]; exact hPh0.isUnit)
  have hQh0 : Qh ≠ 0 := by
    have := (hunit.map (genMap ξ ⟨centre z, hz⟩)).ne_zero
    rwa [hφ1] at this
  have hyh0 : aeval y h ≠ 0 := by
    rw [← hh2]
    exact mul_ne_zero hQh0 hYh
  have hval : ValAt ξ z (c₀ / ∏ k, y ⟨k, cc k⟩ ^ A.a k) (Pg / Ph) := by
    refine ⟨hz, aeval s g * ↑hunit.unit⁻¹, ?_, ?_⟩
    · rw [map_mul, map_units_inv, IsUnit.unit_spec, hφ1, hφ1]
      have hpow : ∏ k, y ⟨k, cc k⟩ ^ A.a k = (∏ k, y ⟨k, cc k⟩ ^ dg k) / ∏ k, y ⟨k, cc k⟩ ^ dh k := by
        rw [← Finset.prod_div_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [← hd k, zpow_sub₀ (hy0 k), zpow_natCast, zpow_natCast]
      have hc0 : c₀ = (Qg * ∏ k, y ⟨k, cc k⟩ ^ dg k) / (Qh * ∏ k, y ⟨k, cc k⟩ ^ dh k) := by
        rw [hg2, hh2, he, mul_div_assoc, div_self hyh0, mul_one]
      rw [hpow, hc0, ← hQg, ← hQh]
      field_simp
      try ring
    · have hq : (aeval s g * ↑hunit.unit⁻¹ : X.presheaf.stalk (centre z)) * aeval s h = aeval s g := by
        rw [mul_assoc, Units.inv_mul_of_eq hunit.unit_spec, mul_one]
      have key2 := (RingHom.map_mul (Scheme.stalkClosedPointTo z).hom _ _).symm.trans
        (congrArg (Scheme.stalkClosedPointTo z).hom hq)
      rw [hφ2, hφ2] at key2
      exact (eq_div_iff hPh0).2 key2
  have key := hyp cc (Pg / Ph) hw0 hval
  have hnpow : ∏ k, ‖w ⟨k, cc k⟩‖ ^ A.a k =
      (∏ k, ‖w ⟨k, cc k⟩‖ ^ dg k) / ∏ k, ‖w ⟨k, cc k⟩‖ ^ dh k := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← hd k, zpow_sub₀ (norm_ne_zero_iff.2 (hw0 k)), zpow_natCast, zpow_natCast]
  have hnh : ∏ k, ‖w ⟨k, cc k⟩‖ ^ dh k ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hw0 k))
  have hPhn : ‖Ph‖ ≠ 0 := norm_ne_zero_iff.2 hPh0
  rw [← key, ← hg1, ← hh1, hnpow, norm_mul, norm_mul, norm_div, norm_prod, norm_prod]
  simp only [norm_pow]
  field_simp
  try ring

theorem norm_evC_of_forms : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [Nonempty K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (A : HermLine J) (c₀ : Ω) (C : ℝ) (g h : MRing J) (dg dh : K → ℕ), IsCptGen ξ → CoordsAt ξ y z w → (∀ (cc : (k : K) → J k) (u : ℂ), (∀ k, w ⟨k, cc k⟩ ≠ 0) → ValAt ξ z (c₀ / ∏ k, y ⟨k, cc k⟩ ^ A.a k) u → ‖u‖ * ∏ k, ‖w ⟨k, cc k⟩‖ ^ A.a k = C * A.h w) → IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) - dh k = A.a k) → aeval y g = c₀ * aeval y h → evC w h ≠ 0 → ‖evC w g‖ = C * A.h w * ‖evC w h‖ := by
  intro X Ω _ ξ K _ _ J _ y z w A c₀ C g h dg dh _ hco hyp hg hh hd he hw
  obtain ⟨k⟩ := ‹Nonempty K›
  obtain ⟨c, hc⟩ := hco.1 k
  obtain ⟨r, ⟨hz, _⟩, _⟩ := (hco.2 k c hc).2 c
  exact norm_evC_of_specializes hz hco hyp hg hh hd he hw

end GlobalTheory.CompanionTheory.Ar.Flat.EvalPt
