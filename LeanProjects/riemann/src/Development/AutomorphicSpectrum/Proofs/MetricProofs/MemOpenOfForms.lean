import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumFundCoMulSumIic
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCoordField
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund
open AlgebraicGeometry CategoryTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.FormsVal

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {z : Spec (CommRingCat.of ℂ) ⟶ X}

def valRing (ξ : Spec (CommRingCat.of Ω) ⟶ X) (z : Spec (CommRingCat.of ℂ) ⟶ X) (h : genPt ξ ⤳ centre z) :
    Subring (Ω × ℂ) :=
  ((genMap ξ ⟨centre z, h⟩).prod (Scheme.stalkClosedPointTo z).hom).range

theorem mem_valRing_of_valAt (h : genPt ξ ⤳ centre z) {a : Ω} {r : ℂ} (hv : ValAt ξ z a r) :
    (a, r) ∈ valRing ξ z h := by
  obtain ⟨h', s, hs, hr⟩ := hv
  exact ⟨s, Prod.ext hs hr⟩

theorem valAt_of_mem_valRing (h : genPt ξ ⤳ centre z) {a : Ω} {r : ℂ} (hv : (a, r) ∈ valRing ξ z h) :
    ValAt ξ z a r := by
  obtain ⟨s, hs⟩ := hv
  exact ⟨h, s, congrArg Prod.fst hs, congrArg Prod.snd hs⟩

theorem aeval_mem_valRing (h : genPt ξ ⤳ centre z) {σ : Type} {a : σ → Ω} {r : σ → ℂ}
    (hv : ∀ i, (a i, r i) ∈ valRing ξ z h) (f : MvPolynomial σ ℤ) :
    (aeval a f, aeval r f) ∈ valRing ξ z h := by
  induction f using MvPolynomial.induction_on with
  | C n =>
    have e : (aeval a (C n : MvPolynomial σ ℤ), aeval r (C n : MvPolynomial σ ℤ)) = ((n : Ω × ℂ)) :=
      Prod.ext (by simp) (by simp)
    rw [e]
    exact intCast_mem _ n
  | add f g hf hg =>
    have := add_mem hf hg
    simpa using this
  | mul_X f i hf =>
    have := mul_mem hf (hv i)
    simpa using this

theorem unitAt_of_mem_valRing (h : genPt ξ ⤳ centre z) {a : Ω} {r : ℂ} (hv : (a, r) ∈ valRing ξ z h) (hr : r ≠ 0) :
    unitAt ξ ⟨centre z, h⟩ a := by
  obtain ⟨s, hs⟩ := hv
  have hs1 : genMap ξ ⟨centre z, h⟩ s = a := congrArg Prod.fst hs
  have hs2 : (Scheme.stalkClosedPointTo z).hom s = r := congrArg Prod.snd hs
  have hl : IsLocalHom (Scheme.stalkClosedPointTo z).hom := Scheme.isLocalHom_stalkClosedPointTo z
  have hu : IsUnit s := hl.map_nonunit s ((congrArg IsUnit hs2).mpr hr.isUnit)
  obtain ⟨t, ht⟩ := hu.exists_right_inv
  have h1 : a * genMap ξ ⟨centre z, h⟩ t = 1 := by rw [← hs1, ← map_mul, ht, map_one]
  have ha0 : a ≠ 0 := left_ne_zero_of_mul_eq_one h1
  exact ⟨ha0, ⟨s, hs1⟩, ⟨t, eq_inv_of_mul_eq_one_right h1⟩⟩

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω}
  {w : (Σ k, ι k) → ℂ}

theorem ratio_mem_valRing (h : genPt ξ ⤳ centre z) (hc : CoordsAt ξ y z w) (c : (k : K) → ι k)
    (hu : ∀ k, w ⟨k, c k⟩ ≠ 0) (p : Σ k, ι k) :
    ((y ⟨p.1, c p.1⟩)⁻¹ * y p, (w ⟨p.1, c p.1⟩)⁻¹ * w p) ∈ valRing ξ z h := by
  obtain ⟨k, i⟩ := p
  obtain ⟨-, hr⟩ := hc.2 k (c k) (hu k).isUnit
  obtain ⟨r, hv, hw⟩ := hr i
  have e1 : (w ⟨k, c k⟩)⁻¹ * w ⟨k, i⟩ = r := by rw [hw]; field_simp [hu k]
  have e2 : (y ⟨k, c k⟩)⁻¹ * y ⟨k, i⟩ = y ⟨k, i⟩ / y ⟨k, c k⟩ := by rw [div_eq_mul_inv, mul_comm]
  show ((y ⟨k, c k⟩)⁻¹ * y ⟨k, i⟩, (w ⟨k, c k⟩)⁻¹ * w ⟨k, i⟩) ∈ _
  rw [e1, e2]
  exact mem_valRing_of_valAt h hv

theorem unitAt_form (h : genPt ξ ⤳ centre z) (hc : CoordsAt ξ y z w) (c : (k : K) → ι k)
    (hu : ∀ k, w ⟨k, c k⟩ ≠ 0) {G : MRing ι} {d : K → ℕ} (hG : IsMultiHomog G d) (hw : aeval w G ≠ 0) :
    unitAt ξ ⟨centre z, h⟩ (aeval y G / ∏ k, y ⟨k, c k⟩ ^ d k) := by
  have hm := aeval_mem_valRing h (ratio_mem_valRing h hc c hu) G
  rw [aeval_scale hG (fun k => (y ⟨k, c k⟩)⁻¹) y, aeval_scale hG (fun k => (w ⟨k, c k⟩)⁻¹) w] at hm
  have e : (∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k) * aeval y G = aeval y G / ∏ k, y ⟨k, c k⟩ ^ d k := by
    simp only [inv_pow, Finset.prod_inv_distrib]
    rw [div_eq_mul_inv, mul_comm]
  rw [e] at hm
  refine unitAt_of_mem_valRing h hm (mul_ne_zero ?_ hw)
  exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (inv_ne_zero (hu k))

end Val

section Field

variable {Ω : Type} [Field Ω]

theorem zpow_sum_eq_prod_zpow {R : Type} (Y : Ω) (hY : Y ≠ 0) (s : Finset R) (f : R → ℤ) :
    Y ^ (∑ r ∈ s, f r) = ∏ r ∈ s, Y ^ f r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert r s hr ih => rw [Finset.sum_insert hr, Finset.prod_insert hr, zpow_add₀ hY, ih]

theorem mono_identity {K R : Type} [Fintype K] [Fintype R] (Y : K → Ω) (hY : ∀ k, Y k ≠ 0) (e : R → Ω)
    (he : ∀ r, e r ≠ 0) (x : R → K → ℤ) (Aa : K → ℤ) (n : R → ℤ) (q : ℕ) (k₀ : K)
    (hA : Aa k₀ = 1 ∧ ∀ k, k ≠ k₀ → Aa k = 0) (a : K → ℤ)
    (ha : ∀ k, a k = -(q : ℤ) * Aa k + ∑ r, -n r * x r k) :
    (∏ k, Y k ^ a k)⁻¹ * ∏ r, e r ^ n r = Y k₀ ^ q / ∏ r, ((∏ k, Y k ^ x r k) • e r) ^ (-n r) := by
  classical
  have h1 : ∏ k, Y k ^ Aa k = Y k₀ := by
    rw [Finset.prod_eq_single k₀ (fun k _ hk => by rw [hA.2 k hk, zpow_zero]) (by simp), hA.1, zpow_one]
  have h2 : ∏ k, Y k ^ a k = (Y k₀ ^ q)⁻¹ * ∏ r, (∏ k, Y k ^ x r k) ^ (-n r) := by
    have e1 : ∀ k, Y k ^ a k = (Y k ^ Aa k) ^ (-(q : ℤ)) * ∏ r, (Y k ^ x r k) ^ (-n r) := fun k => by
      rw [ha k, zpow_add₀ (hY k), zpow_sum_eq_prod_zpow _ (hY k), ← zpow_mul, mul_comm (Aa k)]
      congr 1
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [← zpow_mul, mul_comm (x r k)]
    simp only [e1, Finset.prod_mul_distrib]
    rw [Finset.prod_comm]
    congr 1
    · rw [Finset.prod_zpow, h1, zpow_neg, zpow_natCast]
    · refine Finset.prod_congr rfl fun r _ => ?_
      rw [Finset.prod_zpow]
  have h3 : ∏ r, ((∏ k, Y k ^ x r k) • e r) ^ (-n r) =
      (∏ r, (∏ k, Y k ^ x r k) ^ (-n r)) * (∏ r, e r ^ n r)⁻¹ := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [smul_eq_mul, mul_zpow, zpow_neg (e r)]
  have h4 : ∏ r, (∏ k, Y k ^ x r k) ^ (-n r) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun r _ => zpow_ne_zero _
      (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hY k))
  have h5 : ∏ r, e r ^ n r ≠ 0 := Finset.prod_ne_zero_iff.2 fun r _ => zpow_ne_zero _ (he r)
  have h6 : Y k₀ ^ q ≠ 0 := pow_ne_zero _ (hY k₀)
  rw [h2, h3]
  field_simp

end Field

theorem mem_open_of_forms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (n₀ : Option (RootIx D) → ℤ) (N₀ : ℕ), (∀ r, n₀ (some r) = -Fx.n r) → n₀ none = -(Fx.q' : ℤ) → ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) ≠ 0 → ∀ (x : Or.Re.R.X) (dg dh : RM.K → ℕ) (G Hf : MRing RM.ι), IsMultiHomog G dg → IsMultiHomog Hf dh → (∀ k, (dg k : ℤ) = dh k + (combLine (RM.line 1) n₀).a k) → aeval RM.y G = ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) * aeval RM.y Hf → aeval (Or.Re.R.lift x x) G ≠ 0 → aeval (Or.Re.R.lift x x) Hf ≠ 0 → Or.Re.π x ∈ Sys.open' := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or n₀ N₀ hn hnone hε x dg dh G Hf hG hH hdeg hy hwG hwH
  classical
  have hmem : Or.Re.R.lift x x ∈ mcPts (mCoordIdeal RM.y) := Or.Re.R.mem x x (Or.Re.R.mem_U x)
  obtain ⟨z, hz, hc⟩ := (mem_mcPts_iff_exists_coordsAt _ _ Or.𝔐.ξ _ _ RM.y Or.𝔐.tie _).1 hmem
  refine (Or.interior x z hc).1 ?_
  by_contra hnab
  choose b hb using hc.1
  have hbw : ∀ k, Or.Re.R.lift x x ⟨k, b k⟩ ≠ 0 := fun k => (hb k).ne_zero
  let p : Cpt Or.𝔐.ξ := ⟨centre z, hz⟩
  have hyc : ∀ k, RM.y ⟨k, b k⟩ ≠ 0 := fun k => (hc.2 k (b k) (hb k)).1
  have hrat : ∀ k i, RM.y ⟨k, i⟩ / RM.y ⟨k, b k⟩ ∈ regAt Or.𝔐.ξ p := by
    intro k i
    obtain ⟨r, ⟨h', s, hs, -⟩, -⟩ := (hc.2 k (b k) (hb k)).2 i
    exact ⟨s, hs⟩
  have hch : InChart Or.𝔐.ξ (fun c' : (k : RM.K) → RM.ι k => ∏ k, RM.y ⟨k, c' k⟩) b p := by
    refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => hyc k, fun c' => ?_⟩
    show (∏ k, RM.y ⟨k, c' k⟩) / ∏ k, RM.y ⟨k, b k⟩ ∈ _
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => hrat k (c' k)
  have he0 : ∀ r, Or.e r ≠ 0 := fun r => (Or.lines r).1
  have hgen : ∀ r, (Or.Fl.rootLat r).IsGenAt p ((∏ k, RM.y ⟨k, b k⟩ ^ RM.xdeg r k) • Or.e r) := fun r =>
    ⟨smul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyc k)) (he0 r),
      (Or.lines r).2 _ trivial b hch⟩
  have ht := GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.tens_isGenAt (fun r => -Fx.n r) hgen
  have ya : Or.g (Fx.yf (Or.ix.symm (b Or.k₀))) = RM.y ⟨Or.k₀, b Or.k₀⟩ := by
    rw [← Or.y_eq, Equiv.apply_symm_apply]
  have hch' : InChart Or.𝔐.ξ (fun i' => Or.g (Fx.yf i')) (Or.ix.symm (b Or.k₀)) p := by
    refine ⟨?_, fun j => ?_⟩
    · show Or.g (Fx.yf (Or.ix.symm (b Or.k₀))) ≠ 0
      rw [ya]; exact hyc _
    · show Or.g (Fx.yf j) / Or.g (Fx.yf (Or.ix.symm (b Or.k₀))) ∈ _
      rw [ya, ← Or.y_eq]
      exact hrat _ _
  have hnat : ∀ m : ℕ, m ≠ 0 → unitAt Or.𝔐.ξ p (m : RM.Ω) := by
    intro m hm
    have e : (((m : RM.Ω), (m : ℂ)) : RM.Ω × ℂ) = ((m : RM.Ω × ℂ)) := Prod.ext (by simp) (by simp)
    have h2 : (((m : RM.Ω), (m : ℂ)) : RM.Ω × ℂ) ∈ valRing Or.𝔐.ξ z hz := by
      rw [e]
      exact natCast_mem _ m
    exact unitAt_of_mem_valRing hz h2 (Nat.cast_ne_zero.2 hm)
  have hp0 : ∀ r : ℕ, r.Prime → ¬ InFibre Or.𝔐.ξ r p := fun r hr hf => hf (hnat r hr.ne_zero)
  obtain ⟨-, hnu⟩ := Or.eff p hp0 _ _ hch' ht
  have hN₀ : N₀ ≠ 0 := by
    rintro rfl
    exact hε (by simp)
  have hA := unitAt_form hz hc b hbw hG hwG
  have hB := unitAt_form hz hc b hbw hH hwH
  have hAB : unitAt Or.𝔐.ξ p ((aeval RM.y G / ∏ k, RM.y ⟨k, b k⟩ ^ dg k) /
      (aeval RM.y Hf / ∏ k, RM.y ⟨k, b k⟩ ^ dh k)) :=
    ⟨div_ne_zero hA.1 hB.1, by rw [div_eq_mul_inv]; exact mul_mem hA.2.1 hB.2.2,
      by rw [inv_div, div_eq_mul_inv]; exact mul_mem hB.2.1 hA.2.2⟩
  have hid := mono_identity (fun k => RM.y ⟨k, b k⟩) hyc Or.e he0 RM.xdeg RM.A.a Fx.n Fx.q' Or.k₀ Or.A_deg
    (combLine (RM.line 1) n₀).a (fun k => by
      simp [combLine, Finset.sum_apply, Fintype.sum_option, RootModel.line, RM.x_deg, hn, hnone])
  have hHf0 : aeval RM.y Hf ≠ 0 := fun h0 => hB.1 (by rw [h0, zero_div])
  have hMh : ∏ k, RM.y ⟨k, b k⟩ ^ dh k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hyc k)
  have hPa : ∏ k, RM.y ⟨k, b k⟩ ^ (combLine (RM.line 1) n₀).a k ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyc k)
  have hMg : ∏ k, RM.y ⟨k, b k⟩ ^ dg k =
      (∏ k, RM.y ⟨k, b k⟩ ^ dh k) * ∏ k, RM.y ⟨k, b k⟩ ^ (combLine (RM.line 1) n₀).a k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, hdeg k, zpow_add₀ (hyc k), zpow_natCast]
  have hfin : (aeval RM.y G / ∏ k, RM.y ⟨k, b k⟩ ^ dg k) / (aeval RM.y Hf / ∏ k, RM.y ⟨k, b k⟩ ^ dh k) =
      (Or.g Fx.sE * Or.g (Fx.yf (Or.ix.symm (b Or.k₀))) ^ Fx.q' /
        ∏ r, ((∏ k, RM.y ⟨k, b k⟩ ^ RM.xdeg r k) • Or.e r) ^ (-Fx.n r)) * (N₀ : RM.Ω) := by
    have hid' : (∏ k, RM.y ⟨k, b k⟩ ^ (combLine (RM.line 1) n₀).a k)⁻¹ * ∏ r, Or.e r ^ Fx.n r =
        RM.y ⟨Or.k₀, b Or.k₀⟩ ^ Fx.q' / ∏ r, ((∏ k, RM.y ⟨k, b k⟩ ^ RM.xdeg r k) • Or.e r) ^ (-Fx.n r) := hid
    rw [hy, hMg, ya, mul_div_assoc (Or.g Fx.sE), ← hid']
    field_simp
  rw [hfin] at hAB
  exact hnu hnab (GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.unitAt_of_mul hAB (hnat N₀ hN₀))

end GlobalTheory.CompanionTheory.Ar.Small.FormsVal
