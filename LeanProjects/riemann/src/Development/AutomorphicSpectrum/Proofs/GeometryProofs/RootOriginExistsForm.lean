import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginDegreeCount
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemOfAevalEqZero
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.OffForm

open AlgebraicGeometry CategoryTheory MvPolynomial GlobalTheory.CompanionTheory.Ar.Small.RepAt GlobalTheory.CompanionTheory.Ar.AlgPoly

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {z : Spec (CommRingCat.of ℂ) ⟶ X} {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  {y : (Σ k, J k) → Ω} {w : (Σ k, J k) → ℂ}

theorem valAt_ratio (hw : CoordsAt ξ y z w) (c : ∀ k, J k) (hc : ∀ k, IsUnit (w ⟨k, c k⟩)) (p : Σ k, J k) :
    ValAt ξ z (y p / y ⟨p.1, c p.1⟩) (w p / w ⟨p.1, c p.1⟩) := by
  obtain ⟨k, i⟩ := p
  obtain ⟨r, hr, e⟩ := (hw.2 k (c k) (hc k)).2 i
  show ValAt ξ z _ (w ⟨k, i⟩ / w ⟨k, c k⟩)
  rw [e, mul_div_cancel_right₀ _ (hc k).ne_zero]
  exact hr

theorem valAt_aeval (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) (c : ∀ k, J k)
    (hc : ∀ k, IsUnit (w ⟨k, c k⟩)) (g : MRing J) :
    ValAt ξ z (aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) g)
      (aeval (fun p : Σ k, J k => w p / w ⟨p.1, c p.1⟩) g) := by
  induction g using MvPolynomial.induction_on with
  | C n => simpa using valAt_intCast hz n
  | add a b ha hb =>
    rw [map_add, map_add]
    exact valAt_add ha hb
  | mul_X a p ha =>
    rw [map_mul, map_mul, aeval_X, aeval_X]
    exact valAt_mul ha (valAt_ratio hw c hc p)

theorem aeval_form_ratio {L : Type} [Field L] (v : (Σ k, J k) → L) (c : ∀ k, J k) (hv : ∀ k, v ⟨k, c k⟩ ≠ 0)
    {G : MRing J} {d : K → ℕ} (hG : IsMultiHomog G d) :
    aeval v G = aeval (fun p : Σ k, J k => v p / v ⟨p.1, c p.1⟩) G * ∏ k, v ⟨k, c k⟩ ^ d k := by
  have h := GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.aeval_scaled_homog (fun p : Σ k, J k => v p / v ⟨p.1, c p.1⟩)
    (fun k => v ⟨k, c k⟩) hG
  rw [← h]
  congr 2
  funext p
  exact (div_mul_cancel₀ _ (hv p.1)).symm

theorem unitAt_of_valAt (hz : genPt ξ ⤳ centre z) {a : Ω} {r : ℂ} (ha : ValAt ξ z a r) (hr : r ≠ 0) :
    unitAt ξ ⟨centre z, hz⟩ a := by
  obtain ⟨h, s, hs, hsr⟩ := valAt_iff.1 ha
  have hu : IsUnit s := GlobalTheory.CompanionTheory.Ar.CxVal.isUnit _ (by rw [show (Scheme.stalkClosedPointTo z).hom s = r from hsr]; exact hr)
  obtain ⟨t, ht⟩ := hu.exists_right_inv
  have e : a * genMap ξ ⟨centre z, hz⟩ t = 1 := by
    have := congrArg (genMap ξ ⟨centre z, hz⟩) ht
    rwa [map_mul, map_one, hs] at this
  refine ⟨left_ne_zero_of_mul_eq_one e, ⟨s, hs⟩, ⟨t, ?_⟩⟩
  exact eq_inv_of_mul_eq_one_right e

theorem unitAt_div {p : Cpt ξ} {a b : Ω} (ha : unitAt ξ p a) (hb : unitAt ξ p b) : unitAt ξ p (a / b) := by
  refine ⟨div_ne_zero ha.1 hb.1, ?_, ?_⟩
  · rw [div_eq_mul_inv]
    exact mul_mem ha.2.1 hb.2.2
  · rw [inv_div, div_eq_mul_inv]
    exact mul_mem hb.2.1 ha.2.2

theorem unitAt_of_forms (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w) (c : ∀ k, J k)
    (hc : ∀ k, IsUnit (w ⟨k, c k⟩)) {d : K → ℕ} {G Hf : MRing J} (hG : IsMultiHomog G d) (hH : IsMultiHomog Hf d)
    {ε : Ω} (hHy : aeval y Hf ≠ 0) (hGy : aeval y G = ε * aeval y Hf) (hGw : aeval w G ≠ 0) (hHw : aeval w Hf ≠ 0) :
    unitAt ξ ⟨centre z, hz⟩ ε := by
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (hc k)).1
  have hw0 : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have uG := unitAt_of_valAt hz (valAt_aeval hz hw c hc G) (by
    intro h0
    apply hGw
    rw [aeval_form_ratio w c hw0 hG, h0, zero_mul])
  have uH := unitAt_of_valAt hz (valAt_aeval hz hw c hc Hf) (by
    intro h0
    apply hHw
    rw [aeval_form_ratio w c hw0 hH, h0, zero_mul])
  have hM : ∏ k, y ⟨k, c k⟩ ^ d k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)
  have e : ε = aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) G /
      aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) Hf := by
    rw [aeval_form_ratio y c hy hG, aeval_form_ratio y c hy hH, ← mul_assoc] at hGy
    have h1 := mul_right_cancel₀ hM hGy
    rw [h1, mul_div_cancel_right₀ _ uH.1]
  rw [e]
  exact unitAt_div uG uH

end GlobalTheory.CompanionTheory.Ar.Small.OffForm

open GlobalTheory.CompanionTheory.Ar.Small.OffForm in

theorem GlobalTheory.CompanionTheory.RootForm.exists_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (GlobalTheory.CompanionTheory.Ar.CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (GlobalTheory.CompanionTheory.Ar.CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx), ∃ f : MRing RM.ι, Small.IsFormOff (mCoordIdeal RM.y) f ∧ ∀ w ∈ mcPts (mCoordIdeal RM.y), MvPolynomial.aeval w f ≠ 0 → ∀ x : Or.Re.R.X, SameOrbit (Or.Re.R.lift x x) w → Or.Re.π x ∈ Sys.open' := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or
  obtain ⟨cc, hch⟩ := Or.𝔐.tie.cover ⟨genPt Or.𝔐.ξ, specializes_rfl⟩
  have hy : ∀ k, RM.y ⟨k, cc k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hch.1 k (Finset.mem_univ k)
  have ya : Or.g (Fx.yf (Or.ix.symm (cc Or.k₀))) = RM.y ⟨Or.k₀, cc Or.k₀⟩ := by
    rw [← Or.y_eq, Equiv.apply_symm_apply]
  have ht0 : (∏ r, ((∏ k, RM.y ⟨k, cc k⟩ ^ RM.xdeg r k) • Or.e r) ^ (-Fx.n r)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun r _ => zpow_ne_zero _
      (smul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) (Or.lines r).1)
  have hε : Or.g Fx.sE * Or.g (Fx.yf (Or.ix.symm (cc Or.k₀))) ^ Fx.q' /
      (∏ r, ((∏ k, RM.y ⟨k, cc k⟩ ^ RM.xdeg r k) • Or.e r) ^ (-Fx.n r)) ≠ 0 := by
    refine div_ne_zero (mul_ne_zero ((map_ne_zero Or.g).2 Fx.sE_ne) (pow_ne_zero _ ?_)) ht0
    rw [ya]
    exact hy _
  obtain ⟨d, G, Hf, hG, hH, hHy, hGy⟩ := RM.birational (Or.g Fx.sE * Or.g (Fx.yf (Or.ix.symm (cc Or.k₀))) ^ Fx.q' /
      (∏ r, ((∏ k, RM.y ⟨k, cc k⟩ ^ RM.xdeg r k) • Or.e r) ^ (-Fx.n r)))
  have hGy0 : MvPolynomial.aeval RM.y G ≠ 0 := by
    rw [hGy]
    exact mul_ne_zero hε hHy
  have hform := GlobalTheory.CompanionTheory.Ar.AlgPoly.form_mul (GlobalTheory.CompanionTheory.Ar.AlgPoly.form_mul hG hH)
    (GlobalTheory.CompanionTheory.Ar.Small.RepAt.form_mono cc fun _ => 1)
  refine ⟨G * Hf * GlobalTheory.CompanionTheory.Ar.Small.RepAt.mono cc (fun _ => 1), ⟨⟨_, hform⟩, fun hm => ?_⟩, fun w hw hf x hso => ?_⟩
  · have h := GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.aeval_scaled RM.y (fun _ => 1) (G * Hf * GlobalTheory.CompanionTheory.Ar.Small.RepAt.mono cc (fun _ => 1))
    have h0 : mConeMap RM.y (G * Hf * GlobalTheory.CompanionTheory.Ar.Small.RepAt.mono cc (fun _ => 1)) = 0 := hm
    rw [h0, map_zero] at h
    simp only [mul_one] at h
    rw [map_mul, map_mul, GlobalTheory.CompanionTheory.Ar.Small.RepAt.aeval_mono] at h
    exact mul_ne_zero (mul_ne_zero hGy0 hHy) (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)) h
  obtain ⟨cs, hcs, he⟩ := hso
  have hw' : Or.Re.R.lift x x ∈ mcPts (mCoordIdeal RM.y) := Or.Re.R.mem x x (Or.Re.R.mem_U x)
  have hf' : MvPolynomial.aeval (Or.Re.R.lift x x) (G * Hf * GlobalTheory.CompanionTheory.Ar.Small.RepAt.mono cc (fun _ => 1)) ≠ 0 := by
    have h := GlobalTheory.CompanionTheory.Ar.Flat.UnitChart.aeval_scaled_homog w cs hform
    have e2 : Or.Re.R.lift x x = fun p => w p * cs p.1 := by
      rw [he]
      funext p
      exact mul_comm _ _
    rw [e2, h]
    exact mul_ne_zero hf (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hcs k))
  rw [map_mul, map_mul, GlobalTheory.CompanionTheory.Ar.Small.RepAt.aeval_mono] at hf'
  have hGw := left_ne_zero_of_mul (left_ne_zero_of_mul hf')
  have hHw := right_ne_zero_of_mul (left_ne_zero_of_mul hf')
  have hcc : ∀ k, IsUnit (Or.Re.R.lift x x ⟨k, cc k⟩) := fun k => IsUnit.mk0 _ (by
    have := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hf') k (Finset.mem_univ k)
    simpa using this)
  obtain ⟨z, hz, hco⟩ := (mem_mcPts_iff_exists_coordsAt Or.𝔐.X RM.Ω Or.𝔐.ξ RM.K RM.ι RM.y Or.𝔐.tie _).1 hw'
  have hch' := GlobalTheory.CompanionTheory.Ar.Small.RepAt.inChart_of_coords hz hco cc hcc
  have gens : ∀ r, (Or.Fl.rootLat r).IsGenAt ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ ((∏ k, RM.y ⟨k, cc k⟩ ^ RM.xdeg r k) • Or.e r) :=
    fun r => ⟨smul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) (Or.lines r).1,
      (Or.lines r).2 _ trivial cc hch'⟩
  have ht := GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.tens_isGenAt (fun r => -Fx.n r) gens
  have hchi : InChart Or.𝔐.ξ (fun i' => Or.g (Fx.yf i')) (Or.ix.symm (cc Or.k₀)) ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ := by
    refine ⟨?_, fun j => ?_⟩
    · show Or.g (Fx.yf (Or.ix.symm (cc Or.k₀))) ≠ 0
      rw [ya]
      exact hy _
    · show Or.g (Fx.yf j) / Or.g (Fx.yf (Or.ix.symm (cc Or.k₀))) ∈ _
      rw [ya, ← Or.y_eq]
      exact Lat.block_ratio_mem hch' Or.k₀ (Or.ix j)
  have heff := (Or.eff ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ (fun r hr => GlobalTheory.CompanionTheory.Ar.Small.RepAt.not_inFibre hz hr) _ _ hchi ht).2
  have hu := unitAt_of_forms hz hco cc hcc hG hH hHy hGy hGw hHw
  exact (Or.interior x z hco).1 (not_not.1 fun h => heff h hu)
