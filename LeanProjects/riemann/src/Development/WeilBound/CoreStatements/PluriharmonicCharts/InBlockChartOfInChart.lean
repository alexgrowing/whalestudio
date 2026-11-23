import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAtStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.c_bm_exists_local

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

def HoldsOff (Q₀ : Ideal (MRing J)) (G : Ideal (MRing J) → Prop) : Prop :=
  ∃ (d : K → ℕ) (h : MRing J), IsMultiHomog h d ∧ h ∉ Q₀ ∧ ∀ Q : Ideal (MRing J), h ∉ Q → G Q

variable {Q₀ : Ideal (MRing J)}

theorem HoldsOff.mono {G G' : Ideal (MRing J) → Prop} (h : HoldsOff Q₀ G) (hG : ∀ Q, G Q → G' Q) :
    HoldsOff Q₀ G' :=
  let ⟨d, f, h1, h2, h3⟩ := h
  ⟨d, f, h1, h2, fun Q hQ => hG Q (h3 Q hQ)⟩

theorem holdsOff_of_forall (hQ : Q₀.IsPrime) {G : Ideal (MRing J) → Prop} (h : ∀ Q, G Q) : HoldsOff Q₀ G :=
  ⟨0, 1, GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_one, (Ideal.ne_top_iff_one _).1 hQ.ne_top, fun Q _ => h Q⟩

theorem HoldsOff.and (hQ : Q₀.IsPrime) {G G' : Ideal (MRing J) → Prop} (h : HoldsOff Q₀ G) (h' : HoldsOff Q₀ G') :
    HoldsOff Q₀ fun Q => G Q ∧ G' Q := by
  obtain ⟨d, f, h1, h2, h3⟩ := h
  obtain ⟨d', f', h1', h2', h3'⟩ := h'
  exact ⟨d + d', f * f', GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_mul h1 h1', fun h => (hQ.mem_or_mem h).elim h2 h2',
    fun Q h => ⟨h3 Q fun a => h (Q.mul_mem_right _ a), h3' Q fun a => h (Q.mul_mem_left _ a)⟩⟩

theorem holdsOff_forall (hQ : Q₀.IsPrime) {α : Type} [Finite α] {G : α → Ideal (MRing J) → Prop}
    (h : ∀ a, HoldsOff Q₀ (G a)) : HoldsOff Q₀ fun Q => ∀ a, G a Q := by
  classical
  haveI := Fintype.ofFinite α
  have key : ∀ s : Finset α, HoldsOff Q₀ fun Q => ∀ a ∈ s, G a Q := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact holdsOff_of_forall hQ (by simp)
    | insert a s _ ih =>
      refine (HoldsOff.and hQ (h a) ih).mono fun Q hh b hb => ?_
      rcases Finset.mem_insert.1 hb with rfl | hb
      · exact hh.1
      · exact hh.2 b hb
  exact (key Finset.univ).mono fun Q hh a => hh a (Finset.mem_univ a)

theorem holdsOff_regAt {Ω : Type} [Field Ω] {x : (Σ k, J k) → Ω} {s : Ω} (h : RegAt x Q₀ s) :
    HoldsOff Q₀ fun Q => RegAt x Q s :=
  let ⟨d, g, t, hg, ht, h0, e⟩ := h
  ⟨d, t, ht, h0, fun _ hQ => ⟨d, g, t, hg, ht, hQ, e⟩⟩

theorem inBlockChart_of_inChart {Z : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ Z}
    {x : (Σ k, J k) → Ω} {c : ∀ k, J k} {q : Cpt ξ} (h : InChart ξ (segreCoord x) c q) : InBlockChart ξ x c q := by
  classical
  obtain ⟨h0, hc⟩ := h
  have h1 : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 h0 k (Finset.mem_univ k)
  refine fun k => ⟨h1 k, fun i => ?_⟩
  convert hc (Function.update c k i) using 1
  unfold segreCoord
  rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
  · simp
  · intro k' _ hk
    rw [Function.update_of_ne hk, div_self (h1 k')]
  · simp

theorem exists_frameDomain {Z : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ Z}
    {x : (Σ k, J k) → Ω} (tie : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, x ⟨k, c' k⟩)
    {z : Spec (CommRingCat.of ℂ) ⟶ Z} {w : (Σ k, J k) → ℂ} (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ x z w)
    {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) {G : Ideal (MRing J) → Prop} (hG : HoldsOff (mCoordIdeal w) G) :
    ∃ f : Ω, InFrameDomain x c f w ∧
      ∀ p : Cpt ξ, InChart ξ (segreCoord x) c p → unitAt ξ p f → InBlockChart ξ x c p ∧ G (ptIdeal ξ x p) := by
  obtain ⟨d, h, hd, h0, hG⟩ := hG
  refine ⟨MvPolynomial.aeval x h / ∏ k, x ⟨k, c k⟩ ^ d k, ⟨hc, _,
    (GlobalTheory.T.valAt_iff_value_at Z Ω ξ K J x tie z w hz hw _ _).1 (valAt_form hw hz hc hd), ?_⟩, fun p hp hu => ?_⟩
  · rw [form_mem_mCoordIdeal_iff w hd] at h0
    exact div_ne_zero h0 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))
  · have hb := inBlockChart_of_inChart hp
    refine ⟨hb, hG _ ?_⟩
    obtain ⟨R, _, z', w', e, hw', -⟩ := exists_ptIdeal_eq tie p
    have hz' : genPt ξ ⤳ centre z' := e ▸ p.2
    obtain rfl : p = ⟨centre z', hz'⟩ := Subtype.ext e.symm
    have hc' := (inBlockChart_centre_iff hw' hz' c).1 hb
    rw [ptIdeal_centre hw' hz', form_mem_mCoordIdeal_iff w' hd]
    rw [unitAt_iff_of_valAt (valAt_form hw' hz' hc' hd) hz'] at hu
    intro h1
    exact hu (by rw [h1, zero_div])

theorem exists_goodDomain {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
    {y : (Σ k, ι k) → Φ} {Ψ : Type} [Finite Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)
    (F : FrameData ι Ψ N M.Ω M.blk) {Z : Scheme.{0}} {ξ : Spec (CommRingCat.of M.Ω) ⟶ Z}
    (tie : CoordTie ℤ ξ fun c' : (k : NonPluckerBlocks M.blk) → baseIdx ι M.blk k => ∏ k, M.x ⟨k, c' k⟩)
    {z : Spec (CommRingCat.of ℂ) ⟶ Z} {w : (Σ k, baseIdx ι M.blk k) → ℂ} (hz : genPt ξ ⤳ centre z)
    (hw : CoordsAt ξ M.x z w) (hF : M.GoodAt F (mCoordIdeal w)) :
    ∃ f : M.Ω, InFrameDomain M.x F.c f w ∧
      ∀ p : Cpt ξ, InChart ξ (segreCoord M.x) F.c p → unitAt ξ p f → M.GoodAt F (ptIdeal ξ M.x p) := by
  have hP : (mCoordIdeal w).IsPrime := RingHom.ker_isPrime _
  have hc : ∀ k, w ⟨k, F.c k⟩ ≠ 0 := by
    refine (inBlockChart_centre_iff hw hz F.c).1 ((inBlockChart_iff_X_notMem tie _ F.c).2 ?_)
    rw [ptIdeal_centre hw hz]
    exact hF.1
  have h1 : HoldsOff (mCoordIdeal w) fun Q => ∀ q I, RegAt M.x Q (F.u q I) ∧ RegAt M.x Q (F.u' I q) :=
    holdsOff_forall hP fun q => holdsOff_forall hP fun I =>
      HoldsOff.and hP (holdsOff_regAt (hF.2.1 q I).1) (holdsOff_regAt (hF.2.1 q I).2)
  have h2 : HoldsOff (mCoordIdeal w) fun Q => ∀ p, M.blk p = none →
      F.υ p ≠ 0 ∧ RegAt M.x Q (F.υ p) ∧ RegAt M.x Q (F.υ p)⁻¹ := by
    refine holdsOff_forall hP fun p => ?_
    by_cases hp : M.blk p = none
    · obtain ⟨a, b, c⟩ := hF.2.2 p hp
      exact (HoldsOff.and hP (holdsOff_regAt b) (holdsOff_regAt c)).mono fun Q h _ => ⟨a, h⟩
    · exact holdsOff_of_forall hP fun Q h => absurd h hp
  obtain ⟨f, hf, hg⟩ := exists_frameDomain tie hz hw hc (HoldsOff.and hP h1 h2)
  exact ⟨f, hf, fun p a b => ⟨(inBlockChart_iff_X_notMem tie p F.c).1 (hg p a b).1, (hg p a b).2⟩⟩

end PositivityTheory.Xgp.c_bm_exists_local
