import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.LeviForms.UnifInt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralCongrPotentials
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodProjExistsStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LineIsomorphismDefectFunctionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionFamilyDefectFormulaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilySymmetricStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TelescopingCoordinateDifferenceStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDifferenceTendstoZeroStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ResolutionStatementHoldsStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.OneModel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
  GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open scoped ContDiff

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_pair_ne {P : Ideal (MRing ι)} {f g : MRing ι} (h : UnitRatio P f g) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) : ∃ u v : MRing ι, u * f - v * g ∈ P ∧ evC z u ≠ 0 ∧ evC z v ≠ 0 := by
  let ρ : MRing ι →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ))
  have hprime : (RingHom.ker ρ).IsPrime := RingHom.ker_isPrime ρ
  have hle : P ≤ RingHom.ker ρ := fun q hq => hz.2 q hq
  have hrel : IsRelevant (RingHom.ker ρ) := fun k => by
    obtain ⟨i, hi⟩ := hz.1 k
    refine ⟨i, fun hm => hi ?_⟩
    simpa [ρ] using (RingHom.mem_ker.1 hm)
  obtain ⟨u, v, hu, hv, huv⟩ := h.2.2 _ hprime hle hrel
  exact ⟨u, v, huv, fun h0 => hu (RingHom.mem_ker.2 h0), fun h0 => hv (RingHom.mem_ker.2 h0)⟩

theorem log_line_of_orbit {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) (a : σ) (t : ℝ)
    (h0 : 0 < t) (h1 : t ≤ S.t₀) (x : Re.R.X) (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (ho : SameOrbit (Re.R.lift x x) z) :
    Real.log ((Re.line a t).h z) = Real.log ((Re.ref a).h z) + S.phT a t (Re.π x) := by
  obtain ⟨c, hc, e⟩ := ho
  have h := Re.line_eq a t h0 h1 x
  rw [e, (Re.line a t).smul c z hc, (Re.ref a).smul c z hc, Re.line_deg] at h
  have hp : (∏ k, ‖c k‖ ^ (Re.ref a).a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [Real.log_mul hp ((Re.line a t).pos z hz).ne', Real.log_mul hp ((Re.ref a).pos z hz).ne'] at h
  linarith

theorem samePot_line {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) (c : σ) (t : ℝ)
    (h0 : 0 < t) (h1 : t ≤ S.t₀) :
    SamePot Re.R.A Set.univ (potOf Re.R (Re.line c t)) ((S.potT c t).pullback Re.π Re.holo.1) := by
  intro x _
  obtain ⟨V, hV, hxV, G, hG, hVG⟩ := Re.ref_pot c x (Set.mem_univ x)
  refine ⟨V ∩ Re.R.U x, hV.inter (Re.R.isOpen_U x), ⟨hxV, Re.R.mem_U x⟩, G, ?_, ?_⟩
  · intro j
    exact (hG j).mono fun y hy => ⟨hy.1, hy.2.1⟩
  · rintro y ⟨hyV, hyU⟩
    have hm := Re.R.mem x y hyU
    have ho : SameOrbit (Re.R.lift y y) (Re.R.lift x y) := Re.R.compat y x y ⟨Re.R.mem_U y, hyU⟩
    have e1 := log_line_of_orbit Re c t h0 h1 y _ hm.1 ho
    have e2 : Real.log ((Re.ref c).h (Re.R.lift x y)) - (S.th c).φ (Re.π x) (Re.π y) = (G y).re := hVG y hyV
    show Real.log ((Re.line c t).h (Re.R.lift x y)) -
      ((S.th c).φ (Re.π x) (Re.π y) + S.phT c t (Re.π y)) = (G y).re
    linarith

theorem isC2At_of_isPotential {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {Q : LocPot X}
    (h : IsPotential A Q) (x : X) : IsTwiceDifferentiableAt A Q x := by
  intro j hj
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (Q.isOpen_U x)
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Q.U x :=
    ⟨(A.chart j).map_source hj, by
      show (A.chart j).symm (A.chart j x) ∈ Q.U x
      rw [(A.chart j).left_inv hj]
      exact Q.mem_U x⟩
  exact ((h.1 x j).contDiffAt (hopen.mem_nhds hmem)).of_le (by
    have h2 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
    exact h2)

theorem continuous_of_smooth {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {f : X → ℝ}
    (h : A.Smooth f) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨j, hj⟩ := A.cover x
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ :=
    ⟨(A.chart j).map_source hj, Set.mem_univ _⟩
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ) := by
    simpa using (A.chart j).open_target
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) :=
    (h j).continuousOn.continuousAt (hopen.mem_nhds hmem)
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) x :=
    ContinuousAt.comp h1 ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem step_eq (hR : RatRStatement) (hB : ResBridgeStatement) (hG : GoodProjExistsStatement) (hA : AvoidStatement)
    (II : IntersectionSystem) (hI : IsIntersectionFamily (II K ι)) {P : Ideal (MRing ι)} {D : ℕ} {τ : Type}
    {S : AnSys D τ} (Re : Realis S P) (a₁ a₂ : τ) (f g : MRing ι) (d : S.X → ℝ)
    (hiso : IsLineIso P (Re.ref a₁).a (Re.ref a₂).a f g) (hd : S.A.Smooth d)
    (hlog : ∀ x, ∀ u v : MRing ι, u * f - v * g ∈ P → evC (Re.R.lift x x) u ≠ 0 →
      d (Re.π x) = Real.log (‖evC (Re.R.lift x x) v‖ / ‖evC (Re.R.lift x x) u‖ *
        (Re.ref a₂).h (Re.R.lift x x) / (Re.ref a₁).h (Re.R.lift x x)))
    (u : Fin D → τ) (t : ℝ) (h0 : 0 < t) (h1 : t ≤ S.t₀) :
    II K ι P (D + 1) (Fin.snoc (fun j => Re.line (u j) t) (Re.line a₁ t)) -
        II K ι P (D + 1) (Fin.snoc (fun j => Re.line (u j) t) (Re.line a₂ t)) =
      Re.deg * mInt S.A (fun j => S.potT (u j) t) (fun x => S.phT a₁ t x - S.phT a₂ t x - d x) := by
  have hl₁ := Re.line_smooth a₁ t h0 h1
  have hl₂ := Re.line_smooth a₂ t h0 h1
  have hIso : IsLineIso P (Re.line a₁ t).a (Re.line a₂ t).a f g := by
    rw [Re.line_deg, Re.line_deg]
    exact hiso
  obtain ⟨w, hw, -, -⟩ := GlobalTheory.T.line_isomorphism_defect_function K ι P Re.J D Re.R (Re.line a₁ t) (Re.line a₂ t) f g Re.arith.2.1 hIso hl₁ hl₂
  have h := GlobalTheory.T.intersection_family_defect_formula hR hB hG hA K ι (II K ι) hI P Re.J D Re.R (fun j => Re.line (u j) t) (Re.line a₁ t)
    (Re.line a₂ t) f g w Re.arith (fun j => Re.line_smooth _ t h0 h1) hl₁ hl₂ hIso hw
  rw [h]
  have hval : ∀ x, w (Re.R.lift x x) = -(S.phT a₁ t (Re.π x) - S.phT a₂ t (Re.π x) - d (Re.π x)) := by
    intro x
    have hz := Re.R.mem x x (Re.R.mem_U x)
    obtain ⟨p, q, hpq, hp, hq⟩ := exists_pair_ne hiso.2 hz
    have e0 := hw _ hz p q hpq hp
    have e1 := hlog x p q hpq hp
    have r₁ := Re.line_eq a₁ t h0 h1 x
    have r₂ := Re.line_eq a₂ t h0 h1 x
    have hc : 0 < ‖evC (Re.R.lift x x) q‖ / ‖evC (Re.R.lift x x) p‖ :=
      div_pos (norm_pos_iff.2 hq) (norm_pos_iff.2 hp)
    have l₁ := (Re.line a₁ t).pos _ hz.1
    have l₂ := (Re.line a₂ t).pos _ hz.1
    have f₁ := (Re.ref a₁).pos _ hz.1
    have f₂ := (Re.ref a₂).pos _ hz.1
    rw [Real.log_div (mul_pos hc l₂).ne' l₁.ne', Real.log_mul hc.ne' l₂.ne'] at e0
    rw [Real.log_div (mul_pos hc f₂).ne' f₁.ne', Real.log_mul hc.ne' f₂.ne'] at e1
    linarith
  have hpot : ∀ j, IsPotential S.A (S.potT (u j) t) := fun j =>
    isPotentialAdd S.A _ _ (S.sing (u j)).1 (isPotential_ofFun S.A _ ((S.reg (u j)).2.2 t h0 h1).1)
  have hcont : Continuous fun x => -(S.phT a₁ t x - S.phT a₂ t x - d x) :=
    (((continuous_of_smooth S.A ((S.reg a₁).2.2 t h0 h1).1).sub
      (continuous_of_smooth S.A ((S.reg a₂).2.2 t h0 h1).1)).sub (continuous_of_smooth S.A hd)).neg
  have hcongr := (GlobalTheory.CompanionTheory.Ar.PB.mInt_congr_samePot D Re.R.X Re.R.A Set.univ
    (fun j => potOf Re.R (Re.line (u j) t)) (fun j => (S.potT (u j) t).pullback Re.π Re.holo.1)
    (fun x => w (Re.R.lift x x))
    ((fun x => -(S.phT a₁ t x - S.phT a₂ t x - d x)) ∘ Re.π)
    (by simp [IsNull]) (fun j => samePot_line Re (u j) t h0 h1)
    (fun j x _ => isC2At_of_isPotential Re.R.A (isPotentialPullback S.A Re.R.A Re.π Re.holo _ (hpot j)) x)
    (fun x _ => hval x)).1
  rw [hcongr, degreeFormula S.A Re.R.A Re.π Re.holo Re.deg Re.br Re.degree (fun j => S.potT (u j) t) hpot _ hcont,
    mInt_neg_integrand]
  ring

theorem cmp_one : Inputs → AvoidStatement → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (σ : Type) (S : AnSys D (σ ⊕ σ)) (Re : Realis S P) (f g : σ → MRing ι) (d : σ → S.X → ℝ), (∀ a, IsLineIso P (Re.ref (Sum.inl a)).a (Re.ref (Sum.inr a)).a (f a) (g a)) → (∀ a, S.A.Smooth (d a)) → (∀ a, ∀ y ∈ S.open', S.ph (Sum.inl a) y = S.ph (Sum.inr a) y + d a y) → (∀ a x, ∀ u v : MRing ι, u * f a - v * g a ∈ P → evC (Re.R.lift x x) u ≠ 0 → d a (Re.π x) = Real.log (‖evC (Re.R.lift x x) v‖ / ‖evC (Re.R.lift x x) u‖ * (Re.ref (Sum.inr a)).h (Re.R.lift x x) / (Re.ref (Sum.inl a)).h (Re.R.lift x x))) → ∀ w : Fin (D + 1) → σ, Tendsto (fun t => Re.num II t (fun j => Sum.inl (w j)) - Re.num II t (fun j => Sum.inr (w j))) (𝓝[>] 0) (𝓝 0) := by
  intro hIn hA II hII K _ ι _ P D σ S Re f g d hiso hd hph hlog w
  have hI : IsIntersectionFamily (II K ι) := hII.1 K ι
  have ht : 0 < S.t₀ := (S.reg (Sum.inl (w 0))).1
  have hdeg : (Re.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Re.deg_pos.ne'
  have hstep : ∀ i : Fin (D + 1), Tendsto (fun t =>
      Re.num II t (fun j => if j < i then Sum.inr (w j) else Sum.inl (w j)) -
        Re.num II t (fun j => if j ≤ i then Sum.inr (w j) else Sum.inl (w j))) (𝓝[>] 0) (𝓝 0) := by
    intro i
    let c : Fin (D + 1) → σ ⊕ σ := fun j => if j < i then Sum.inr (w j) else Sum.inl (w j)
    let c' : Fin (D + 1) → σ ⊕ σ := fun j => if j ≤ i then Sum.inr (w j) else Sum.inl (w j)
    let u : Fin D → σ ⊕ σ := fun j => c (i.succAbove j)
    have hT := GlobalTheory.T.monge_ampere_difference_tendsto_zero hIn.convergenceSigned D σ S d hd hph (w i) u
    refine hT.congr' ?_
    filter_upwards [Ioc_mem_nhdsGT ht] with t ht'
    have h0 := ht'.1
    have h1 := ht'.2
    have hci : c i = Sum.inl (w i) := by simp [c]
    have hci' : c' i = Sum.inr (w i) := by simp [c']
    have hcc : ∀ j : Fin D, c' (i.succAbove j) = u j := by
      intro j
      have hne : i.succAbove j ≠ i := Fin.succAbove_ne i j
      have hiff : i.succAbove j ≤ i ↔ i.succAbove j < i := ⟨fun h => lt_of_le_of_ne h hne, le_of_lt⟩
      simp only [c', u, c, hiff]
    have s₁ := GlobalTheory.T.intersection_family_symmetric K ι (II K ι) hI P D (fun j => Re.line (c j) t) i Re.arith
      (fun j => Re.line_smooth _ t h0 h1)
    have s₂ := GlobalTheory.T.intersection_family_symmetric K ι (II K ι) hI P D (fun j => Re.line (c' j) t) i Re.arith
      (fun j => Re.line_smooth _ t h0 h1)
    simp only [hci, hci', hcc] at s₁ s₂
    have hs := step_eq hIn.ratR (GlobalTheory.T.resolution_statement_holds) GlobalTheory.CompanionTheory.Ar.Link.goodProjExistsStatement_holds hA II hI Re
      (Sum.inl (w i)) (Sum.inr (w i)) (f (w i)) (g (w i)) (d (w i)) (hiso (w i)) (hd (w i)) (hlog (w i)) u t h0 h1
    show mInt S.A _ _ = Re.num II t c - Re.num II t c'
    simp only [Realis.num]
    rw [s₁, s₂, ← sub_div, hs, mul_div_cancel_left₀ _ hdeg]
  have hsum := tendsto_finset_sum Finset.univ fun i (_ : i ∈ Finset.univ) => hstep i
  simp only [Finset.sum_const_zero] at hsum
  refine hsum.congr fun t => ?_
  exact (GlobalTheory.T.telescoping_coordinate_difference (σ ⊕ σ) (D + 1) (Re.num II t) _ _).symm

end GlobalTheory.CompanionTheory.Ar.Cmp.OneModel
