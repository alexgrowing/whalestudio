import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.CountAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeadingProductsIndependentModuloDeepProducts
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardExponentsAndChooseRatioBoundsPair
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinrankDomainSpanLeBinomialStatement

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares GlobalTheory.UpTie
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.UpTie.LeadCount

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in

theorem _root_.GlobalTheory.UpTie.LeadCount.bdd_mul_pow (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {la L : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} {P Q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hP : X.IsBddSec la P) (hQ : X.IsBddSec L Q) (k : ℕ) : X.IsBddSec (la + k • L) (P * Q ^ k) := by
  induction k with
  | zero => simpa using hP
  | succ k ih =>
    rw [succ_nsmul, ← add_assoc, pow_succ, ← mul_assoc]
    exact _root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_mul X ih hQ

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in

theorem _root_.GlobalTheory.UpTie.LeadCount.bdd_mul_prod {n : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {la L : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hP : X.IsBddSec la P) {s : Fin n → _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hs : ∀ k, X.IsBddSec L (s k)) (α : Fin n → ℕ)
    (t : Finset (Fin n)) : X.IsBddSec (la + (∑ k ∈ t, α k) • L) (P * (∏ k ∈ t, s k ^ α k)) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hP
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, add_comm (α a), add_smul, ← add_assoc,
      mul_comm (s a ^ α a), ← mul_assoc]
    exact _root_.GlobalTheory.UpTie.LeadCount.bdd_mul_pow X ih (hs a) (α a)

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), Margins X Xa → deepM X Xa Fl ≤ domSpan X (X.SS (Xa.Fp + Xa.T • Xa.L)) ∧ Fl.δ * (Xa.T - 1).choose (nd X) + Module.finrank ℂ (deepM X Xa Fl) ≤ Module.finrank ℂ (domSpan X (X.SS (Xa.Fp + Xa.T • Xa.L))) := by
  classical
  intro E _ _ _ r X Xa Fl hM
  obtain ⟨⟨bb, m, h1, h2, h3⟩, -, hL, -, hcusp⟩ := hM
  have hn := Xa.n_ge
  have hT : nd X < Xa.T := by have := Xa.T_ge; nlinarith
  have hsb : ∀ k, X.IsBddSec Xa.L (Fl.s k) := fun k => (Fl.s_van k).1.1
  have hdeep : deepM X Xa Fl ≤ domSpan X (X.SS (Xa.Fp + Xa.T • Xa.L)) := by
    refine Submodule.span_mono (Set.image_mono ?_)
    rintro P ⟨α, g, hα, hg, rfl⟩
    apply hcusp
    have h := bdd_mul_prod X hg.1 hsb α Finset.univ
    rw [hα, add_assoc, ← add_smul, Nat.add_sub_cancel' hT.le] at h
    convert h using 1
    funext x
    simp [monoM, Finset.prod_apply, mul_comm]
  refine ⟨hdeep, ?_⟩
  have hF : ∀ j : Fin Fl.δ, ∃ F ∈ X.SSgt Xa.Fp 0, ∀ j', F (Fl.xs j') = if j' = j then 1 else 0 := fun j =>
    interpStatement_holds r X Xa Fl (GlobalTheory.ClosedDiscontinuity.propDisc_closed _ _)
      ⟨bb, m, h1, h2, fun x0 hx0 z hz ξ => by simpa using h3 0 (by simp) x0 hx0 z hz ξ⟩ hL
      (fun P hP => by simpa using hcusp 0 P (by simpa using hP)) (fun j' => if j' = j then 1 else 0)
  choose F hFss hFval using hF
  have hind : ∀ {G : Wt X.Ψ r} (f : Frame X.Ψ r → ℂ), X.IsSec G f → ∀ x,
      DifferentiableOn ℂ (fun z => X.dom.indicator f (cpt X x z)) (OmF X x) := fun f hf x =>
    (OntoB.hol_comp X x hf.1).congr fun z hz => Set.indicator_of_mem (show cpt X x z ∈ X.dom from hz) f
  have hz0 : ∀ i a, Fl.s a (Fl.xs i) = 0 := by
    intro i
    refine (Fl.S_eq _ (Fl.xs_mem i)).2
      ⟨i, 1, X.Γ.one_mem, fun τ => (1 : Matrix (Fin r) (Fin r) ℂ), ?_, ?_⟩
    · intro τ
      refine ⟨?_, fun a c h => Matrix.one_apply_ne h.ne'⟩
      show (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
      simp
    · funext τ
      show mat (Fl.xs i) τ = ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
        (mat (Fl.xs i) τ * (1 : Matrix (Fin r) (Fin r) ℂ))
      simp
  have key := GlobalTheory.Shares.LeadDeep.indep_disjoint Xa.T (Xa.T - nd X) Fl.xs Fl.s Fl.w0
    (fun k => X.dom.indicator (F k)) ((fun f => X.dom.indicator f) '' X.SS (Xa.Fp + nd X • Xa.L))
    (fun q => ⟨nd X, rfl, cpt X (Fl.xs q), OmF X (Fl.xs q), OntoB.isOpen_OmF X _,
      by show cpt X (Fl.xs q) 0 ∈ X.dom
         rw [IW.cpt_zero]; exact Fl.xs_mem q,
      IW.cpt_zero X _, fun k => OntoB.hol_comp X _ (hsb k).1.1, OntoB.hol_comp X _ Fl.weightForm_vanishes.1.1.1.1,
      fun i => hind _ (hFss i).1.1.1 _,
      by rintro f ⟨g, hg, rfl⟩; exact hind _ hg.1.1 _, hz0 q, Fl.w0_ne q, Fl.coord q⟩)
    (by
      refine Fintype.linearIndependent_iff.mpr fun c hc j => ?_
      have := congrFun hc j
      simpa [vals, Finset.sum_apply, Set.indicator_of_mem (Fl.xs_mem j), hFval] using this)
  obtain ⟨hli, hdis⟩ := key
  have hD : Submodule.span ℂ {g | ∃ (α : Fin (nd X) → ℕ) (f : Frame X.Ψ r → ℂ), ∑ i, α i = Xa.T - nd X ∧
      f ∈ (fun f => X.dom.indicator f) '' X.SS (Xa.Fp + nd X • Xa.L) ∧ g = (∏ i, Fl.s i ^ α i) * f} =
      deepM X Xa Fl := by
    unfold deepM domSpan
    congr 1
    have e : ∀ (α : Fin (nd X) → ℕ) (g : Frame X.Ψ r → ℂ), (∏ i, Fl.s i ^ α i) * X.dom.indicator g =
        X.dom.indicator fun x => monoM X Fl.s α x * g x := by
      intro α g
      funext x
      by_cases hx : x ∈ X.dom <;> simp [hx, monoM, Finset.prod_apply]
    ext P
    constructor
    · rintro ⟨α, f, hα, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨_, ⟨α, g, hα, hg, rfl⟩, (e α g).symm⟩
    · rintro ⟨f, ⟨α, g, hα, hg, rfl⟩, rfl⟩
      exact ⟨α, _, hα, ⟨g, hg, rfl⟩, (e α g).symm⟩
  rw [hD] at hdis
  letI : Fintype {α : Fin (nd X) → ℕ // ∑ i, α i < Xa.T - nd X} :=
    Fintype.subtype (multiLt (nd X) (Xa.T - nd X)) fun _ => GlobalTheory.LeadIndep.mem_multiLt
  have hrk := finrank_span_eq_card hli
  have hcard := (GlobalTheory.card_exponents_and_choose_ratio_bounds (nd X) Xa.T).1 (by omega) hT
  rw [Fintype.card_prod, Fintype.card_fin, ← Nat.card_eq_fintype_card, hcard] at hrk
  set A := Submodule.span ℂ (Set.range fun p : {α : Fin (nd X) → ℕ // ∑ i, α i < Xa.T - nd X} × Fin Fl.δ =>
      (∏ i, Fl.s i ^ p.1.1 i) * Fl.w0 ^ (Xa.T - ∑ i, p.1.1 i) * X.dom.indicator (F p.2)) with hA
  have hAle : A ≤ domSpan X (X.SS (Xa.Fp + Xa.T • Xa.L)) := by
    refine Submodule.span_mono ?_
    rintro P ⟨⟨⟨α, hα⟩, k⟩, rfl⟩
    refine ⟨F k * (∏ i, Fl.s i ^ α i) * Fl.w0 ^ (Xa.T - ∑ i, α i), hcusp _ _ ?_, ?_⟩
    · have h := bdd_mul_pow X (bdd_mul_prod X (hFss k).1.1 hsb α Finset.univ) Fl.weightForm_vanishes.1.1 (Xa.T - ∑ i, α i)
      rwa [add_assoc, ← add_smul, Nat.add_sub_cancel' (by omega)] at h
    · funext x
      by_cases hx : x ∈ X.dom
      · simp only [Set.indicator_of_mem hx, Pi.mul_apply]
        ring
      · simp [hx]
  haveI := (GlobalTheory.T.finrank_domain_span_le_binomial E r X Xa Fl).1
  haveI : FiniteDimensional ℂ A := Submodule.finiteDimensional_of_le hAle
  haveI : FiniteDimensional ℂ (deepM X Xa Fl) := Submodule.finiteDimensional_of_le hdeep
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq A (deepM X Xa Fl)
  rw [hdis.eq_bot, finrank_bot, add_zero, hrk] at hsum
  have hle := Submodule.finrank_mono (sup_le hAle hdeep)
  rw [mul_comm, ← hsum]
  exact hle

end GlobalTheory.UpTie.LeadCount
