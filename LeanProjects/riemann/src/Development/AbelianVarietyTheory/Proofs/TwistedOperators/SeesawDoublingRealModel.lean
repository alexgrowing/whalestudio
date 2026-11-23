import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineOneParameterStatement

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilCompositionLinesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.PureProdRule

theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (θ : InfFam D) (X : HSp D) {a a' : ℕ} (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ l : List (D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ), (∀ q ∈ l, q.2 ∈ lieAt X q.1) →
    ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin a × Fin (a + a') → v.adicCompletion D.host.F) → ℂ,
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) →
    ∀ Ψ : Fin l.length → (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
    (∀ i, Ψ i ∈ algD Γ.M Bs.ψ Bs.emb ∧
        ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (Ψ i x) 0) →
    ∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) (∑ i, Ψ i x) 0 := by
  classical
  intro hP D θ X a a' e Bs Γ Xc om om' hJ hθ hTr l hl f hf φ hφ hvac Ψ hΨ x
  have hline : ∀ i : Fin l.length, ∃ γ ∈ Lines D.sp.cm.sig Γ.W, ∀ t : ℝ,
      γ (Multiplicative.ofAdd t) = kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t) := fun i =>
    GlobalTheory.KapXLine.exists_line D θ X (l.get i).1 (l.get i).2 hθ (hl _ (List.get_mem _ _)) e Γ.W hJ
  choose γ hγ hγt using hline
  have hT := fun i => GlobalTheory.T.weil_line_one_parameter hP Γ.M Bs.ψ Xc.β (Xc.β / Xc.α) om hTr.base.cm hTr.base.std hTr.weil (γ i) (hγ i)
  choose T hTa hTadd hT0 using hT
  have hstd : ∀ᶠ v in Filter.cofinite,
      φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers D.host.F} 1 := by
    filter_upwards [hvac, hTr.geo.hM.std] with v h1 h2
    rw [h1, h2]
  obtain ⟨r, hR, hpure⟩ : ∃ r : (Fin a × Fin (a + a') → AF D.host.F) → ℂ,
      (∀ g : SInf D.host.F (Fin a × Fin (a + a')), Rest (evI D.host.F) ⇑g r) ∧
      ∀ g : SInf D.host.F (Fin a × Fin (a + a')), pure g φ = tens (evI D.host.F) ⇑g r :=
    ⟨_, fun g => GlobalTheory.ThK.EvUniqInf.rest_pure g φ hφ hstd, fun g => rfl⟩

  have hlist : ∀ (t : ℝ) (L : List (Fin l.length)) (g : SInf D.host.F (Fin a × Fin (a + a'))),
      (L.map fun i => om (1, γ i (Multiplicative.ofAdd t))).prod (tens (evI D.host.F) ⇑g r) =
        tens (evI D.host.F) ⇑((L.map fun i => T i t).prod g) r := by
    intro t L
    induction L with
    | nil => intro g; rfl
    | cons i L ih =>
      intro g
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
      rw [ih g]
      exact hTa i t _ r (hR _)
  let κ : GA D X →* UA D.sp.cm.sig Γ.W.J :=
    { toFun := kapX X e hJ, map_one' := GlobalTheory.KapXLine.kapX_one X e hJ,
      map_mul' := GlobalTheory.KapXLine.kapX_mul X e hJ }
  let H : GA D X →* Module.End ℂ ((Fin a × Fin (a + a') → AF D.host.F) → ℂ) :=
    (om.comp (MonoidHom.inr _ _)).comp κ
  have hH : ∀ g, H g = om (1, kapX X e hJ g) := fun g => rfl
  have hprod : ∀ t : ℝ, om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (pure f φ) =
      tens (evI D.host.F) ⇑((List.ofFn fun i => T i t).prod f) r := by
    intro t
    rw [← hH, map_list_prod, List.map_map]
    have e1 : l.map (H ∘ fun q => oneP θ X q.1 q.2 t) =
        (List.finRange l.length).map fun i => om (1, γ i (Multiplicative.ofAdd t)) := by
      conv_lhs => rw [← List.ofFn_get l]
      rw [List.map_ofFn, List.ofFn_eq_map]
      refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp_apply, hH, hγt]
    rw [e1, hpure, hlist, ← List.ofFn_eq_map]
  have hone : ∀ (i : Fin l.length) (t : ℝ), om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (pure f φ) =
      tens (evI D.host.F) ⇑(T i t f) r := by
    intro i t
    rw [← hγt, hpure]
    exact hTa i t f r (hR f)
  have hd : ∀ i, HasDerivAt (fun t : ℝ => T i t f (fun j => evI D.host.F (x j)) * r x) (Ψ i x) 0 := by
    intro i
    have h := (hΨ i).2 x
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    show _ = om (1, kapX X e hJ (oneP θ X (l.get i).1 (l.get i).2 t)) (pure f φ) x
    rw [hone]
    rfl
  have hgoal : (fun t : ℝ => om (1, kapX X e hJ ((l.map fun q => oneP θ X q.1 q.2 t).prod)) (pure f φ) x) =
      fun t => (List.ofFn fun i => T i t).prod f (fun j => evI D.host.F (x j)) * r x := by
    funext t
    rw [hprod]
    rfl
  rw [hgoal]
  by_cases hr : r x = 0
  · have h0 : ∀ i, Ψ i x = 0 := fun i => by
      have := hd i
      simp only [hr, mul_zero] at this
      exact this.unique (hasDerivAt_const _ _)
    simp only [hr, mul_zero, h0, Finset.sum_const_zero]
    exact hasDerivAt_const _ _
  · have hc : ∀ i, HasDerivAt (fun t : ℝ => T i t f (fun j => evI D.host.F (x j))) (Ψ i x / r x) 0 := fun i => by
      have := (hd i).mul_const (r x)⁻¹
      refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
      · simp only [mul_assoc, mul_inv_cancel₀ hr, mul_one]
      · rw [div_eq_mul_inv]
    have hcore := GlobalTheory.T.weil_composition_lines hP Γ.M Bs.ψ Xc.β (Xc.β / Xc.α) om hTr.base.cm hTr.base.std hTr.weil l.length γ hγ T hTa
      hTadd hT0 f (fun j => evI D.host.F (x j)) (fun i => Ψ i x / r x) hc
    refine (hcore.mul_const (r x)).congr_deriv ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => div_mul_cancel₀ _ hr

end GlobalTheory.PureProdRule
