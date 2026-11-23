import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodLabelsRankPartParameterCuspidalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TieAutAndSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularDefinite
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.UbcString

theorem not_isSplitPl_of_inert {R : Ranks} (H : Host R) (w : HeightOneSpectrum (𝓞 H.E))
    (hw : Formalism.UG.IsInertAt H.F H.E (w.under (𝓞 H.F)) w) : ¬ IsSplitPl H w := by
  rintro ⟨x, hx, hy⟩
  let c : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv (H.conj : H.E ≃+* H.E)
  have hc : ∀ z : 𝓞 H.E, ((c z : 𝓞 H.E) : H.E) = H.conj (z : H.E) := fun z => rfl
  have hfix : ∀ a : 𝓞 H.F, c (algebraMap (𝓞 H.F) (𝓞 H.E) a) = algebraMap (𝓞 H.F) (𝓞 H.E) a := by
    intro a
    apply RingOfIntegers.ext
    rw [hc]
    have e : ((algebraMap (𝓞 H.F) (𝓞 H.E) a : 𝓞 H.E) : H.E) = ((a : H.F) : H.E) := rfl
    rw [e]
    exact (H.conjE_mem_hostF_iff _).1 (a : H.F).2
  have hle : w.asIdeal ≤ w.asIdeal.comap (c : 𝓞 H.E →+* 𝓞 H.E) := by
    unfold Formalism.UG.IsInertAt at hw
    rw [← hw, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change c (algebraMap (𝓞 H.F) (𝓞 H.E) a) ∈ _
    rw [hfix]
    exact Ideal.mem_map_of_mem _ ha
  exact hy (c x) (hc x) (hle hx)

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N)

theorem unr_of_foldr {w : PlE H} (a : A.LP w) (f : ℝ → ℝ) (L : List ℝ) (k : ℝ) (hk : k ∈ L)
    (h : A.unr (L.foldr (fun k acc => A.lpSum (A.lpTw a (f k)) acc) (A.lpZero w))) : A.unr a := by
  induction L with
  | nil => simp at hk
  | cons j L ih =>
    rw [List.foldr_cons, A.unr_sum] at h
    rcases List.mem_cons.1 hk with rfl | hk
    · exact (A.unr_tw a _).1 h.1
    · exact ih hk h.2

theorem frobEig_foldr {w : PlE H} (a : A.LP w) (ha : A.unr a) (f : ℝ → ℝ) (L : List ℝ) :
    A.unr (L.foldr (fun k acc => A.lpSum (A.lpTw a (f k)) acc) (A.lpZero w)) ∧
    A.frobEig (L.foldr (fun k acc => A.lpSum (A.lpTw a (f k)) acc) (A.lpZero w)) =
      (L.map fun k => (A.frobEig a).map (· * ((normV w : ℕ) : ℂ) ^ ((f k : ℝ) : ℂ))).sum := by
  induction L with
  | nil => exact ⟨A.lpZero_unr w, A.frobEig_zero w⟩
  | cons k L ih =>
    have hk := (A.unr_tw a (f k)).2 ha
    refine ⟨(A.unr_sum _ _).2 ⟨hk, ih.1⟩, ?_⟩
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    rw [A.frobEig_sum _ _ hk ih.1, A.frobEig_tw a _ ha, ih.2]

theorem sum_singletons {ι : Type} (g : ι → ℂ) (L : List ι) :
    (L.map fun k => ({g k} : Multiset ℂ)).sum = ((L.map g : List ℂ) : Multiset ℂ) := by
  induction L with
  | nil => simp
  | cons k L ih => simp [ih]

end GlobalTheory.UbcString

theorem GlobalTheory.UbcString.ubc_string : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc), ∀ x ∈ ZgoodN D.nd D.naut i, ∃ P', D.naut.ptV i P' = some x ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w → ∃ (B'' : Multiset ℂ) (c : ℂ), D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) = {c} ∧ ubc D.R.nV (D.naut.satV i P' w) = B'' + GlobalTheory.DownLift.str (Ideal.absNorm w.asIdeal) c D.R.t ∧ ∀ a ∈ B'', ‖a‖ = 1 := by
  intro hAF hL D P X _ _ h7 htie i x hx
  obtain ⟨-, Sig, ⟨P', hP', hB⟩, hgood⟩ := hx
  obtain ⟨π, rfl⟩ := GlobalTheory.T.goodLabels_rank_part_parameter_cuspidal D htie i x Sig ⟨P', hP', hB⟩ hgood
  refine ⟨P', hP', fun w hw => ?_⟩
  have hns := GlobalTheory.UbcString.not_isSplitPl_of_inert D.host w hw
  obtain ⟨hunr, hfe⟩ := hB.2.2.2.2.1 w hns
  have e1 : spehLoc D.nd D.naut ⟨D.R.r, D.naut.tw π D.naut.etaTinv, 1⟩ w =
      D.naut.locG (D.naut.tw π D.naut.etaTinv) w := by
    simp [spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]
  have e : isoLoc D.nd D.naut (twistIso D.nd D.naut ([⟨D.R.r, π, 1⟩] ++ [muPart D.nd D.naut i]) D.naut.etaTinv) w =
      D.naut.lpSum (D.naut.locG (D.naut.tw π D.naut.etaTinv) w)
        (spehLoc D.nd D.naut ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ w) := by
    simp only [isoLoc, twistIso, muPart, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, D.naut.lpSum_zero, e1]
  rw [e] at hunr hfe
  obtain ⟨ha, hb⟩ := (D.naut.unr_sum _ _).1 hunr
  have hb' : D.naut.unr ((List.range D.R.t).map (fun a : ℕ => (a : ℝ)) |>.foldr
      (fun k acc => D.naut.lpSum (D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w)
        (((D.R.t : ℝ) - 1) / 2 - k)) acc) (D.naut.lpZero w)) := by
    rw [← GlobalTheory.LocalInv.list_coe]; exact hb
  have hm : D.naut.unr (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) :=
    GlobalTheory.UbcString.unr_of_foldr D.naut _ (fun k : ℝ => ((D.R.t : ℝ) - 1) / 2 - k) _ 0
      (List.mem_map.2 ⟨0, List.mem_range.2 D.R.t_odd.pos, by simp⟩) hb'
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.1
    (by rw [D.naut.frobEig_card _ hm, D.naut.locG_dim] :
      Multiset.card (D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w)) = 1)
  have hstr : D.naut.frobEig (spehLoc D.nd D.naut ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ w) =
      GlobalTheory.DownLift.str (Ideal.absNorm w.asIdeal) c D.R.t := by
    have h := (GlobalTheory.UbcString.frobEig_foldr D.naut _ hm (fun k : ℝ => ((D.R.t : ℝ) - 1) / 2 - k)
      ((List.range D.R.t).map (fun a : ℕ => (a : ℝ)))).2
    unfold spehLoc
    rw [GlobalTheory.LocalInv.list_coe]
    refine h.trans ?_
    rw [hc]
    simp only [Multiset.map_singleton]
    rw [List.map_map, Function.comp_def, GlobalTheory.UbcString.sum_singletons (fun a : ℕ => c * ((normV w : ℕ) : ℂ) ^ ((((D.R.t : ℝ) - 1) / 2 - (a : ℝ) : ℝ) : ℂ)), GlobalTheory.DownLift.str, Multiset.range, Multiset.map_coe]
    congr 1
    refine List.map_congr_left fun k _ => ?_
    have hq : ((normV w : ℕ) : ℂ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) := rfl
    rw [hq]
    push_cast
    ring_nf
  rw [D.naut.frobEig_sum _ _ ha hb, hstr] at hfe
  refine ⟨D.naut.frobEig (D.naut.locG (D.naut.tw π D.naut.etaTinv) w), c, hc, hfe.symm, ?_⟩

  have hAut := (GlobalTheory.AutomorphismSplitting.tieAut_and_split hAF hL D P).1
  have hη : GlobalTheory.LocalInv.EtaType D.nd D.naut := by
    obtain ⟨⟨h1, -⟩, h2, -⟩ := hAut
    refine ⟨h1, fun τ z hz => ?_⟩
    rcases (h2 τ).1 with e | e <;> rw [e, Multiset.mem_singleton] at hz <;> subst hz
    · exact ⟨0, by simp⟩
    · exact ⟨-1, by push_cast; ring⟩
  have hpa := GlobalTheory.LocalInv.part_alg D.nd D.naut hη (GlobalTheory.LocalInv.weightRegular_definite D) i P' _ hB
    ⟨D.R.r, D.naut.tw π D.naut.etaTinv, 1⟩ (by simp [twistIso]) (GlobalTheory.LocalInv.r_odd D.R) odd_one
  have ht := h7 D.R.r _ (GlobalTheory.LocalInv.r_odd D.R).pos hpa.1 hpa.2 w
  rw [D.naut.locG_tw] at ht
  have he := D.naut.etaT_unr w
  have hd := D.naut.locG_dim D.naut.etaT w
  have hu := D.naut.unr_char _ _ hd ha he
  rw [D.naut.tempered_unr _ hu, D.naut.frobEig_char _ _ (-1) ha he hd (D.naut.etaT_inert w hns)] at ht
  intro α hα
  have := ht (α * -1) (Multiset.mem_map_of_mem _ hα)
  simpa using this
