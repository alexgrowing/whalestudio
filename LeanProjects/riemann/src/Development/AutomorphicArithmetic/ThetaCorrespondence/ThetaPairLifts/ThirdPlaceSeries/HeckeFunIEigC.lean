import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilityNinth
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigenAtInert
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRtEqOfGoodInertStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.InertEigSat
set_option maxHeartbeats 4000000 in
theorem heckeFunI_eigC_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D)
    (i : D.nd.Loc) (x : D.nd.X i) {w : HeightOneSpectrum (𝓞 D.host.E)} (hns : ¬ Formalism.BasicNotions.IsSplitPl D.host w)
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))} (hov : NG.OverPl w v)
    (Dv : InertDatum D.host.E D.R.nV v w)
    (hfix : ∀ g : D.what₂.Mt (D.nd.mu i) (D.nd.j i), ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {v} κ →
      NG.rt D.host.E D.R.nV κ ((P.M.loc i).real g) = (P.M.loc i).real g)
    (P₀ : D.naut.AV i) (hP₀ : D.naut.ptV i P₀ = some x) (α₀ : Fin (D.R.nV / 2) → ℂ)
    (hα₀ : D.naut.satV i P₀ w = Multiset.map α₀ Finset.univ.val)
    (h0 : Formalism.UG.GU Dv.σw D.R.nV → ℂ) (hh0 : h0 ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw D.R.nV)) :
    ∀ g ∈ eigC D.nd D.naut i x, heckeFunI D.host.E D.R.nV (Umax D.host.E D.R.nV) Dv h0 ((P.M.loc i).real g) =
      Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield D.host.E) v) h0 α₀ • (P.M.loc i).real g := by
  classical
  obtain ⟨C, a, xs, hC⟩ := GlobalTheory.EigInert.heckeFunI_umax_sum Dv h0 hh0
  set c := Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield D.host.E) v) h0 α₀ with hc
  intro g hg
  unfold eigC at hg
  refine Submodule.iSup_induction _ (motive := fun g => heckeFunI D.host.E D.R.nV (Umax D.host.E D.R.nV) Dv h0
    ((P.M.loc i).real g) = c • (P.M.loc i).real g) hg ?_ ?_ ?_
  · intro P' g' hg'
    by_cases hP' : D.naut.ptV i P' = some x
    · rw [iSup_pos (show P' ∈ {P | D.naut.ptV i P = some x} from hP')] at hg'
      obtain ⟨α', hα', hsv'⟩ := _root_.GlobalTheory.EigInert.exists_satAt_of_nonsplit_over hL D P i P' v w hov hns Dv
      have hub : ubc D.R.nV (D.naut.satV i P' w) = ubc D.R.nV (D.naut.satV i P₀ w) := by
        have h41i := (show _root_.Formalism.MainNotions.SumRepresentations.At.provisionFortyOne D.nd D.naut i from h41 i).2.1 P' P₀ (by rw [hP']; simp) (by rw [hP', hP₀])
        have hS : w ∉ D.nd.S i := fun hm => hns (D.nd.SQ_split i w (Or.inl hm))
        have hQ : w ∉ D.nd.Q i := fun hm => hns (D.nd.SQ_split i w (Or.inr hm))
        exact (h41i.2 w hS hQ).2 hns
      rw [hsv', hα₀] at hub
      have hW := GlobalTheory.T.satakeTransform_eq_of_unramifiedBaseChange_eq _ Dv.ϖ Dv.σw _ D.R.nV Dv.unram α' _ hub h0 hh0
      rw [hc, ← hW]
      have hmem : (P.M.loc i).real g' ∈ NG.isoTyp (P.H.av.rep i P').ρ (P.H.av.rep i P').S := by
        have h2 := hg'
        rw [P.H.av.typeV] at h2
        exact h2
      exact GlobalTheory.T.isotypicFixedVector_isSatakeEigen_inertPlace _ _ (P.H.av.rep i P') v w hov Dv α' hα' _ hmem (hfix g') h0 hh0
    · rw [iSup_neg (show P' ∉ {P | D.naut.ptV i P = some x} from hP')] at hg'
      rw [(Submodule.mem_bot ℂ).1 hg']
      simp [hC]
  · simp [hC]
  · intro g1 g2 h1 h2
    rw [hC] at h1 h2 ⊢
    simp only [map_add, smul_add, Finset.sum_add_distrib, h1, h2]
set_option maxHeartbeats 4000000 in
theorem eig_eq_satU_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w → ∃ P₀, D.naut.ptV i P₀ = some x ∧ ∃ α₀ : Fin ((Formalism.IndefR.Links.Vc D j).rank / 2) → ℂ, D.naut.satV i P₀ w = Finset.univ.val.map α₀ ∧ ∀ (τ : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (ϖ : w.adicCompletion D.host.E), Formalism.UG.IsUnramInv ϖ τ (Formalism.UG.qV D.host.F (w.under (𝓞 D.host.F))) → GlobalTheory.LFun.IsConjAt D.sp.cm.sig (rfl : w.under (𝓞 D.host.F) = _) τ → ∀ (d : Fin (Formalism.IndefR.Links.Vc D j).rank → ℤ) (t' : Formalism.UG.GU τ (Formalism.IndefR.Links.Vc D j).rank), Antitone d → t'.1.1 = Matrix.diagonal (fun k => ϖ ^ d k) → s w (List.ofFn d) = Formalism.UG.SatU ϖ (Formalism.UG.qV D.host.F (w.under (𝓞 D.host.F))) (Formalism.UG.dosetInd ℂ (Formalism.UG.KU τ (Formalism.IndefR.Links.Vc D j).rank) t') α₀ := by
  intro hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 h hops s hs w hG hin
  classical
  have hn : (Formalism.IndefR.Links.Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have hns : ¬ Formalism.BasicNotions.IsSplitPl D.host w := GlobalTheory.T.not_isSplitPlace_of_inert_over_realSubfield D w hin
  have hf0 : (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ≠ 0 := fun e => hy0 (X.hinj _ _ (by
    rw [hy, cast_eq_zero hj f e, map_zero]
    exact congrArg Subtype.val (map_zero (X.IL.jMt _ hμ j))))
  obtain ⟨P₀, hP₀⟩ : ∃ P₀, D.naut.ptV i P₀ = some x := by
    by_contra hne
    apply hf0
    unfold eigC at hf
    have : (⨆ P ∈ {P | D.naut.ptV i P = some x}, D.naut.typeV i P) = ⊥ :=
      iSup_eq_bot.2 fun P' => iSup_eq_bot.2 fun hP' => absurd ⟨P', hP'⟩ hne
    rw [this] at hf
    exact (Submodule.mem_bot ℂ).1 hf
  obtain ⟨v₀, Dv₀, hov₀⟩ := GlobalTheory.T.exists_inertLocalDatum_at_inertPlace D hA.hF w hin
  obtain ⟨α₀, -, hα₀⟩ := _root_.GlobalTheory.EigInert.exists_satAt_of_nonsplit_over hL D P i P₀ v₀ w hov₀ hns Dv₀
  refine ⟨P₀, hP₀, ?_⟩
  rw [hn]
  refine ⟨α₀, hα₀, fun τ ϖ hU hc d t hd ht => ?_⟩
  obtain ⟨v, Dv, hov, rfl, rfl, hq, he, hsupp⟩ :=
    exists_datum D.host.F hA.hF D.sp.cm.sig (fun _ => rfl) D.R.nV w hin τ ϖ hU hc
  obtain ⟨R, hR, hop⟩ := exists_sphOp hn (hA.stdV j) hin Dv hc he (triv_iff (hA.stdV j) hsupp) hd t ht
  have hfix := _root_.GlobalTheory.T.operator_eigen_good_place_first_alt hAF hL D P X hA h41 h7 htl i hμ j hj h hops w hG hin v hov
  have k1 := _root_.GlobalTheory.InertEigSat.heckeFunI_eigC_alt hL D P h41 i x hns hov Dv hfix P₀ hP₀ α₀ hα₀ _
    (Formalism.UG.Final.DosetIndMem _ (Formalism.UG.KU Dv.σw D.R.nV) ℂ t) _ hf
  rw [← hop _ _ (hfix _), hq] at k1
  have k2 := sum_extV X j _ h hops hG hR y _ (hs w _ hG ⟨_, hR⟩)
  obtain ⟨e, hreal⟩ := real_cast hA hμ j _ hj (D.nd.j_range i).1 (D.nd.j_range i).2
  have k3 : ∑ γ ∈ R, NG.rt D.host.E D.R.nV γ ((P.M.loc i).real (hj ▸ f)) =
      s w (List.ofFn d) • (P.M.loc i).real (hj ▸ f) := by
    funext g
    have k4 := congrArg e (k2 ((hA.PV j).ψ ((hA.a j)⁻¹ * g)))
    rw [Finset.sum_image (hA.PV j).inj.injOn, map_sum, map_smul, hy] at k4
    rw [Finset.sum_apply, Pi.smul_apply]
    refine (Finset.sum_congr rfl fun γ _ => ?_).trans (k4.trans (congrArg _ (hreal f g).symm))
    refine (hreal f (g * γ)).trans ?_
    rw [← mul_assoc, map_mul]
  have hne : (P.M.loc i).real (hj ▸ f) ≠ 0 := fun e0 => hf0 ((P.M.loc i).real_inj (e0.trans (map_zero _).symm))
  exact smul_left_injective ℂ hne (k3.symm.trans k1)
end GlobalTheory.InertEigSat
end
end
