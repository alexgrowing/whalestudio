import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertSatakeParametersEqOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosetsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosetsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotIsSplitPlaceOfInertOverRealSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInertLocalDatumAtInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorEigenGoodPlaceFirstStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorEigenGoodPlaceSecondStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSatakeParameterSphericalInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicFixedVectorIsSatakeEigenInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeTransformEqOfUnramifiedBaseChangeEqStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.EigInert.satParam : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (i : D.nd.Loc) (P' : D.naut.AV i) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (w : HeightOneSpectrum (𝓞 D.host.E)), NG.OverPl w v → ¬ Formalism.BasicNotions.IsSplitPl D.host w → ∀ Dv : InertDatum D.host.E D.R.nV v w, ∃ α, NG.SatAt (P.H.av.rep i P') Dv α ∧ D.naut.satV i P' w = Multiset.map α Finset.univ.val := by
  intro hL D P i P' v w hov hns Dv
  have hsph := D.nbc.embAV_sph i P' w hns
  rw [P.H.emb i P'] at hsph
  have hS : (P.H.av.rep i P').SphAt v := (P.H.au.sph (D.nd.j i) _ _ (P.H.av.rep i P') w v hns hov).1 hsph
  obtain ⟨α, hα, hsat⟩ := P.H.au.sat (D.nd.j i) _ _ (P.H.av.rep i P') v w hov Dv (GlobalTheory.T.exists_satakeParameter_spherical_inertPlace _ _ _ v w hov Dv hS)
  refine ⟨α, hα, ?_⟩
  rw [D.nbc.embAV_sat, P.H.emb]
  exact hsat

theorem GlobalTheory.EigInert.heckeFunI_umax_sum {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} {w : HeightOneSpectrum (𝓞 L)} (Dv : InertDatum L n v w)
    (h : Formalism.UG.GU Dv.σw n → ℂ) (hh : h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n)) :
    ∃ (C : Finset (GAf L n ⧸ Umax L n)) (a : GAf L n ⧸ Umax L n → ℂ) (x : GAf L n ⧸ Umax L n → GAf L n),
      ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (φ : GAf L n → W),
        heckeFunI L n (Umax L n) Dv h φ = ∑ c ∈ C, a c • NG.rt L n (x c) φ :=
  GlobalTheory.SatIso.heckeFunI_eq_sum Dv _ h (GlobalTheory.T.finite_inertHecke_support_cosets L n v w Dv (GlobalTheory.T.unitary_doubleCoset_finite_left_cosets Dv.ϖ Dv.σw _ n Dv.unram)
    (GlobalTheory.T.mem_maxCompact_of_trivOutside_local_integral L n v w Dv) _ (fun _ _ => Iff.rfl) h hh)

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.EigInert.eigen_at_inert : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.UG.IsInertAt D.host.F D.host.E (Pp.under (𝓞 D.host.F)) Pp → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∃ c : ℂ, h Pp (Finsupp.single d 1) y = c • y := by
  intro hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 h hops Pp hG hin d hd
  classical
  have hns : ¬ Formalism.BasicNotions.IsSplitPl D.host Pp := GlobalTheory.T.not_isSplitPlace_of_inert_over_realSubfield D Pp hin
  obtain ⟨v, Dv, hov⟩ := GlobalTheory.T.exists_inertLocalDatum_at_inertPlace D hA.hF Pp hin
  have hfix := GlobalTheory.T.operator_eigen_good_place_first hAF hL D P X hA h41 h7 htl i hμ j hj h hops Pp hG hin v hov
  obtain ⟨h0, hh0, htr⟩ := GlobalTheory.T.operator_eigen_good_place_second hAF hL D P X hA h41 h7 htl i hμ j hj h hops Pp hG hin d hd v Dv hov
  obtain ⟨C, a, xs, hC⟩ := GlobalTheory.EigInert.heckeFunI_umax_sum Dv h0 hh0
  let c : ℂ := if hP : ∃ P0 : D.naut.AV i, D.naut.ptV i P0 = some x then
    Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield D.host.E) v) h0 (GlobalTheory.EigInert.satParam hL D P i hP.choose v Pp hov hns Dv).choose else 0
  refine ⟨c, htr f y c hy (hfix (hj ▸ f)) ?_⟩
  have key : ∀ g ∈ eigC D.nd D.naut i x, heckeFunI D.host.E D.R.nV (Umax D.host.E D.R.nV) Dv h0 ((P.M.loc i).real g) =
      c • (P.M.loc i).real g := by
    intro g hg
    unfold eigC at hg
    refine Submodule.iSup_induction _ (motive := fun g => heckeFunI D.host.E D.R.nV (Umax D.host.E D.R.nV) Dv h0
      ((P.M.loc i).real g) = c • (P.M.loc i).real g) hg ?_ ?_ ?_
    · intro P' g' hg'
      by_cases hP' : D.naut.ptV i P' = some x
      · rw [iSup_pos (show P' ∈ {P | D.naut.ptV i P = some x} from hP')] at hg'
        have hex : ∃ P0 : D.naut.AV i, D.naut.ptV i P0 = some x := ⟨P', hP'⟩
        have hc : c = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV _ v) h0 (GlobalTheory.EigInert.satParam hL D P i hex.choose v Pp hov hns Dv).choose := dif_pos hex
        obtain ⟨α', hα', hsv'⟩ := GlobalTheory.EigInert.satParam hL D P i P' v Pp hov hns Dv
        have hsv0 := (GlobalTheory.EigInert.satParam hL D P i hex.choose v Pp hov hns Dv).choose_spec.2
        have hub : ubc D.R.nV (D.naut.satV i P' Pp) = ubc D.R.nV (D.naut.satV i hex.choose Pp) := by
          have h41i := (show Formalism.MainNotions.SumRepresentations.At.Conclusion41 D.nd D.naut i from h41 i).2.1 P' hex.choose (by rw [hP']; simp) (by rw [hP', hex.choose_spec])
          have hS : Pp ∉ D.nd.S i := fun hm => hns (D.nd.SQ_split i Pp (Or.inl hm))
          have hQ : Pp ∉ D.nd.Q i := fun hm => hns (D.nd.SQ_split i Pp (Or.inr hm))
          exact (h41i.2 Pp hS hQ).2 hns
        rw [hsv', hsv0] at hub
        have hW := GlobalTheory.T.satakeTransform_eq_of_unramifiedBaseChange_eq _ Dv.ϖ Dv.σw _ D.R.nV Dv.unram α' _ hub h0 hh0
        rw [hc, ← hW]
        have hmem : (P.M.loc i).real g' ∈ NG.isoTyp (P.H.av.rep i P').ρ (P.H.av.rep i P').S := by
          have h2 := hg'
          rw [P.H.av.typeV] at h2
          exact h2
        exact GlobalTheory.T.isotypicFixedVector_isSatakeEigen_inertPlace _ _ (P.H.av.rep i P') v Pp hov Dv α' hα' _ hmem (hfix g') h0 hh0
      · rw [iSup_neg (show P' ∉ {P | D.naut.ptV i P = some x} from hP')] at hg'
        rw [(Submodule.mem_bot ℂ).1 hg']
        simp [hC]
    · simp [hC]
    · intro g1 g2 h1 h2
      rw [hC] at h1 h2 ⊢
      simp only [map_add, smul_add, Finset.sum_add_distrib, h1, h2]
  exact key _ hf
