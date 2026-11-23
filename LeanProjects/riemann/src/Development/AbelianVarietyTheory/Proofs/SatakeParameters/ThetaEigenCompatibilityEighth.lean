import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParamDefinite
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExtensionVectorThetaCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGoodStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAutomorphicVectorSatakeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsoTypeSpaceMaximalCompactStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeUnramifiedFrobeniusEigenStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.StrSplitDict.cast_ne_zero : ∀ (D : D7) (μ : D.what₂.Tup) (a b : ℕ) (h : a = b) (f : D.what₂.Mt μ a), f ≠ 0 → (h ▸ f : D.what₂.Mt μ b) ≠ 0 := by
  intro D μ a b h f hf
  subst h
  exact hf

theorem GlobalTheory.StrSplitDict.dict : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D) (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i))) (Formalism.IndefR.Links.Vc D j).rank s B → ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → ∃ Q : D.naut.AV i, D.naut.ptV i Q = some x ∧ D.naut.unr (D.naut.locV i Q w) ∧ (B w).map (fun a : ℂˣ => (a : ℂ)) = (D.naut.frobEig (D.naut.locV i Q w)).map (fun a : ℂ => a⁻¹) := by
  intro hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 h hh s B hs hB w hw hsp
  have hrank : (Formalism.IndefR.Links.Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  obtain ⟨sp, hspw, hJ⟩ := GlobalTheory.T.good_place_split_of_tieLab hAF hL D P X hA h41 h7 htl i w hw hsp
  have hv : w.under (𝓞 D.host.F) ∉ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i)) :=
    (GlobalTheory.DownLift.Params.good_iff _ _ _).1 hw
  rcases hB _ hv w rfl with ⟨-, hcard, heq⟩ | ⟨hin, -⟩
  swap
  · exact absurd hsp (GlobalTheory.LFun.not_isSplit_of_isInertAt hin)
  rw [hrank] at hcard heq
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hy0
    have h1 : X.R.extV j (X.tupT (D.nd.mu i)) y = 0 := by
      rw [hy]
      show (X.IL.jMt (D.nd.mu i) hμ j 0).1 = 0
      simp only [map_zero, ZeroMemClass.coe_zero, Submodule.coe_zero]
    exact X.hinj j (X.tupT (D.nd.mu i)) (h1.trans (LinearMap.map_zero _).symm)
  have hf'0 := GlobalTheory.StrSplitDict.cast_ne_zero D _ _ _ hj f hf0
  subst hspw
  have htr := GlobalTheory.T.extension_vector_theta_compatible hAF hL D P X hA h41 h7 htl i hμ j hj f y hy h hh s hs sp hw hJ
  obtain ⟨Q, hQx, F, hFi, hFt, hF0, hFe⟩ := GlobalTheory.T.exists_automorphic_vector_satake hL D P i x _ hf hf'0 sp
    (fun k => s sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0)) htr
  obtain ⟨σ, α, hloc, hsat, hα⟩ := GlobalTheory.T.iso_type_space_maximal_compact hAF hL D P i Q sp hJ (B sp.w) hcard F hFi hFt hF0
    (fun ϖ hϖ k hk => by rw [hFe ϖ hϖ k hk, heq k hk])
  obtain ⟨hu, hfr⟩ := GlobalTheory.T.satake_unramified_frobenius_eigen hL D P i Q sp σ α hloc hsat
  refine ⟨Q, hQx, hu, ?_⟩
  rw [hfr, ← hα]
  simp [Multiset.map_map, Function.comp_def]
