import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilityEighth
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodOffGpStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TransportStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerMoreStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLocCompHasSatakeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocVUnrFrobEigOfHasSatakeStatement
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.StrSplitDict.dict_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D) (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i))) (Formalism.IndefR.Links.Vc D j).rank s B → ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → ∃ Q : D.naut.AV i, D.naut.ptV i Q = some x ∧ D.naut.unr (D.naut.locV i Q w) ∧ (B w).map (fun a : ℂˣ => (a : ℂ)) = (D.naut.frobEig (D.naut.locV i Q w)).map (fun a : ℂ => a⁻¹) := by
  intro hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 h hh s B hs hB w hw hsp
  have hrank : (Formalism.IndefR.Links.Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  obtain ⟨sp, hspw, hJ⟩ := _root_.GlobalTheory.T.isSplit_of_hk3_good hAF hL D P X hA h41 h7 htl i w hw hsp
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
  have htr := _root_.GlobalTheory.T.extension_vector_theta_compatible_alt hAF hL D P X hA h41 h7 htl i hμ j hj f y hy h hh s hs sp hw hJ
  obtain ⟨Q, hQx, F, hFi, hFt, hF0, hFe⟩ := _root_.GlobalTheory.T.exists_automorphic_vector_satake_alt hL D P i x _ hf hf'0 sp
    (fun k => s sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0)) htr
  obtain ⟨σ, α, hloc, hsat, hα⟩ := _root_.GlobalTheory.T.iso_type_space_maximal_compact_alt hAF hL D P i Q sp hJ (B sp.w) hcard F hFi hFt hF0
    (fun ϖ hϖ k hk => by rw [hFe ϖ hϖ k hk, heq k hk])
  obtain ⟨hu, hfr⟩ := _root_.GlobalTheory.T.unr_and_frobEig_eq_inv_satake hL D P i Q sp σ α hloc hsat
  refine ⟨Q, hQx, hu, ?_⟩
  rw [hfr, ← hα]
  simp [Multiset.map_map, Function.comp_def]
end
