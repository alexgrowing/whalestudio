import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalStrongMultiplicityOneOfAnalytic
import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.CuspOfCq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
noncomputable section
namespace GlobalTheory.RowRepOcc
theorem wdOf_of_isRepOfSig_alt_alt (D : D7) (hT : Formalism.MainNotions.SumRepresentations.tie0 D) (h2 : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D) (h5 : Formalism.MainNotions.SumRepresentations.adm5 D)
    (i : D.nd.Loc) (π : D.naut.CG D.R.r) (hc : D.naut.csd π) (hr : D.naut.ralg π) (hr1 : 1 ≤ D.R.r)
    (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) (hρ : IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ)
    (w : PlE D.host) (hw : w ∉ placesOver D.host.E (D.nd.l i)) :
    UpperTheory.GalS.RelW D.nd D.naut (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) ρ) w)
      (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) := by
  obtain ⟨r, hrc, hrss, hraway, -⟩ := (_root_.UpperTheory.GalS.weak' h2 i).1 D.R.r hr1 π hc hr
  have hι := GlobalTheory.TypeLeaf.iotaOQ_continuous_injective D i
  haveI := charZero_Kf D.nd D.naut i
  have hQc : Continuous fun g => ((mapRep (iotaOQ D.nd D.naut i) ρ g : GL _ _) :
      Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.nd.l i))) := by
    simp only [coe_mapRep]
    exact hρ.1.matrix_map hι.1
  have hQss : IsSSRep (mapRep (iotaOQ D.nd D.naut i) ρ) := by
    have e : mapRep (iotaOQ D.nd D.naut i) ρ =
        mapRep (D.naut.iotaQ i) (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) ρ) := by
      rw [mapRep_mapRep]
      rfl
    rw [e]
    exact isSSRep_map _ _ hρ.2.1
  have hfin : (placesOver D.host.E (D.nd.l i)).Finite :=
    placesOver_finite_joint_conditions_zpowers D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero
  have hall := hρ.2.2.and ((D.naut.locG_unr_ae π).and hfin.eventually_cofinite_notMem)
  have hdense := dense_iff_closure_eq.2 (h5.2.2.1 _ (Filter.eventually_cofinite.1 hall))
  have hcp := GlobalTheory.TypeLeaf.charpoly_eq_of_dense _ (Qbar (D.nd.l i)) D.R.r
    (fun g => ((r g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.nd.l i))))
    (fun g => ((mapRep (iotaOQ D.nd D.naut i) ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.nd.l i))))
    _ hdense hrc hQc (by
      rintro σ ⟨w', hw', -, B, hB, hσ⟩
      obtain ⟨h1, hu, hwl⟩ := not_not.1 hw'
      apply Polynomial.map_injective (D.naut.iotaQC i).toRingHom (D.naut.iotaQC i).injective
      have hunr : D.naut.unr (D.naut.wdOf i r w') := by
        rw [(hraway w' hwl).eq_of_unr ((D.naut.unr_tw _ _).2 hu)]
        exact (D.naut.unr_tw _ _).2 hu
      rw [D.naut.wdOf_frob i r w' hwl hrc hunr B σ hB hσ, (hraway w' hwl).eq_of_unr ((D.naut.unr_tw _ _).2 hu)]
      simp only [coe_mapRep]
      rw [Matrix.charpoly_map, Polynomial.map_map]
      have e : (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) = iotaO D.nd D.naut i := rfl
      rw [e, h1 B σ hB hσ, isoLoc_one]
      rfl)
  obtain ⟨Pm, hPm⟩ := h5.2.2.2 (Qbar (D.nd.l i)) D.R.r r _ hrss hQss hcp
  rw [((hT.2.2.2.2.2 i).2.1 D.R.r r _ hrc Pm hPm).2.1 w (Or.inl hw)]
  exact hraway w hw
theorem repAtGN_of_point_split : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → Formalism.MainNotions.SumRepresentations.adm5 D →
    Formalism.MainNotions.SumRepresentations.Conclusion42 D → Formalism.MainNotions.N.GlobalDatumResidualRepCondition D →
    (∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)) → RowPoint D.nd D.naut → UpperTheory.GalS.RowRepAtGN D := by
  intro D hT h2 h5 h42 hJ hsp hRP i σ hne hg
  obtain ⟨i', hj, hl, hloc, ⟨φ, hφc, hφι⟩, P, x, hθ, hPx⟩ := hRP i σ hne
  have hne' : D.what₂.isot (D.nd.j i') σ ≠ ⊥ := by rw [hj]; exact hne
  obtain ⟨-, ⟨Sig, hW', hBC⟩, hcusp⟩ := h42 i' σ hne'
  have hB := hBC P hθ
  have hX : HasParamX D.nd D.naut i' x Sig := ⟨P, hPx, hB⟩
  have hgs : goodSig D.nd D.naut Sig := (GlobalTheory.Proof.SplitPlaceGoodSignature.goodRow_iff_goodSig D.nd D.naut hW'.2.2).1 hg
  have hZ : x ∈ ZgoodN D.nd D.naut i' :=
    ⟨⟨P, hPx, _, hB, List.mem_map.2 ⟨muPart D.nd D.naut i', by simp, rfl⟩⟩, Sig, hX, hgs⟩
  obtain ⟨ρ₀, -, hρ₀, -, -⟩ := hJ i' x hZ Sig hX hgs
  obtain ⟨π, rfl⟩ := hcusp hg Sig hW'
  have hr1 : 1 ≤ D.R.r := (hW'.1 _ (List.mem_singleton_self _)).1
  obtain ⟨hc, hr⟩ := pointPar D hT h5 i' x π hX
  have hW : HasParamW D.nd D.naut i σ [⟨D.R.r, π, 1⟩] :=
    ⟨hW'.1, hW'.2.1, fun w hw => (hW'.2.2 w hw).trans (hloc w hw)⟩
  have hρ := isRepOfSig_transport D.nd D.naut φ hφc hφι _ ρ₀ hρ₀
  refine ⟨_, _, hW, hρ, fun k v hkl => ?_⟩
  have hv : D.naut.plGw k v ∉ placesOver D.host.E (D.nd.l i) :=
    Formalism.MainNotions.N.placesOver_disj D.host.E (D.host.g_prime k) (D.nd.lPrime i).out (Ne.symm hkl) _ (D.naut.plGw_over k v)
  rw [← hW.2.2 _ (hsp k v), isoLoc_one]
  exact _root_.GlobalTheory.RowRepOcc.wdOf_of_isRepOfSig_alt_alt D hT h2 h5 i π hc hr hr1 _ hρ _ hv
end GlobalTheory.RowRepOcc
end
end
