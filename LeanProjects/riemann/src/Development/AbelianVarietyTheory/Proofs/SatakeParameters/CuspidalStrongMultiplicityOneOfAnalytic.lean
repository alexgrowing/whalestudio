import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SSAscent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointParOfTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistInvOfCharLawsMultOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCharpolyCoeffOfMatrix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaOQContinuousInjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceGoodSignature
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.RowRepOcc

theorem charLaws_of_tie (D : D7) (h : Formalism.MainNotions.SumRepresentations.tie0 D) : GlobalTheory.TypeLeaf.CharLaws D := fun w a χ χ' h1 h2 =>
  let H := h.1 w a a χ χ' 0 h1 h2
  ⟨H.2.2.2.1, H.2.2.2.2.1⟩

theorem isoLoc_one (D : D7) {a : ℕ} (π : D.naut.CG a) (w : PlE D.host) :
    isoLoc D.nd D.naut [⟨a, π, 1⟩] w = D.naut.locG π w := by
  simp [isoLoc, spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]

theorem cuspidalStrongMultiplicityOne_of_analytic (D : D7) (h : Formalism.MainNotions.SumRepresentations.adm5 D) : GlobalTheory.TypeLeaf.MultOne D := by
  intro a π π' ha hloc
  have hp := h.1 [⟨a, π, 1⟩] [⟨a, π', 1⟩] (by simp [ha]) (by simp [ha])
    (Filter.Eventually.of_forall fun w => by rw [isoLoc_one, isoLoc_one, hloc w])
  rw [List.singleton_perm_singleton] at hp
  exact eq_of_heq (Formalism.BasicNotions.Part.mk.inj hp).2.1

theorem etaShift (D : D7) (h : Formalism.MainNotions.SumRepresentations.tie0 D) (τ : D.host.E →+* ℂ) :
    ∀ z ∈ D.naut.infG D.naut.etaTinv τ, ∃ k : ℤ, z + ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = (k : ℂ) := by
  intro z hz
  obtain ⟨h1, h2⟩ := h.2.1.2.1 τ
  obtain ⟨c, hc⟩ := D.R.t_odd
  have hc' : (D.R.t : ℂ) = 2 * c + 1 := by exact_mod_cast hc
  rw [h2] at hz
  rcases h1 with e | e <;> rw [e] at hz <;> simp at hz <;> subst hz
  · exact ⟨-(c + 1), by push_cast; rw [hc']; ring⟩
  · exact ⟨-c, by push_cast; rw [hc']; ring⟩

theorem pointPar (D : D7) (hT : Formalism.MainNotions.SumRepresentations.tie0 D) (h5 : Formalism.MainNotions.SumRepresentations.adm5 D) : GlobalTheory.TypeLeaf.PointPar D :=
  GlobalTheory.TypeLeaf.pointPar_of_twist D
    (GlobalTheory.TypeLeaf.twistInv_of_charLaws_multOne D (charLaws_of_tie D hT) (cuspidalStrongMultiplicityOne_of_analytic D h5))
    hT.2.1.1.1 (etaShift D hT)

end GlobalTheory.RowRepOcc

noncomputable section

namespace GlobalTheory.RowRepOcc

theorem mapRep_mapRep {Γ : Type} [Group Γ] {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {a : ℕ}
    (f : A →+* B) (g : B →+* C) (ρ : Γ →* GL (Fin a) A) :
    mapRep g (mapRep f ρ) = mapRep (g.comp f) ρ := by
  ext x i j
  simp [mapRep]

theorem coe_mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ}
    (f : A →+* B) (ρ : Γ →* GL (Fin a) A) (x : Γ) :
    ((mapRep f ρ x : GL (Fin a) B) : Matrix (Fin a) (Fin a) B) = ((ρ x : GL (Fin a) A) : Matrix (Fin a) (Fin a) A).map f := by
  simp [mapRep]

theorem isSSRep_map {Γ : Type} [Group Γ] {K L : Type} [Field K] [CharZero K] [Field L] {a : ℕ}
    (f : K →+* L) (ρ : Γ →* GL (Fin a) K) (h : IsSSRep ρ) : IsSSRep (mapRep f ρ) := by
  letI : Algebra K L := f.toAlgebra
  exact ssAscent K L Γ a ρ h

end GlobalTheory.RowRepOcc

noncomputable section

namespace GlobalTheory.RowRepOcc

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

include A in

theorem charZero_Kf (i : N.Loc) : CharZero (Kf N i) :=
  (RingHom.charZero_iff (ϕ := A.iotaQ i) (A.iotaQ i).injective).2 inferInstance

theorem isRepOfSig_transport {i i' : N.Loc} (φ : N.O i' ≃+* N.O i) (hφc : Continuous φ)
    (hφι : ∀ z, iotaO N A i (φ z) = iotaO N A i' z) (Sig : List (Formalism.BasicNotions.Part A.CG))
    (ρ₀ : G H.E N.Om →* GL (Fin R.r) (N.O i')) (h : IsRepOfSig N A i' Sig ρ₀) :
    IsRepOfSig N A i Sig (mapRep φ.toRingHom ρ₀) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [coe_mapRep]
    exact h1.matrix_map hφc
  · haveI := charZero_Kf N A i'
    let ψ : Kf N i' ≃+* Kf N i := IsFractionRing.ringEquivOfRingEquiv φ
    have e : mapRep (algebraMap (N.O i) (Kf N i)) (mapRep φ.toRingHom ρ₀) =
        mapRep ψ.toRingHom (mapRep (algebraMap (N.O i') (Kf N i')) ρ₀) := by
      rw [mapRep_mapRep, mapRep_mapRep]
      congr 1
      ext z
      simp [ψ]
    rw [e]
    exact isSSRep_map ψ.toRingHom _ h2
  · refine h3.mono fun w hw B σ hB hσ => ?_
    rw [coe_mapRep, Matrix.charpoly_map, Polynomial.map_map]
    have : (iotaO N A i).comp φ.toRingHom = iotaO N A i' := by
      ext z
      exact hφι z
    rw [this]
    exact hw B σ hB hσ

end GlobalTheory.RowRepOcc

noncomputable section

namespace GlobalTheory.RowRepOcc

theorem wdOf_of_isRepOfSig (D : D7) (hT : Formalism.MainNotions.SumRepresentations.tie0 D) (h2 : Formalism.MainNotions.SumRepresentations.adm2 D) (h5 : Formalism.MainNotions.SumRepresentations.adm5 D)
    (i : D.nd.Loc) (π : D.naut.CG D.R.r) (hc : D.naut.csd π) (hr : D.naut.ralg π) (hr1 : 1 ≤ D.R.r)
    (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) (hρ : IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ)
    (w : PlE D.host) (hw : w ∉ placesOver D.host.E (D.nd.l i)) :
    D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) ρ) w = D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2) := by
  obtain ⟨r, hrc, hrss, hraway, -⟩ := (h2 i).1 D.R.r hr1 π hc hr
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
        rw [(hraway w' hwl).1]
        exact (D.naut.unr_tw _ _).2 hu
      rw [D.naut.wdOf_frob i r w' hwl hrc hunr B σ hB hσ, (hraway w' hwl).1]
      simp only [coe_mapRep]
      rw [Matrix.charpoly_map, Polynomial.map_map]
      have e : (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) = iotaO D.nd D.naut i := rfl
      rw [e, h1 B σ hB hσ, isoLoc_one]
      rfl)
  obtain ⟨Pm, hPm⟩ := h5.2.2.2 (Qbar (D.nd.l i)) D.R.r r _ hrss hQss hcp
  rw [((hT.2.2.2.2.2 i).2.1 D.R.r r _ hrc Pm hPm).2.1 w (Or.inl hw), (hraway w hw).1]

end GlobalTheory.RowRepOcc

noncomputable section

namespace GlobalTheory.RowRepOcc

theorem rowRepAtG_of_rowPoint : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → Formalism.MainNotions.SumRepresentations.adm2 D → Formalism.MainNotions.SumRepresentations.adm5 D →
    Formalism.MainNotions.SumRepresentations.Conclusion42 D → Formalism.MainNotions.N.GlobalDatumResidualRepCondition D →
    (∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)) → RowPoint D.nd D.naut → RowRepAtG D := by
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
  rw [wdOf_of_isRepOfSig D hT h2 h5 i π hc hr hr1 _ hρ _ hv, ← hW.2.2 _ (hsp k v), isoLoc_one]

end GlobalTheory.RowRepOcc
