import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPair
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLSAExh
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLQOf

open MeasureTheory Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem spectral_pairing_exhaustion : RDSPExh := by
  intro k r Wp Wq _ _ _ _ _ _ D X hX C hC hCO
  have hX' : X ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') := by
    rwa [rdb_ffl_om_eq] at hX
  have hqC : IsCompact (Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf D.z D.z' '' C) :=
    hC.image_of_continuousOn ((Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf_contOn D.z D.z').mono fun g hg => (hCO hg).2)
  have hqQ : Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf D.z D.z' '' C ⊆ JF.QDom k r D.z D.z' := by
    rintro _ ⟨g, hg, rfl⟩
    exact (Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.om_eq_sgs D (hCO hg)).choose_spec.2.1
  obtain ⟨K', hK'c, hCK', hK'Q⟩ := exists_compact_between hqC (Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open D.z D.z') hqQ
  obtain ⟨φ, hφ, ⟨C', hC'c, hC'O, hC'φ⟩, hint⟩ :=
    Formalism.FourierDecayAlt.P.CutMP.JA.SA.average_one_cutoff_on_orbits k r Wp Wq D K' hK'c hK'Q
  have hsuppC : tsupport (fun g => φ g • X g) ⊆ C' := by
    refine closure_minimal (fun g hg => ?_) hC'c.isClosed
    by_contra hgC
    exact hg (by simp [hC'φ g hgC])
  refine ⟨fun g => φ g • X g,
    Q.OmPlus k r D.z D.z' ∩ Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf D.z D.z' ⁻¹' interior K', ?_, ?_, ?_,
    Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.isOpen_qOf D.z D.z' isOpen_interior, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    by_cases hO : g₀ ∈ Q.OmPlus k r D.z D.z'
    · obtain ⟨U₁, φ', hU₁, hg₁, hφ', hφe⟩ := hφ g₀ hg₀
      obtain ⟨U₂, f', hU₂, hg₂, hf', hfe⟩ := hX'.1 g₀ ⟨(Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g₀).2 hg₀, hO⟩
      refine ⟨U₁ ∩ U₂, fun g => φ' g • f' g, hU₁.inter hU₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
      · exact (hφ'.mono Set.inter_subset_left).smul (hf'.mono Set.inter_subset_right)
      · intro g hg hgG
        simp only [hφe g hg.1 hgG, hfe g hg.2 ((Formalism.FourierDecayAlt.P.CapelliUnderIntegral.glev0 g).2 hgG)]
    · refine ⟨C'ᶜ, fun _ => 0, hC'c.isClosed.isOpen_compl, fun h => hO (hC'O h).2, contDiffOn_const, ?_⟩
      intro g hg _
      simp [hC'φ g hg]
  · exact hC'c.of_isClosed_subset (isClosed_tsupport _) hsuppC
  · exact hsuppC.trans hC'O
  · intro g hg
    exact ⟨(hCO hg).2, hCK' ⟨g, hg, rfl⟩⟩
  · intro p hp g hg hs
    refine ⟨hg.2, ?_⟩
    have h2 := hs.2
    simp only [Set.mem_preimage] at h2 ⊢
    rwa [Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.qOf_sgs D hp] at h2
  · intro g hg
    have hJ : B.JF D (fun g => φ g • X g) g = (∫ p, φ (B.sgs p g) ∂D.μSS) • X g := by
      change ∫ p, JF.xiP D p • B.rho D p (fun g => φ g • X g) g ∂D.μSS = _
      rw [← integral_smul_const]
      apply integral_congr_ae
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
      have hr : B.rho D p (fun g => φ g • X g) g = φ (B.sgs p g) • B.rho D p X g := by
        unfold B.rho
        rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
      rw [hr, smul_comm, Formalism.FourierDecayAlt.P.CutMP.JA.SA.eqv_of_FFl D X hX' hp hg]
    refine ⟨fun hgU => ?_, fun h0 => by rw [hJ, h0, smul_zero]⟩
    obtain ⟨p₀, hp₀, -, hge⟩ := Formalism.FourierDecayAlt.P.CutMP.JA.SA.QO.om_eq_sgs D hg
    have h1 := hint p₀ hp₀ _ (interior_subset hgU.2)
    rw [← hge] at h1
    rw [hJ, h1, one_smul]

end Formalism.FourierDecayAlt.P.CutSE
