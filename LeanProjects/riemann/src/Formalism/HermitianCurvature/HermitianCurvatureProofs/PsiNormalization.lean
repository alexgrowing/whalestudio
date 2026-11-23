import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.FormalDegreeBessel.FinalG

open Matrix MeasureTheory Filter

noncomputable section

namespace Formalism.FourierDecayAlt.P.BesselCapelliCommutation

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

variable {k r : ℕ}

theorem psi_one {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) : psi k r z c 1 = 1 := by
  have heI : ∀ (a : Fin r) (h : (a : ℕ) + 1 < r), eI k r a ≠ eI k r ⟨a + 1, h⟩ := by
    intro a h he
    have := congrArg Fin.val he
    simp [eI] at this
  have hz' : ∀ a : Fin r, z (eI k r a) = 0 := fun a => hz _ (Or.inl (by simp [eI]))
  simp [psi, ell, Matrix.one_apply_ne, heI, hz']

end Formalism.FourierDecayAlt.P.BesselCapelliCommutation

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem bessel_capelli_commute_of_parts : Formalism.FourierDecayAlt.JF.BesselCommutesOfParts := by
  intro hW hCVR hCVU hGq hCI hNE hUE k r Wp Wq _ _ _ _ _ _ D A m F Y hnm hThr hF _hCVF
  have hCk : CkOn (m : ℕ∞) (GV k r) F := hF.choose_spec.1
  have hCkn : CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (GV k r) F := B5.ckOn_mono (by exact_mod_cast hnm) hCk
  have hThr' : TransportedAlt k r A m := hThr
  have := B5.haar_sigmaFinite D.haarW
  have := B5.haar_sigmaFinite D.haarN
  have := B5.haar_sigmaFinite D.haarW'
  have hN := hNE Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F D.z_mem D.z'_mem D.haarN.conc
    (fun n₀ h => D.haarN.left n₀ h)
  refine ⟨JF D F, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F', hU, hgU, hc, he⟩ := (hW k r Wp Wq D A m F hThr' hF).1 g₀ hg₀
    exact ⟨U, F', hU, hgU, hc.of_le (by exact_mod_cast hnm), he⟩
  · intro g _ n hn
    have e := hN g n hn.1 1 WeylGroupFacts.mem_n_one
    rw [Matrix.mul_one, BesselCapelliCommutation.psi_one D.z'_mem, mul_one] at e
    exact e
  · intro g _ n hn
    have e := hN g 1 WeylGroupFacts.mem_n_one n hn.1
    rw [Matrix.one_mul, BesselCapelliCommutation.psi_one D.z_mem, one_mul] at e
    exact e
  · intro g _ h hh h' hh'
    exact hUE Wp Wq k r D.z D.z' cStd D.π D.π' D.μW D.μN D.μW' F D.z_mem D.z'_mem D.haarN.conc D.haarW.conc
      D.haarW'.conc (fun h₀ hh₀ => D.haarW.left h₀ hh₀) (fun h₀ hh₀ => D.haarW'.left h₀ hh₀) (hCI k r Wp Wq D)
      D.π_rep D.π'_rep g h hh h' hh'
  · exact Filter.Eventually.of_forall fun q => rfl
  · filter_upwards [hGq k r Wp Wq D] with q hq
    rw [hCVU k r Wp Wq D A m F Y hnm hThr' hF (gq D q) hq]
    show _ = ∫ p, xiP D p • rho D p (Q.CV k r Y F) (gq D q) ∂D.μSS
    refine integral_congr_ae ?_
    filter_upwards [B5.ae_inSS D] with p hp
    rw [hCVR k r Wp Wq D Y F p hp hCkn (gq D q) hq.1]

end Formalism.FourierDecayAlt.P
