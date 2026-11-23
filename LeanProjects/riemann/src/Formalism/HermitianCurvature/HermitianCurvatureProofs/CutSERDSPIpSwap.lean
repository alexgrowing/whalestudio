import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPair

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem spectral_pairing_inner_swap : RDSPIpSwap := by
  intro k r z z' Wp Wq _ _ _ _ _ _ π π' μ Φ Ψ c
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin r => ℂ)
    (Equiv.subtypeUnivEquiv (p := fun l : Fin r => ((0 : Fin (r + 1)) : ℕ) ≤ l) (fun l => Nat.zero_le _))
  set e := MeasurableEquiv.piCongrLeft (fun _ : Fin r => ℂ)
    (Equiv.subtypeUnivEquiv (p := fun l : Fin r => ((0 : Fin (r + 1)) : ℕ) ≤ l) (fun l => Nat.zero_le _)) with he
  have happ : ∀ (c' : Cf r 0) (l : {l : Fin r // ((0 : Fin (r + 1)) : ℕ) ≤ l}), e c' l.1 = c' l := by
    intro c' l
    rw [he]
    exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin r => ℂ)
      (Equiv.subtypeUnivEquiv (p := fun l : Fin r => ((0 : Fin (r + 1)) : ℕ) ≤ l) (fun l => Nat.zero_le _)) c' l
  have hglue : ∀ c' : Cf r 0, glue 0 c c' = e c' := fun c' => funext fun l => by
    simp only [glue]
    rw [dif_pos (show ((0 : Fin (r + 1)) : ℕ) ≤ (l : ℕ) from Nat.zero_le _)]
    exact (happ c' ⟨l, Nat.zero_le _⟩).symm
  have hprod : ∀ c' : Cf r 0,
      (∏ l : {l : Fin r // ((0 : Fin (r + 1)) : ℕ) ≤ l}, ‖c' l‖ ^ (-2 : ℤ)) = ∏ l : Fin r, (‖e c' l‖ ^ 2)⁻¹ := by
    intro c'
    refine Fintype.prod_equiv (Equiv.subtypeUnivEquiv (fun l => Nat.zero_le _)) _ _ (fun l => ?_)
    show ‖c' l‖ ^ (-2 : ℤ) = (‖e c' l.1‖ ^ 2)⁻¹
    rw [happ c' l, zpow_neg]
    norm_cast
  unfold radIp LocFacts₂ pairAt dxc
  simp only [B.hsInner]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  rw [← hmp.integral_comp']
  refine integral_congr_ae (ae_of_all _ fun c' => ?_)
  simp only
  rw [hglue c', ENNReal.toReal_ofReal (Finset.prod_nonneg fun _ _ => by positivity), Complex.real_smul, hprod c']

end Formalism.FourierDecayAlt.P.CutSE
