import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFormalGroupCocycleIffMemCocyclesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitCotangentClassPowerSeriesEvalAtNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDifferentialsConnectedPDivGroupCoordinaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearPDivGroupHomEvalTwoVariableSeries
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem GlobalTheory.Katz.rig_pull_natural_semi : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (φ : Fin d → MvPowerSeries (Fin e) k') (ρ : MvPowerSeries (Fin d ⊕ Fin d) k × (Fin d → k) →ₗ[k] G.RigExt) (ρ' : MvPowerSeries (Fin e ⊕ Fin e) k' × (Fin e → k') →ₗ[k'] G'.RigExt), c.IsLawOf μ → (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → (∀ t w (z : G.cocycles) (u : G.omega), (∀ n, z.1 n = c.ev₂ n t) → (∀ n, u.1 n = ∑ i, w i • dUnit k (c.x n i)) → ρ (t, w) = G.rigMk (z, u)) → (∀ t w (z : G'.cocycles) (u : G'.omega), (∀ n, z.1 n = c'.ev₂ n t) → (∀ n, u.1 n = ∑ i, w i • dUnit k' (c'.x n i)) → ρ' (t, w) = G'.rigMk (z, u)) → ∀ t w, IsCoc μ t → ρ' (pull2 φ (MvPowerSeries.map σ t), pullLin φ (fun i => σ (w i))) = s.rig (ρ (t, w)) := by
  intro p k k' _ _ σ d e G G' c c' s μ φ ρ ρ' hμ hφ hρ hρ' t w ht
  have hz : (fun n => c.ev₂ n t) ∈ G.cocycles := (GlobalTheory.T.isSymmetricFormalGroupCocycle_iff_mem_cocycles p k d G c μ hμ t).1 ht
  have hu : (fun n => ∑ i, w i • dUnit k (c.x n i)) ∈ G.omegaSub := (GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates p k d G c).1 w
  rw [hρ t w ⟨_, hz⟩ ⟨_, hu⟩ (fun _ => rfl) (fun _ => rfl), SemiHom.rig_mk]
  have hev : ∀ n, c'.ev₂ n (pull2 φ (MvPowerSeries.map σ t)) = (s.app n).two (c.ev₂ n t) := by
    intro n
    exact GlobalTheory.Katz.semiHom_ev₂_pull2 p k k' σ d e G G' c c' s φ hφ n t
  refine hρ' _ _ _ _ (fun n => ?_) (fun n => ?_)
  · rw [SemiHom.cocycles_val, hev n]
  · rw [SemiHom.omega_val]
    change (s.app n).cot (∑ i, w i • dUnit k (c.x n i)) = _
    rw [map_sum]
    simp only [map_smulₛₗ, SemiBialgHom.cot_d]
    have hd : ∀ i, dUnit k' (s.app n (c.x n i)) = ∑ l, lin (φ i) l • dUnit k' (c'.x n l) := fun i => by
      rw [← hφ n i]
      exact (GlobalTheory.T.counit_cotangentClass_powerSeriesEvalAtNilpotent k' e (G'.A n) (c'.x n) (c'.nil n) (c'.aug n) (φ i)).2
    simp only [hd, Finset.smul_sum, smul_smul, pullLin, Finset.sum_smul]
    exact Finset.sum_comm
