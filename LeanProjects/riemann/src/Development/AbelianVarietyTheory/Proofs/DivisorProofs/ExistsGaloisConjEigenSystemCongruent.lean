import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisLiftResidueCongruencePadicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensorStatement

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.ExpFrame.Conj

theorem isEig_map {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (F : Frame l ι N)
    (mu : ι → ℕ → ℕ) (g : PadicAlgCl l ≃+* PadicAlgCl l) (hg : ∀ x, g (F.emb x) = F.emb x)
    (θ : F.I → PadicAlgCl l) (h : F.IsEig mu θ) : F.IsEig mu (fun i => g (θ i)) := by
  obtain ⟨f, hf0, ⟨hΓ, hK⟩, hH⟩ := h
  obtain ⟨Φ, hinj, hsm, hgrp⟩ := GlobalTheory.T.exists_semilinear_action_dualWeylTensor (PadicAlgCl l) ι N mu g
  refine ⟨fun x => Φ (f x), ?_, ⟨fun γ hγ x => by simp only [hΓ γ hγ x], fun κ x => ?_⟩, fun i x => ?_⟩
  · intro h0
    apply hf0
    funext x
    have := congrFun h0 x
    exact hinj (by simpa using this)
  · have hfix : ∀ τ a b, g ((Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ) : Matrix (Fin N) (Fin N) (PadicAlgCl l)) a b) =
        (Matrix.GeneralLinearGroup.map F.emb (F.kap κ τ) : Matrix (Fin N) (Fin N) (PadicAlgCl l)) a b := by
      intro τ a b
      simp [hg]
    rw [← hgrp _ hfix, ← hg (F.chi κ : F.O), ← hsm, hK κ x]
  · have := hH i x
    simp only
    rw [← hg (F.cst i), ← map_sum, ← hsm, this, hsm]

theorem exists_eig_congr : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ), F.Ok → ∀ (θ θ0 : F.I → PadicAlgCl l) (m : Ideal F.T), F.IsEig lam θ → F.Over θ m → F.Over θ0 m → ∃ θ', F.IsEig lam θ' ∧ (∀ i, ‖θ' i‖ ≤ 1) ∧ ∀ i, ‖θ' i - θ0 i‖ < 1 := by
  intro l _ ι _ _ N F lam hOk θ θ0 m hE hθ hθ0
  obtain ⟨_, L, hfin, hrange⟩ := hOk.ring
  have hmemL : ∀ x, F.emb x ∈ L := fun x => by
    have : F.emb x ∈ Set.range F.emb := ⟨x, rfl⟩
    rw [hrange] at this
    exact this.1
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_galois_lift_residue_congruence_padic l L F.I θ θ0 hθ.1 hθ0.1 (by
    intro p hp
    have hmem : p ∈ Set.range (MvPolynomial.map F.emb) := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro c hc
      obtain ⟨n, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hc
      rw [hrange]
      exact hp n
    obtain ⟨q, rfl⟩ := hmem
    rw [MvPolynomial.eval_map, MvPolynomial.eval_map, ← hθ.2 q, hθ0.2 q])
  have hn : ∀ x, ‖g x‖ = ‖x‖ := fun x => (spectralNorm_eq_of_equiv (g.restrictScalars ℚ_[l]) x).symm
  refine ⟨fun i => g (θ i), isEig_map F lam g.toRingEquiv (fun x => g.commutes ⟨F.emb x, hmemL x⟩) θ hE,
    fun i => (hn _).trans_le (hθ.1 i), hg⟩

end GlobalTheory.ExpFrame.Conj
