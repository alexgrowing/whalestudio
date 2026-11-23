import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentMulIdemSumEqZeroOfNotMemStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardLatticeHomCompletionStableSplitIdempotenStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfEqOfEqOnRationalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceModelStandardLatticeValuesAreThetaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatTensorHalfAddPlaceIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocalModelTensorWithHalfFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelTensorIntegralIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIntegralMatrixIndicatorMemSchwartzBruhStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
namespace GlobalTheory.LocMod

theorem pi_e_self {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : p.π p.e = 1 := by
  have h := p.ι_π 1
  rw [map_one, mul_one] at h
  rw [← h, p.π_ι]

theorem pi_eq_zero_of {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {e : AE D} (h : e * p.e = 0) : p.π e = 0 := by
  have := congrArg p.π h
  rwa [map_mul, pi_e_self, mul_one, map_zero] at this

theorem up_down_eq {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (t : WO S T) :
    p.up FS FT (p.down FS FT t) = t.map (fun x => p.e * x) := by
  unfold Place.up Place.down
  have hM : FT.β * (FT.γ * (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π * FS.β) * FS.γ =
      (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
  rw [hM]
  ext i j
  simp only [Matrix.map_apply, p.ι_π]

theorem ratDatum_factor : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → DenseRange p.pr → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D), PP ∉ P → Formalism.L2.NTheta.IsIdemAt p.e PP → IsIdemSum e P → IsIdemSum (e + p.e) (@insert _ _ (@Finset.instInsert _ (Classical.decEq _)) PP P) → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ↔ p.up FS FT x ∈ stdHom S T) → ∀ (Ξ Ξ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (Ξk : Matrix Y Y' k → ℂ), Ξk ∈ SB (Matrix Y Y' k) → (∀ γ, Ξ' γ = Ξ γ * Ξk (FT.γ * γ.map p.pr * FS.β)) → ∀ c, p.IsCombAt ψ FS FT c Ξk → ∀ f₀ f f', IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (stdHom S T) f₀ → IsRatDatum ψ S T e Ξ f₀ f → IsRatDatum ψ S T (e + p.e) Ξ' f₀ f' → f' = comb ψ S T c f := by
  intro D k _ _ _ _ p ψ hψ _hdense S T Y Y' _ _ _ _ FS FT P PP e hPP hIdemAt hE hE' hstd Ξ Ξ' Ξk hΞk hΞ' c hc f₀ f f' hf₀ hvac hf hf'
  obtain ⟨Φ, hΦSB, hΦrat, hθ⟩ := hf
  obtain ⟨Φ', hΦ'SB, hΦ'rat, hθ'⟩ := hf'
  obtain ⟨T', hT'⟩ := hθ'.1
  have hf'T : f' = T' Φ' := hθ'.2 T' hT'
  have horth : e * p.e = 0 := GlobalTheory.T.splitPlaceIdempotent_mul_idemSum_eq_zero_of_not_mem D k p P PP e hPP hIdemAt hE
  have hstabp := GlobalTheory.T.standardLatticeHomCompletion_stable_splitIdempotent D S T p.e p.split
  have hθT' := GlobalTheory.T.placeModel_standardLattice_values_are_theta D ψ hψ S T _ (e + p.e) hE' f₀ T' hf₀ hvac hT'
  have hsb := GlobalTheory.T.isSchwartzBruhat_tensor_half_add_placeIdempotent D k p S T Y Y' FS FT e horth hstd hstabp Φ hΦSB
  have hmodel := GlobalTheory.T.isLocalModel_tensorWithHalfFunction D k p ψ S T Y Y' FS FT e horth Φ hΦSB.1 f₀ T' hT' hθT' hsb
  have hvacm := GlobalTheory.T.isPlaceModel_tensorIntegralIndicator D k p ψ S T Y Y' FS FT e horth hstd hstabp f₀ T' hT'
    (fun Φ₁ h₁ => GlobalTheory.T.isSchwartzBruhat_tensor_half_add_placeIdempotent D k p S T Y Y' FS FT e horth hstd hstabp Φ₁ h₁ _ (GlobalTheory.T.splitPlaceIntegralMatrixIndicator_mem_schwartzBruhat k Y Y'))
  have hfT : f = T' (p.tensorOne FS FT Φ) := hθ.2 _ hvacm
  have hπe : p.π e = 0 := pi_eq_zero_of p horth
  have hpe2 : p.e * p.e = p.e := p.split.1
  have hid : Φ' = p.tensorAt FS FT Φ Ξk := by
    refine GlobalTheory.T.schwartzBruhat_half_eq_of_eq_on_rational D S T _ (e + p.e) hE' Φ' _ hΦ'SB (hsb Ξk hΞk) fun γ => ?_
    rw [hΦ'rat, hΞ']
    have hd : p.down FS FT (γ.map fun a => (e + p.e) * incA D a) = FT.γ * γ.map p.pr * FS.β := by
      unfold Place.down
      congr 2
      ext i j
      simp only [Matrix.map_apply, map_mul, map_add, hπe, pi_e_self, zero_add, one_mul, Place.pr]
    have hs : (γ.map fun a => (e + p.e) * incA D a) - p.up FS FT (p.down FS FT (γ.map fun a => (e + p.e) * incA D a)) =
        γ.map fun a => e * incA D a := by
      rw [up_down_eq]
      ext i j
      simp only [Matrix.sub_apply, Matrix.map_apply]
      have h2 : p.e * e = 0 := by rw [mul_comm]; exact horth
      linear_combination (-(incA D (γ i j))) * h2 + (-(incA D (γ i j))) * hpe2
    simp only [Place.tensorAt]
    rw [hs, hd, hΦrat]
  have key := hc.2 (T' ∘ₗ p.tensorL FS FT Φ) hmodel ⟨Place.intInd Y Y', GlobalTheory.T.splitPlaceIntegralMatrixIndicator_mem_schwartzBruhat k Y Y'⟩ ⟨Ξk, hΞk⟩ rfl rfl
  rw [hf'T, hid, hfT]
  simpa only [LinearMap.comp_apply, Place.tensorL_apply, Place.tensorOne_apply] using key

end GlobalTheory.LocMod
end
