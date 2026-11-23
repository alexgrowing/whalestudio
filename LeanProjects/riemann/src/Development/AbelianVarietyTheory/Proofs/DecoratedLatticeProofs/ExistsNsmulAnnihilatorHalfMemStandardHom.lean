import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAnnihilatorOpenSubgroupInBox
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemStdHom
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

open scoped TensorProduct

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HalfAnnStd

variable {D : D7}

theorem symplO_nsmul_swap (S T : HSp D) (N : ℕ) (x y : WO S T) :
    symplO S T (N • x) y = symplO S T x (N • y) := by
  have h := GlobalTheory.PlaceModel.symplO_smul S T (N : AE D) x y
  rwa [map_natCast, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul] at h

theorem exists_nsmul_frame_mem (S T : HSp D) : ∃ N : ℕ, 0 < N ∧
    ∀ y ∈ latO S T (GlobalTheory.PlaceModel.latFrame S : Set (Fin S.rank → D.host.E))
      (GlobalTheory.PlaceModel.latFrame T : Set (Fin T.rank → D.host.E)) (fun _ => True), N • y ∈ stdHom S T := by
  obtain ⟨M, hM, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame S).1.fg (GlobalTheory.PlaceModel.isSelfDualC_latFrame T).1.fg
  obtain ⟨K, hK, hKm⟩ := GlobalTheory.AdForm.exists_nsmul_mem_stdHom S T
  refine ⟨K * M, Nat.mul_pos hK hM, fun y hy => ?_⟩
  rw [mul_smul]
  refine hKm _ (Matrix.ext fun i j => ?_) fun i j => ?_
  · rw [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul, RingHom.map_mul, GlobalTheory.LatVac.infPart_of_mem hy i j,
      mul_zero, Matrix.zero_apply]
  · rw [Matrix.smul_apply, nsmul_eq_mul, RingHom.map_mul, map_natCast]
    exact hden y hy i j

theorem exists_nsmul_ann_mem_stdHom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∃ N : ℕ, 0 < N ∧ ∀ u : WO S T, IsHalf (cA D E₂) u → (∀ x ∈ stdHom S T, IsHalf E₂ x → ψ (symplO S T x u) = 1) → N • u ∈ stdHom S T := by
  intro D ψ hψ S T Q e he
  obtain ⟨N, hN, hNm⟩ := exists_nsmul_frame_mem S T
  refine ⟨N * N, Nat.mul_pos hN hN, fun u hu hann => ?_⟩
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf := GlobalTheory.AnnihBox.infPart_cA' e (GlobalTheory.PlaceDatum.infPart_idemSum he)
  have hfix : cA D e • u = u := Matrix.ext fun i j => hu i j
  have hall : ∀ x ∈ stdHom S T, ψ (symplO S T x u) = 1 := fun x hx => by
    have h := hann (e • x) (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ e
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hee])) _ hx) fun i j => by
        change e * (e * _) = e * _
        rw [← mul_assoc, hee]
    rwa [GlobalTheory.PlaceModel.symplO_smul, hfix] at h
  rw [mul_smul]
  refine hNm _ (((GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame T)).1 _ (Matrix.ext fun i j => ?_)).2 fun y hy => ?_)
  · rw [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul, RingHom.map_mul, ← hu i j, RingHom.map_mul, hinf, zero_mul,
      mul_zero, Matrix.zero_apply]
  · rw [symplO_nsmul_swap, GlobalTheory.PlaceModel.symplO_skew, AddChar.map_neg_eq_inv, hall _ (hNm y hy), inv_one]

end GlobalTheory.HalfAnnStd

end
