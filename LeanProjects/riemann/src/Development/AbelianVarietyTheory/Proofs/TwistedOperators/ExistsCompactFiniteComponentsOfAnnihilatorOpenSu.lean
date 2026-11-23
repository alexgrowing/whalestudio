import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharAnnihilatorOpenSubgroupFinPartCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAnnihilatorOpenSubgroupInBox
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaMatrixCoeffRapidDecayRealFunctional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergVacuumCommutantPreservesLatticeVacua
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.MixModel GlobalTheory.Unf
noncomputable section

namespace GlobalTheory.AnnihMat

variable {D : D7}

theorem hO_single (S T : HSp D) (w : WO S T) (i : Fin T.rank) (j : Fin S.rank) (e : AE D) :
    hO S T w (Matrix.single i j (cA D e)) = e * (gA T ⬝ w ⬝ giA S) i j := by
  have ha : adj (Matrix.single i j (cA D e)) = Matrix.single j i e := by
    ext a b
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.single_apply]
    by_cases h1 : i = b <;> by_cases h2 : j = a <;> simp [h1, h2, GlobalTheory.DualPairCheck.cA_cA]
  rw [hO_eq_trace, ha, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.trace_single_mul, smul_eq_mul]

end GlobalTheory.AnnihMat

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
open GlobalTheory.AnnihMat GlobalTheory.AnnihBox in

theorem GlobalTheory.AnnihMat.annihilator_inBox_full : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (U : AddSubgroup (WO S T)), IsOpen (U : Set (WO S T)) → ∃ Q : Set (WO S T), IsCompact Q ∧ ∀ w : WO S T, (∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO S T w u) = 1) → GlobalTheory.Unf.InBox Q w := by
  intro D ψ hψ S T U hU
  let g : Fin T.rank → Fin S.rank → (AE D →+ WO S T) := fun i j =>
    { toFun := fun c => Matrix.single i j (cA D c)
      map_zero' := by simp
      map_add' := fun a b => by simp [Matrix.single_add] }
  have hg : ∀ i j, Continuous (g i j) := fun i j => by
    show Continuous fun c => Matrix.single i j (cA D c)
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.single_apply]
    split_ifs
    · exact continuous_cA'
    · exact continuous_const
  have hK := fun i j => GlobalTheory.CondBound.annihilator_finPart_compact D ψ hψ (U.comap (g i j)) (hU.preimage (hg i j))
  choose K hKc hK using hK
  let R : WO S T → WO S T := fun k => giA T ⬝ k.map (fun z => incA D D.host.xi0⁻¹ * z) ⬝ gA S
  have hR : Continuous R :=
    (continuous_const.matrix_mul (continuous_id.matrix_map (continuous_const.mul continuous_id))).matrix_mul
      continuous_const
  refine ⟨R '' (Set.univ.pi fun i => Set.univ.pi fun j => K i j : Set (WO S T)),
    (isCompact_univ_pi fun i => isCompact_univ_pi fun j => hKc i j).image hR, ?_⟩
  intro w hw
  have hy : ∀ i j, ∃ k ∈ K i j, finPart D (incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j - k) = 0 := fun i j =>
    hK i j _ fun c hc hc0 => by
      have h1 : (Matrix.single i j (cA D c)).map (infPart D) = 0 := by
        ext a b
        simp only [Matrix.map_apply, Matrix.single_apply, Matrix.zero_apply]
        split_ifs
        · exact infPart_cA' c hc0
        · exact map_zero _
      have h2 := hw (Matrix.single i j (cA D c)) hc h1
      have e3 : incA D D.host.xi0 * hO S T w (Matrix.single i j (cA D c)) =
          incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j * c := by rw [hO_single]; ring
      unfold symplO at h2
      rwa [e3] at h2
  choose k hk hk0 using hy
  refine ⟨R (Matrix.of k), ⟨Matrix.of k, fun i _ j _ => hk i j, rfl⟩, ?_⟩
  have hsub : ∀ a b : WO S T, R (a - b) = R a - R b := fun a b => by
    simp only [R]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    congr 2
    ext i j
    simp [mul_sub]
  have hx' : R (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j) = w := by
    simp only [R]
    have e : (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j).map
        (fun z => incA D D.host.xi0⁻¹ * z) = gA T ⬝ w ⬝ giA S := by
      ext i j
      simp only [Matrix.map_apply, Matrix.of_apply]
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), RingHom.map_one, one_mul]
    rw [e]
    simp only [Matrix.mul_assoc, giA_mul_gA, Matrix.mul_one, giA_gA_cancel]
  have e : w - R (Matrix.of k) = R (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j - k i j) := by
    have hm : (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j - k i j) =
        (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j) - Matrix.of k := Matrix.ext fun _ _ => rfl
    rw [hm, hsub, hx']
  have h0 := map_finPart_mul_map (giA T) (incA D D.host.xi0⁻¹)
    (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ w ⬝ giA S) i j - k i j) fun i j => hk0 i j
  rw [e]
  simp only [R]
  rw [Matrix.map_mul, h0, Matrix.zero_mul]
