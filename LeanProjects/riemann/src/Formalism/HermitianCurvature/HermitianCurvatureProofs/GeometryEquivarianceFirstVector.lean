import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomCut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.HermBvecEI
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.AdjugateLastEntrySum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.FixOfPos

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.QuantumDeterminants PI.UnitaryGroupMassFormula.GsFr
open scoped Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace S2

variable {k r : ℕ}

private theorem herm_hpk_mulVec_of_mem_uh {h : B.Mat k r} (hh : h ∈ UH (Hpk k r)) (v w : Fin (2 * r + k + 1) → ℂ) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ w) = Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v w := by
  have hh' : hᴴ * Formalism.QuantumDeterminants.Hpk k r * h = Formalism.QuantumDeterminants.Hpk k r := hh
  show star (h *ᵥ w) ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ (h *ᵥ v)) = star w ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ v)
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hh']

lemma unitH_UH {h : B.Mat k r} (hh : h ∈ UH (Hpk k r)) (v : Fin (2 * r + k + 1) → ℂ) :
    unitH k r (h *ᵥ v) = h *ᵥ unitH k r v := by
  show ((((Real.sqrt (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ v)).re)⁻¹ : ℝ) : ℂ) • (h *ᵥ v)) =
    h *ᵥ ((((Real.sqrt (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v v).re)⁻¹ : ℝ) : ℂ) • v)
  rw [herm_hpk_mulVec_of_mem_uh hh, Matrix.mulVec_smul]

lemma omW_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {n n' : B.Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (g : B.Mat k r) :
    omW k r z z' (n * g * n') = omW k r z z' g := by
  show prW k r z (xcof k r z z' (n * g * n')) = prW k r z (xcof k r z z' g)
  rw [xcof_N hz hz' hn hn' g]
  exact prW_N hn (fun a => xcof_esI z z' g a)

lemma omW'_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {n n' : B.Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    omW' k r z z' (n * g * n') = omW' k r z z' g := by
  have hh : nᴴ * Hpk k r * n = Hpk k r := hn.1
  have hleft : (Hpk k r * nᴴ * Hpk k r) * n = 1 := by
    calc (Hpk k r * nᴴ * Hpk k r) * n = Hpk k r * (nᴴ * Hpk k r * n) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hh, WeylGroupFacts.hpk_sq]
  have hnn : n⁻¹ * n = 1 := by
    rw [Matrix.inv_eq_left_inv hleft]
    exact hleft
  show prW k r z' ((n * g * n')⁻¹ *ᵥ xcofL k r z z' (n * g * n')) = prW k r z' (g⁻¹ *ᵥ xcofL k r z z' g)
  rw [xcofL_N hz hz' hn hn' g, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, Matrix.mul_assoc, hnn, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  exact prW_N (WeylGroupFacts.mem_n_inv hn') (fun a => ginv_xcofL_esI z z' hg a)

end S2

open S2 in
theorem geometry_equivariance_first_vector : GeomEqvNu := by
  intro k r z z' _ hz hz' h hh n hn h' hh' n' hn' g hg
  have hy : h⁻¹ * n⁻¹ * g * n' * h' = h⁻¹ * (n⁻¹ * g * n') * h' := by simp only [Matrix.mul_assoc]
  have hhi := WeylGroupFacts.uw_inv hh
  have hhi' := WeylGroupFacts.uw_inv hh'
  have hni := WeylGroupFacts.mem_n_inv hn
  have hu : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv h (RankOneEmbeddings.In.uw_unit hh)
  have hu' : h' * h'⁻¹ = 1 := Matrix.mul_nonsing_inv h' (RankOneEmbeddings.In.uw_unit hh')
  constructor
  · show unitH k r (omW k r z z' g) = h *ᵥ unitH k r (omW k r z z' (h⁻¹ * n⁻¹ * g * n' * h'))
    rw [hy, omW_UW hz hhi hh', omW_N hz hz' hni hn', unitH_UH hhi.1, Matrix.mulVec_mulVec, hu,
      Matrix.one_mulVec]
  · show unitH k r (omW' k r z z' g) = h' *ᵥ unitH k r (omW' k r z z' (h⁻¹ * n⁻¹ * g * n' * h'))
    rw [hy, omW'_UW hz hz' hhi hh', omW'_N hz hz' hni hn' hg.1, unitH_UH hhi'.1, Matrix.mulVec_mulVec,
      hu', Matrix.one_mulVec]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
