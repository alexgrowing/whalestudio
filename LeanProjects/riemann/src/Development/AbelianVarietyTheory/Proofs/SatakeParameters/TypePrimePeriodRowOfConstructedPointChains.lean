import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSaj
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetTableBoundConstantOneOfChainAgreementStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDegreesSmallAgainstTypePrimesStatement

noncomputable section

namespace GlobalTheory.AtG

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc GlobalTheory.Mem.Top GlobalTheory.AtG

theorem row_atG_of_jetSplitAmb : JetSplitAmb → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd),
    RowE Q Lk (fun _ D O _ _ => ∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → TiesAt D O.ex.errX O.X μ) →
    Row Q Lk fun 𝒜 _ => Closed (W3 𝒜) fun Fm _ => ∃ C1, (∃ x0, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i,
      Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX C1) ∧ WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1 := by
  intro hJ Bd Q Lk hE
  refine ⟨_, hE, fun 𝒜 σ s => ?_⟩
  refine ⟨1 / 100, by norm_num, fun eps he hle => ?_⟩
  obtain ⟨xs, hxs⟩ := GlobalTheory.T.kernelDegrees_small_against_typePrimes eps he (by linarith)
  refine ⟨⟨0, fun _ => 0, fun _ => 2, fun _ => 0⟩, fun Fm CH hc hL => ?_⟩
  have hg : (2 : ℝ) ≤ Fm.cX.err.g := hL.2.2.1 Fm.cX.err.g (by simp [FamP.cMid])
  obtain ⟨κ, -, -, t⟩ := s Fm (w3_a hc)
  refine ⟨1, ⟨xs, fun x hx hx0 i => ?_⟩, Formalism.MainNotions.J.family_type_prime_loss Fm zero_le_one (by linarith)⟩
  refine GlobalTheory.T.propositionCOneUsedTuples_one_of_tiesAt_sizeAt hJ (Fm.D x i) (Fm.L x i) (Fm.ex x hx i).errX (Fm.X x i) (t x hx i).2 ?_
  exact hxs (Fm.D x i) (Fm.L x i) (Fm.params x hx i) (Fm.sizes x hx i) (Fm.L_eps x i) (by rw [Fm.L_x x i hx]; exact hx0)

end GlobalTheory.AtG

end
