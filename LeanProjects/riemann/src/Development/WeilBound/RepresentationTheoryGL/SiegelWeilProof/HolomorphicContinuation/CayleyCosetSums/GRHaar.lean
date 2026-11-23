import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.GRH

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem continuous_mR : Continuous (mR : GR n → M2 n) :=
  Units.continuous_val.comp continuous_subtype_val

instance m2LC (n : ℕ) : LocallyCompactSpace (M2 n) :=
  inferInstanceAs (LocallyCompactSpace (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))

instance secondCountableBlockMatrices (n : ℕ) : SecondCountableTopology (M2 n) :=
  inferInstanceAs (SecondCountableTopology (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))

theorem JJ_mul_self : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, neg_zero]
  rw [← fromBlocks_one, fromBlocks_neg, neg_zero]

theorem isClosed_inG : IsClosed {x : M2 n | InG x} :=
  isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const

theorem inv_left {x : M2 n} (hx : InG x) : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
  unfold InG at hx
  have h : JJ n * xᴴ * JJ n * x = JJ n * (xᴴ * JJ n * x) := by
    simp only [Matrix.mul_assoc]
  rw [Matrix.neg_mul, h, hx, JJ_mul_self, neg_neg]

def toSet : GR n ≃ₜ {x : M2 n | InG x} where
  toFun g := ⟨mR g, g.2⟩
  invFun x := ⟨⟨x.1, -(JJ n * x.1ᴴ * JJ n), mul_eq_one_comm.mp (inv_left x.2), inv_left x.2⟩, x.2⟩
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    rfl
  right_inv x := rfl
  continuous_toFun := continuous_mR.subtype_mk _
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    exact ((continuous_const.matrix_mul (continuous_subtype_val.matrix_conjTranspose)).matrix_mul continuous_const).neg

theorem isClosedEmbedding_mR : Topology.IsClosedEmbedding (mR : GR n → M2 n) :=
  (isClosed_inG.isClosedEmbedding_subtypeVal).comp toSet.isClosedEmbedding

theorem isCompact_preimage_mR {C : Set (M2 n)} (hC : IsCompact C) : IsCompact ((mR : GR n → M2 n) ⁻¹' C) :=
  isClosedEmbedding_mR.isCompact_preimage hC

instance : LocallyCompactSpace (GR n) := isClosedEmbedding_mR.locallyCompactSpace

instance : MeasurableSpace (GR n) := borel _

instance : BorelSpace (GR n) := ⟨rfl⟩

instance : SecondCountableTopology (GR n) := isClosedEmbedding_mR.isEmbedding.secondCountableTopology

end PositivityTheory.Rg.Sw.HSt.GRH
