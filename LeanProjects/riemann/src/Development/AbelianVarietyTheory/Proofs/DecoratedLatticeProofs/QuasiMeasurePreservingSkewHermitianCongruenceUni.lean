import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructureStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.SkewConjQmp

theorem skewConj_matMul {D : D7} {ρ : ℕ} (a b : Mx D ρ ρ) (c : skewA D ρ) :
    skewConj (a ⬝ b) c = skewConj a (skewConj b c) := by
  apply Subtype.ext
  simp only [skewConj, adj_mul, Matrix.mul_assoc]

theorem skewConj_matOne {D : D7} {ρ : ℕ} (c : skewA D ρ) : skewConj (1 : Mx D ρ ρ) c = c := by
  apply Subtype.ext
  simp only [skewConj, adj_one, Matrix.one_mul, Matrix.mul_one]

theorem skewConj_addArg {D : D7} {ρ : ℕ} (a : Mx D ρ ρ) (c d : skewA D ρ) :
    skewConj a (c + d) = skewConj a c + skewConj a d := by
  apply Subtype.ext
  simp only [skewConj, AddSubgroup.coe_add, Matrix.mul_add, Matrix.add_mul]

theorem continuous_skewConj_arg {D : D7} {ρ : ℕ} (a : Mx D ρ ρ) : Continuous (skewConj a : skewA D ρ → skewA D ρ) := by
  have h1 : Continuous fun c : skewA D ρ => (a ⬝ c.1 : Mx D ρ ρ) := continuous_const.matrix_mul continuous_subtype_val
  have h2 : Continuous fun c : skewA D ρ => (a ⬝ c.1 ⬝ adj a : Mx D ρ ρ) := h1.matrix_mul continuous_const
  exact Continuous.subtype_mk h2 _

noncomputable def skewConjEquiv {D : D7} {ρ : ℕ} (g : GL (Fin ρ) (AE D)) : skewA D ρ ≃+ skewA D ρ where
  toFun := skewConj g.val
  invFun := skewConj (g⁻¹).val
  left_inv c := by
    rw [← skewConj_matMul]
    have : (g⁻¹).val ⬝ g.val = 1 := Units.inv_mul g
    rw [this, skewConj_matOne]
  right_inv c := by
    rw [← skewConj_matMul]
    have : g.val ⬝ (g⁻¹).val = 1 := Units.mul_inv g
    rw [this, skewConj_matOne]
  map_add' := skewConj_addArg _

set_option synthInstance.maxHeartbeats 200000 in

theorem quasiMeasurePreserving_skewConj : ∀ (D : D7) (ρ : ℕ) (lC : Measure (skewA D ρ)), lC.IsAddHaarMeasure →
    ∀ u : UX D ρ, Measure.QuasiMeasurePreserving (skewConj u.1.1) lC lC := by
  intro D ρ lC hC u
  obtain ⟨a1, a2, a3, a4, -⟩ := lattice_Mx D ρ ρ
  have : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  have : BorelSpace (skewA D ρ) := Subtype.borelSpace _
  have hcl : IsClosed (skewA D ρ : Set (Mx D ρ ρ)) := isClosed_eq continuous_adj continuous_neg
  have : LocallyCompactSpace (skewA D ρ) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : IsTopologicalAddGroup (skewA D ρ) := inferInstance
  have : SecondCountableTopology (skewA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  have hc := continuous_skewConj_arg (u.1.1 : Mx D ρ ρ)
  have hH : (lC.map (skewConj u.1.1)).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map lC (skewConjEquiv u.1) hc
      (continuous_skewConj_arg (u.1⁻¹).val)
  refine ⟨hc.measurable, ?_⟩
  exact Measure.absolutelyContinuous_isAddHaarMeasure _ _

end GlobalTheory.Unf.SkewConjQmp
