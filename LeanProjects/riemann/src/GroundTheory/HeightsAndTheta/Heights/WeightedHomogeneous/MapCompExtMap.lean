import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.FunFieldEquivMemChartRingIff
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsChartFormsIffIsFormSystem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n}

theorem map_comp_extMap (D : Heights.AddBlockData P) :
    (MvPolynomial.map (funFieldEquiv P : P.FunField →+* FunField P)).comp D.extMap =
      (mConeMap (AddBlockData.ofObjects D).yPlus).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    refine Eq.trans ?_ (map_intCast (mConeMap (AddBlockData.ofObjects D).yPlus) r).symm
    simp [Heights.AddBlockData.extMap]
  · intro v
    refine Eq.trans ?_ (MvPolynomial.aeval_X (R := ℤ)
      (fun p : Coord D.extSizes ↦ C ((AddBlockData.ofObjects D).yPlus p) * X p.1) v).symm
    rcases v with ⟨_ | k, i⟩
    · simp [Heights.AddBlockData.extMap, Heights.AddBlockData.extVal, AddBlockData.yPlus,
        AddBlockData.ofObjects]
    · simp [Heights.AddBlockData.extMap, Heights.AddBlockData.extVal, AddBlockData.yPlus,
        funFieldEquiv_mkF_X]

theorem ext_ofObjects (D : Heights.AddBlockData P) :
    (AddBlockData.ofObjects D).ext = D.extIdeal := by
  ext f
  show mConeMap (AddBlockData.ofObjects D).yPlus f = 0 ↔ D.extMap f = 0
  have h : MvPolynomial.map (funFieldEquiv P : P.FunField →+* FunField P) (D.extMap f) =
      mConeMap (AddBlockData.ofObjects D).yPlus f :=
    RingHom.congr_fun (map_comp_extMap D) f
  constructor
  · intro h0
    apply MvPolynomial.map_injective _ (funFieldEquiv P).injective
    rw [map_zero]
    exact h.trans h0
  · intro h0
    exact h.symm.trans (by rw [h0, map_zero])

theorem ExtensionDimension.equiv :
    GroundTheory.Heights₂.Heights.ExtensionDimension.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ExtensionDimension.Statement := by
  constructor
  · intro h ι _ _ n P D
    obtain ⟨E, rfl⟩ : ∃ E, AddBlockData.ofObjects E = D :=
      ⟨AddBlockData.toObjects D, AddBlockData.ofObjects_toObjects D⟩
    rw [ext_ofObjects]
    exact h ι n P E
  · intro h ι _ _ n P D
    have := h ι n P (AddBlockData.ofObjects D)
    rw [ext_ofObjects] at this
    exact this

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
