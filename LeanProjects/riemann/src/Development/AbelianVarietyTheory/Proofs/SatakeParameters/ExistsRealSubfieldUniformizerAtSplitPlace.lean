import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitLocalPlaceDataAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomTrivOutsideLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFacts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceHeckeSatake
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.RealUnifSplit

theorem le_exp_neg_one_of_lt {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add, neg_add_cancel,
    WithZero.exp_zero]
  exact h

theorem val_sq_le {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L)
    (z : 𝓞 L) (hz : z ∈ s.w.asIdeal ^ 2) :
    Valued.v (s.i (z : L)) ≤ WithZero.exp (-2) := by
  rw [pow_two] at hz
  refine Submodule.mul_induction_on hz ?_ ?_
  · intro a ha b hb
    have ha' : Valued.v (s.i (a : L)) < 1 := (s.split_mem_ideal a).1 ha
    have hb' : Valued.v (s.i (b : L)) < 1 := (s.split_mem_ideal b).1 hb
    show Valued.v (s.i ((a : L) * (b : L))) ≤ _
    rw [map_mul, map_mul]
    calc Valued.v (s.i (a : L)) * Valued.v (s.i (b : L))
        ≤ WithZero.exp (-1) * WithZero.exp (-1) :=
          mul_le_mul' (le_exp_neg_one_of_lt ha') (le_exp_neg_one_of_lt hb')
      _ = WithZero.exp (-2) := by rw [← WithZero.exp_add]; norm_num
  · intro a b ha hb
    show Valued.v (s.i ((a : L) + (b : L))) ≤ _
    rw [map_add]
    exact le_trans (Valuation.map_add _ _ _) (max_le ha hb)

end GlobalTheory.RealUnifSplit

theorem GlobalTheory.realUnif_split {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    ∃ y : 𝓞 L, y ∈ s.w.asIdeal ∧ y ∉ s.w.asIdeal ^ 2 ∧ Formalism.AUTREP.IsUnif L s.v (s.i (y : L)) := by
  obtain ⟨π, hπ⟩ := s.v.intValuation_exists_uniformizer
  have hv : Valued.v (s.i ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) π : 𝓞 L) : L)) =
      WithZero.exp (-1) := by
    rw [s.split_val_alg, HeightOneSpectrum.valuation_of_algebraMap, hπ]
  refine ⟨algebraMap _ (𝓞 L) π, ?_, ?_, hv⟩
  · refine (s.split_mem_ideal _).2 ?_
    rw [hv]; rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  · intro h
    have h2 := GlobalTheory.RealUnifSplit.val_sq_le s _ h
    rw [hv] at h2
    have := WithZero.exp_le_exp.1 h2
    omega
