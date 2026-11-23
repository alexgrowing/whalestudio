import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriTrivialCase.IwahoriTrivialLemmas.UnitProductIndicatorTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedQuadraticDatumAtInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedQuadraticDatumAtInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStableTwistedOrbitalUnitEqLatticeSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralUnitGLEqHermitianLatticeCo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertOrbitalIntegralUnitEqLatticeCount
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLatticeIsLatticeSelfDualHermitianModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryCentralizerEquivNormOneTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexEqOfMulEquivSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLatticeStableIffConjIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralIndicatorEqFinsumRelIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLatticeEqIffInvMulIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeStandardHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerEqMapNormOneTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactClosureZpowersLeftMulGLIffIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpannedByGLColumnsEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLLatticeSpannedByGLColumnsEqFullLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjugacyClassesEquivUnitsModNormsNonspli
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraceFormOfTwistedNormCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStableTwistedOrbitalUnitEqLatticeSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaUnramifiedProductUnitaryGroupsStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

theorem PositivityTheory.Rg.Bc.ArchbcB.B.archimedean_base_change_first : PositivityTheory.Rg.Bc.ArchbcB.B.M1 := by
  intro E _ _ _ hE w hw n a b hab Q₁ Q₂ hm₁ hm₂ hd₁ hd₂ hsep hc₁ hc₂
  obtain ⟨K, e, he1, he2, he3, he4⟩ := GlobalTheory.T.exists_unramifiedQuadraticDatum_at_inertPlace E hE w hw
  have hs₁ : Q₁.Separable := hsep.of_mul_left
  have hs₂ : Q₂.Separable := hsep.of_mul_right
  obtain ⟨B₁, hg₁, hP₁, hst₁⟩ := GlobalTheory.T.inertPlace_stableTwistedOrbital_unit_eq_latticeSum E hE w hw K e he1 he2 he3 he4 a Q₁ hm₁ hd₁ hs₁ hc₁
  obtain ⟨B₂, hg₂, hP₂, hst₂⟩ := GlobalTheory.T.inertPlace_stableTwistedOrbital_unit_eq_latticeSum E hE w hw K e he1 he2 he3 he4 b Q₂ hm₂ hd₂ hs₂ hc₂
  have hk := GlobalTheory.T.inertPlace_kappaOrbital_unit_eq_signedLatticeSum E hE w hw K e he1 he2 he3 he4 n Q₁ Q₂ hm₁ hm₂ (by omega) hsep hc₁ hc₂ B₁ B₂ hg₁ hg₂ hP₁ hP₂
  have hsepP : (B₁.P * B₂.P).Separable := by
    rw [hP₁, hP₂, ← Polynomial.map_mul]
    exact hsep.map
  have hid := GlobalTheory.T.unitLemma_unramified_product_unitary_groups K B₁ B₂ hg₁ hg₂ hsepP
  unfold GlobalTheory.UnitLemma.InvAlg.Identity at hid
  have hv : GlobalTheory.UnitLemma.val K.O (resultant B₁.P B₂.P) = ordL (resultant Q₁ Q₂) := by
    rw [he3, hP₁, hP₂]
    have h1 : (Q₁.map e.symm.toRingHom).natDegree = Q₁.natDegree :=
      Polynomial.natDegree_map_eq_of_injective e.symm.injective _
    have h2 : (Q₂.map e.symm.toRingHom).natDegree = Q₂.natDegree :=
      Polynomial.natDegree_map_eq_of_injective e.symm.injective _
    rw [h1, h2, Polynomial.resultant_map_map]
    simp
  rw [PositivityTheory.BcbA.Ties.unit_product_indicator_twist E hE a b w hw Q₁ Q₂ hs₁ hs₂, hst₁, hst₂, hk, ← Rat.cast_mul, ← hid, Rat.cast_mul]
  congr 1
  rw [hv]
  unfold delta absHalf
  rw [if_neg hw, he4]
  set v := ordL (resultant Q₁ Q₂)
  have hq : Real.sqrt (((K.q ^ 2 : ℕ) : ℝ) ^ (-v)) = (K.q : ℝ) ^ (-v) := by
    rw [Nat.cast_pow, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast]
    exact Real.sqrt_sq (zpow_nonneg (Nat.cast_nonneg _) _)
  rw [hq]
  push_cast
  rw [neg_eq_neg_one_mul, mul_zpow, ← _root_.inv_zpow', inv_neg_one]

theorem PositivityTheory.Rg.Bc.ArchbcB.B.m1 : PositivityTheory.Rg.Bc.ArchbcB.B.M1 :=
  PositivityTheory.Rg.Bc.ArchbcB.B.archimedean_base_change_first
