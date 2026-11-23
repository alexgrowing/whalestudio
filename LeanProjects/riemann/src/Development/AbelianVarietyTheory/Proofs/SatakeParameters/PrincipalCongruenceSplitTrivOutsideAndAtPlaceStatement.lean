import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalCongruenceSplitTrivOutsideAndAtPlace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteOfTrivOutside
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruenceElementDecompose
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruence_split_trivOutside_and_at_place : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (N : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (κ : GAf L n), NG.Cong L n N κ → ∃ x y : GAf L n, TrivOutside {v} x ∧ TrivOutside {v}ᶜ y ∧ NG.Cong L n N x ∧ NG.Cong L n N y ∧ κ = x * y := by
  first | exact @GlobalTheory.CongSplitBoth.split_cong_at_place | exact GlobalTheory.CongSplitBoth.split_cong_at_place | (intros; apply GlobalTheory.CongSplitBoth.split_cong_at_place <;> assumption)
