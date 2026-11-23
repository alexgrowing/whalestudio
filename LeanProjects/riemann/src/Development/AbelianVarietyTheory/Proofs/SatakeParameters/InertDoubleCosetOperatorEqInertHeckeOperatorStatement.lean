import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDoubleCosetOperatorEqInertHeckeOperator
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteOfTrivOutside
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertDoubleCosetOperator_eq_inertHeckeOperator : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), (∀ x : GAf L n, Dv.loc x ∈ Formalism.UG.GU Dv.σw n) → (∀ κ : GAf L n, κ ∈ Umax L n → ∀ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n) → (∀ k : GL (Fin n) (w.adicCompletion L), k ∈ Formalism.UG.GU Dv.σw n → ∃ x : GAf L n, TrivOutside {v} x ∧ Dv.loc x = k) → (∀ x y : GAf L n, TrivOutside {v} x → TrivOutside {v} y → Dv.loc x = Dv.loc y → x = y) → ∀ a : GAf L n, TrivOutside {v} a → ∃ (R : Finset (GAf L n)) (ha : Formalism.UG.GU Dv.σw n → ℂ), GlobalTheory.SphLabelOps.Reps (GlobalTheory.InertSph.Kv L n v) a R ∧ ha ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (φ : GAf L n → W), (∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ φ = φ) → ∑ γ ∈ R, NG.rt L n γ φ = heckeFunI L n (Umax L n) Dv ha φ := by
  first | exact @GlobalTheory.InertDCOp.dcOp_eq_heckeFunI | exact GlobalTheory.InertDCOp.dcOp_eq_heckeFunI | (intros; apply GlobalTheory.InertDCOp.dcOp_eq_heckeFunI <;> assumption)
