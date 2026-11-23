import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumVolShellInterTranslate

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.shellSum_eq_const_of_twist_eq_indicator_double_coset :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ →
        ∀ (a : ℕ) (ν : kˣ →* ℂˣ) (z C : ℂ) (φ : Matrix (Fin a) (Fin a) k → ℂ) (g₀ g₁ : GL (Fin a) k),
        (∀ g : GL (Fin a) k, φ g.1 * (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) z =
          {g : GL (Fin a) k | g₀ * g * g₁ ∈ GlobalTheory.SplitWeil.KO k (Fin a)}.indicator (fun _ => C) g) →
        GlobalTheory.SplitFlip.shellSum (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ ν z φ = C := by
  intro k _ _ _ _ _ _ ϖ hϖ a ν z C φ g₀ g₁ hφ
  letI : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
  haveI : BorelSpace (GL (Fin a) k) := GlobalTheory.SplitFlip.borel_GL
  have hSm : MeasurableSet {g : GL (Fin a) k | g₀ * g * g₁ ∈ GlobalTheory.SplitWeil.KO k (Fin a)} :=
    (GlobalTheory.PureMatch.ShellVolume.isOpen_translate g₀ g₁).measurableSet
  have hvol := GlobalTheory.PureMatch.ShellVolume.finsum_vol_shell_inter_translate k a ϖ g₀ g₁ hϖ
  have hshell : ∀ m : {m : Fin a → ℤ // Antitone m},
      GlobalTheory.SplitFlip.shell (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ ν z φ m.1 =
      (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))).real (GlobalTheory.SplitFlip.shellSet ϖ m.1 ∩
        {g : GL (Fin a) k | g₀ * g * g₁ ∈ GlobalTheory.SplitWeil.KO k (Fin a)}) • C := by
    intro m
    rw [GlobalTheory.SplitFlip.shell]
    simp_rw [hφ]
    have e1 := MeasureTheory.setIntegral_indicator (μ := GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a)))
      (s := GlobalTheory.SplitFlip.shellSet ϖ m.1) (f := fun _ => C) hSm
    rw [e1, MeasureTheory.setIntegral_const]
  rw [GlobalTheory.SplitFlip.shellSum]
  simp_rw [hshell]
  rw [← finsum_smul, hvol, one_smul]
