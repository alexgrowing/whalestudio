import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GrowthOfBasic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondDerivativeHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermExpansionMatrixFunction
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.TheoremS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pbApplied : ∀ C₄ Cthr : ℝ, 1 ≤ C₄ →
    ∃ CA C : ℝ, Cthr ≤ CA ∧ 1 ≤ CA ∧ 0 ≤ C ∧ C ≤ CA ∧
    ∀ (C0 CG CDel cT Cb : ℝ), 1 ≤ C0 → 0 ≤ CG → 4 < CDel → 0 < cT → 0 < Cb → 1 < cT * Cb →
    ∃ k0 : ℕ, ∀ (E W : Type) [Field E] [NumberField E] [IsCMField E] (D : TB.Data E W)
      (e : Fin D.f ≃ InfinitePlace E) (G : Sz.Glob (InfinitePlace E)) (bb Cp Cf Th : ℝ)
      (de de' : ℕ → ℝ) (T T' : ℕ) (du du' : ℝ) (l : ℕ),
      k0 ≤ G.k → J.SzHyp G CA C0 CG CDel cT Cb bb Cp Th de de' T T' du du' l →
      16 ≤ Sz.cExp CDel cT Cb * Cf → Cf * Real.log bb ≤ G.f * Real.log G.k →
      S6.Unram E → J.Inst D e G CA de de' T T' l → PB.LocalModel D →
      ∀ (jn : ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (Vt : TB.Pt E → H) (c : ℕ → TB.Pt E → ℂ) (sd : ℝ),
        PB.RealInputs D C₄ jn Vt → PB.DensInput G.k G.r G.f sd →
        ∀ (P : Type) [Fintype P] (B : S3.MassData P), PB.RowsInput D sd Vt c B → PB.MassDataHyp B →
          PB.EnergyLink B jn sd C Th D.r D.f →
          ∀ (τ Rw I HS H₁ : Type) [Fintype I] [NormedAddCommGroup HS] [InnerProductSpace ℂ HS]
            [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
            (X : PB.Terms τ Rw I HS H₁) (c5 Cn : ℝ),
            PB.Link X B G de T du du' → PB.SplitInputs X B.tt →
            PB.SizeNumbers G.k G.r G.f bb G.g1 G.g2 c5 Cn →
            X.RowBig (Real.exp (-(c5 * G.k * G.f * Real.log G.k))) (du * du' / (G.size de T du).Dstar) →
            X.RowNotScalar (Real.exp (-(c5 * G.k * G.f * Real.log G.k)))
              (du * du' / (G.size de T du).Dstar) →
            X.RowNG (((2 : ℝ) ^ (G.k - 2 * G.r - 5))⁻¹ *
              Real.exp (Cn * ((2 * G.r + 2 : ℕ) : ℝ) ^ 5 * G.f * Real.log bb))
              (du * du' / (G.size de T du).Dstar) →
            ‖X.K0‖ ^ 2 ≤ (1 + (bb ^ 6)⁻¹) * (du * du' / (G.size de T du).Dstar) := by
  open Formalism.FourierDecayAlt.P.GrowthPolynomialOperator in
  exact t_PairBoundFromLocal t_MainRow t_PairBound Formalism.FourierDecayAlt.P.HilbertSchmidtNorm.localCores
    Formalism.FourierDecayAlt.P.HilbertSchmidtNorm.globalCores t_LatticeLink t_AxiomsOfLocalModel Formalism.FourierDecayAlt.P.lattice_average_induction
    t_PairBoundAbstract t_PriceOfIota t_EqualIota t_PairSplit t_SubFamily t_NumPrice t_NumExp
    t_NumDens t_NumLoops t_NumNG t_NGExponent t_EtaZero

end Formalism.L2.SG.TheoremS
