import Formalism.SharpRestriction.CuspSpanNormBounds.UniformConstantsAndStatements
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.LocalFormOfHypotheses

noncomputable section

namespace Formalism.MainNotions.S.MainBoundWithDegrees

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Formalism.MainNotions.UniformConstantsAndStatements ValuativeRel IsDedekindDomain NumberField
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def dStd (D : D7) (u : D.what₂.Word) : ℝ :=
  Formalism.HermitianLatticesTheory.mass (Cnt.stdH D.host.E D.R.k) (Cnt.stdLat D.host.E D.R.k) * gaG D *
    (∏ τ, vand (uS D u τ) / ∏ i ∈ Finset.range D.R.k, (i.factorial : ℝ)) * (Tr D u ^ D.R.k - 1) ^ D.R.f

def DsStd (D : D7) : ℝ :=
  Formalism.HermitianLatticesTheory.mass (Cnt.stdH D.host.E D.R.r) (Cnt.stdLat D.host.E D.R.r) * LocalBesselAndTopKernel.idxRows D * ∏ τ, D.dsig τ

def mainBody (D : D7) (large₂ : SizeData₂ D) (C Ce : ℝ) (dd : D.what₂.Word → ℝ) (Ds : ℝ) : Prop :=
  ∀ u u' : D.what₂.Word,
    ∃ (cInf : ℝ) (constP : HeightOneSpectrum (𝓞 D.host.F) → ℝ)
      (dens : Cnt.GramM D → HeightOneSpectrum (𝓞 D.host.F) → ℝ),
      0 < cInf ∧ (∀ p, 0 < constP p) ∧ Multipliable constP ∧ 0 < ∏' p, constP p ∧
      (∀ Z p, |dens Z p - 1| ≤ C * (Ideal.absNorm p.asIdeal : ℝ) ^ (-((D.R.k : ℝ) - 2 * D.R.rS - 3))) ∧
      (∀ F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
        ∀ what₂ : Finset (Cnt.LatV D), IsRowReps D F0 what₂ →
        ∀ Z : Cnt.GramM D, (∀ τ, 0 < Cnt.Gz D (Tr D u) (Tr D u') Z τ) →
          (∃ Λ ∈ what₂, ∃ F' : Cnt.FlagU D u', IsNormFrame D Λ (lf D F0) F' ∧ Lat.ZhatL (lf D F0) F' = Z) →
          Multipliable (dens Z) ∧
          nuTot D u u' F0 what₂ Z =
            ENNReal.ofReal (cInf * (∏' p, constP p) * (∏' p, dens Z p) *
              ∏ τ, Cnt.Gz D (Tr D u) (Tr D u') Z τ ^ ((D.R.k : ℝ) - 1))) ∧
      ∀ θ : ℝ, 0 < θ → ∀ W : D.what₂.Tau → LocW D.R.k D.R.rS, (∀ τ, GoodW D τ u u' θ (W τ)) →
        ∀ A : ∀ τ, LocS (W τ), (∀ τ, GoodS D (lamD D τ) (A τ)) → (∀ τ, (A τ).deg = D.dsig τ) →
        ∀ μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ,
          (∀ τ, IsSection D.R.k D.R.rS (W τ).z (W τ).z' (μsec τ)) →
          ENNReal.ofReal (gaG D * (cInf * ∏' p, constP p)) * ∏ τ, MMv D u u' (A τ) (μsec τ) ≤
            ENNReal.ofReal (θ ^ (2 * Fintype.card D.what₂.Tau) *
              large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2 * (Fintype.card D.what₂.Tau : ℝ)) *
              ((1 + eSum D Ce) * (dd u * dd u') / Ds))

def MainEstimateWithDegrees (D : D7) (large₂ : SizeData₂ D) (h : LargenessConstants) (C Ce : ℝ) (dd : D.what₂.Word → ℝ) (Ds : ℝ) : Prop :=
  Hyp D large₂ h → mainBody D large₂ C Ce dd Ds

def mainConclStd (D : D7) (large₂ : SizeData₂ D) (C Ce : ℝ) : Prop := mainBody D large₂ C Ce (dStd D) (DsStd D)

def MainT (D : D7) (large₂ : SizeData₂ D) (h : LargenessConstants) (C Ce : ℝ) : Prop :=
  cdScaleTie D → dsigTie D → LocalBesselAndTopKernel.FamilyMidVolume D → MainEstimateWithDegrees D large₂ h C Ce (dStd D) (DsStd D)

section Family

variable {eps : ℝ} (Fm : FamP eps)

def MainTF (g : Given) (C Ce : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => MainT (Fm.D x i) (Fm.L x i) (g.wth C' Cl) C Ce

end Family

def NuTotIndep (D : D7) (u u' : D.what₂.Word) : Prop :=
  ∀ F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
    ∀ what₂ rows' : Finset (Cnt.LatV D), IsRowReps D F0 what₂ → IsRowReps D F0 rows' →
      ∀ Z : Cnt.GramM D, nuTot D u u' F0 what₂ Z = nuTot D u u' F0 rows' Z

end Formalism.MainNotions.S.MainBoundWithDegrees
