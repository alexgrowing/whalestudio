import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorNefOfDimLeZero
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.AmplePlusNefInductionStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory

theorem isAmpleLB_tens_of_isNef_of_dim_le (k : Type) [Field k] [Infinite k] : ∀ d : ℕ,
    ∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) → topologicalKrullDim Y ≤ (d : ℕ) →
      ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N) := by
  intro d
  induction d with
  | zero => exact isAmpleLB_tens_of_isNef_of_dim_le_zero k
  | succ d ih => exact GlobalTheory.T.ample_plus_nef_induction k d ih

theorem isAmpleLB_of_cls_eq_ample_add_nef : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (A N P : LB X) (hA : IsAmpleLB A) (hN : letI := algebraΓOfHom p; IsNef k N) (hP : P.IsLB), cls P hP = cls A hA.isLB + cls N (letI := algebraΓOfHom p; hN.isLB) → IsAmpleLB P := by
  intro k _ _ X p hp A N P hA hN hP hcls
  letI := algebraΓOfHom p
  have hs : strHom k X = p := strHom_eq fun _ => rfl
  have hp' : IsProjOver (strHom k X) := hs ▸ hp
  obtain ⟨n, i, hi, -⟩ := hp
  have hd : topologicalKrullDim X ≤ (n : ℕ) :=
    i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans
      (ProjSpace.topologicalKrullDim_eq k n).le
  have hT : IsAmpleLB (tens A N) := isAmpleLB_tens_of_isNef_of_dim_le k n X hp' hd A N hA hN
  refine IsAmpleLB.of_lbIso hT hP ((cls_eq_iff hP hT.isLB).1 ?_)
  rw [hcls, cls_tens hA.isLB hN.isLB hT.isLB]

end GlobalTheory
