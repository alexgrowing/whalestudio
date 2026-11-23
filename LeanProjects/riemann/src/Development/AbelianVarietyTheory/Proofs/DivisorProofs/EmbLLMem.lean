import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.KerConjMean

variable (D : D7) (δ t0 : ℂ)

abbrev lat : AddSubgroup ℂ := lamOf D D.host.ccK δ

def fld : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range D.what₂.embLL ∪ {g2 (lat D δ), g3 (lat D δ), wpF (lat D δ) t0})

theorem embLL_mem (x : D.what₂.LL) : D.what₂.embLL x ∈ fld D δ t0 :=
  IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨x, rfl⟩)

def ext (σ : D.what₂.LL →+* ℂ) : Set (fld D δ t0 →ₐ[ℚ] ℂ) :=
  {ρ | ∀ x, ρ ⟨D.what₂.embLL x, embLL_mem D δ t0 x⟩ = σ x}

open Classical in

def tc (ρ : fld D δ t0 →ₐ[ℚ] ℂ) : ℂ :=
  if h : ∃ t, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj (fld D δ t0) ρ (lat D δ)) t then h.choose else 0

def hArea (ρ : fld D δ t0 →ₐ[ℚ] ℂ) : ℝ := Real.posLog (area (lamConj (fld D δ t0) ρ (lat D δ)))⁻¹

def hTh (ρ : fld D δ t0 →ₐ[ℚ] ℂ) : ℝ :=
  Real.posLog (nrm1Sq (lamConj (fld D δ t0) ρ (lat D δ)) (GL3Theta.th0 (lamConj (fld D δ t0) ρ (lat D δ)) (tc D δ t0 ρ)))

def avg (σ : D.what₂.LL →+* ℂ) (h : (fld D δ t0 →ₐ[ℚ] ℂ) → ℝ) : ℝ :=
  (∑ᶠ ρ ∈ ext D δ t0 σ, h ρ) / Nat.card (ext D δ t0 σ)

end GlobalTheory.KerConjMean

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat

namespace GlobalTheory.KerConjMean

open GlobalTheory.SumSize GlobalTheory.RowTest GlobalTheory.FunObj GlobalTheory.ChiGrid Formalism.IndefR.Links Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Claims

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C b C1 : ℝ)

def RatTopAt : Prop := ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (j : Fin D.R.m),
  ∃ f : VV D.what₂.LL (wt ch.G (.top j)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.top (j + 1))), ∀ u,
    ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)

def ConjTopAt : Prop := ∃ a0 nD Gd : ℝ, 0 ≤ a0 ∧ 0 ≤ nD ∧ 0 ≤ Gd ∧ 2 * a0 + (nD + Gd) * C1 * Real.log b ≤ aOne ch.G C b ∧
  ∀ Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (j : Fin D.R.m)
    (f : VV D.what₂.LL (wt ch.G (.top j)) →ₗ[D.what₂.LL] VV D.what₂.LL (wt ch.G (.top (j + 1)))),
    (∀ u, ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) (GlobalTheory.CoefModel.mapVV D.what₂.embLL _ u) =
      GlobalTheory.CoefModel.mapVV D.what₂.embLL _ (f u)) →
    ∀ (σ : D.what₂.LL →+* ℂ), ∀ ρ ∈ ext D ch.S.Z.δ ch.S.Z.t0 σ, ∀ u (B : ℝ), nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV σ _ u) ≤ B →
      nrm _ (fun _ => 1) (GlobalTheory.CoefModel.mapVV σ _ (f u)) ≤
        Real.exp (a0 + nD * hArea D ch.S.Z.δ ch.S.Z.t0 ρ + Gd * hTh D ch.S.Z.δ ch.S.Z.t0 ρ) * B

end Claims

end GlobalTheory.KerConjMean

end
