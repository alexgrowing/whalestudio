import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitLiftOfLiftParam

noncomputable section

namespace GlobalTheory.RowCuspPar

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings

variable (D : D7)

def blockPart (μ : D.naut.CG 1) : Part D.naut.CG := ⟨1, μ, D.R.t⟩

def liftLoc (μ : D.naut.CG 1) (w : PlE D.host) (a : D.naut.LP w) : D.naut.LP w :=
  D.naut.lpChar (D.naut.lpSum a (spehLoc D.nd D.naut (blockPart D μ) w)) (D.naut.locG D.naut.etaTinv w)

def eOf {R : Ranks} (P : HCParam R) (j : ℕ) : ℚ := if h : j - 1 < R.m then P.e ⟨j - 1, h⟩ else 0

def runE (R : Ranks) (e : ℚ) : Multiset ℂ :=
  (Multiset.range R.t).map fun k : ℕ => -(e : ℂ) + ((R.t : ℂ) - 1) / 2 - (k : ℂ)

def IsThetaLift (S : GlobalTheory.HeightCounting.RowSide D) (μ : D.naut.CG 1) (j : ℕ) (σ : D.what₂.FT) (P : D.nbc.AU j) : Prop :=
  (∀ w, IsSplitPl D.host w → D.nbc.locAU j P w = liftLoc D μ w (S.locR σ w)) ∧
  (∀ w, ¬ IsSplitPl D.host w → D.nbc.sphAU j P w) ∧
  ∀ τ : D.what₂.Tau,
    D.nbc.infW j (D.nbc.wtAU j P) (embTau D τ) =
        (hcSigma (D.hc τ) + runE D.R (eOf (D.hc τ) j)).map (fun z => z - 1 / 2) ∧
    D.nbc.infW j (D.nbc.wtAU j P) (embTauBar D τ) =
        (hcSigma (D.hc τ) + runE D.R (eOf (D.hc τ) j)).map (fun z => -(z - 1 / 2))

def ThetaLiftRow (S : GlobalTheory.HeightCounting.RowSide D) (μ : ℕ → D.naut.CG 1) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ σ : D.what₂.FT, D.what₂.isot j σ ≠ ⊥ → ∃ P : D.nbc.AU j, IsThetaLift D S (μ j) j σ P

def IsBCU (j : ℕ) (P : D.nbc.AU j) (Pa : List (Part D.naut.CG)) : Prop :=
  (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π) ∧
  (Pa.map fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)).Nodup ∧
  rankIso D.nd D.naut Pa = D.R.nV ∧
  (∀ w, IsSplitPl D.host w → isoLoc D.nd D.naut Pa w = D.nbc.locAU j P w) ∧
  (∀ w, ¬ IsSplitPl D.host w → D.naut.unr (isoLoc D.nd D.naut Pa w) ∧
    D.naut.frobEig (isoLoc D.nd D.naut Pa w) = ubc D.R.nV (D.nbc.satAU j P w)) ∧
  ∀ τ, isoInf D.nd D.naut Pa τ = D.nbc.infW j (D.nbc.wtAU j P) τ

def BaseChangeU : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ P : D.nbc.AU j, (∀ w, ¬ IsSplitPl D.host w → D.nbc.sphAU j P w) →
    ∃ Pa, IsBCU D j P Pa

def BcPartsTempered : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ (P : D.nbc.AU j) (Pa : List (Part D.naut.CG)), IsBCU D j P Pa →
    ∀ p ∈ Pa, ∀ w, IsSplitPl D.host w → D.naut.unr (D.naut.locG p.π w) → D.naut.tempered (D.naut.locG p.π w)

def RowSizeR (S : GlobalTheory.HeightCounting.RowSide D) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ σ : D.what₂.FT, D.what₂.isot j σ ≠ ⊥ → ∀ w, IsSplitPl D.host w →
    D.naut.unr (S.locR σ w) → ∀ α ∈ D.naut.frobEig (S.locR σ w),
      ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((D.R.r : ℝ) - 1) / 2)

def RowUnrR (S : GlobalTheory.HeightCounting.RowSide D) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ σ : D.what₂.FT, D.what₂.isot j σ ≠ ⊥ → ∀ w, IsSplitPl D.host w →
    (∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k)) → D.naut.unr (S.locR σ w)

def CharFacts (μ : ℕ → D.naut.CG 1) : Prop :=
  D.naut.csd D.naut.etaT ∧
  (∀ j τ, D.naut.infG (μ j) (embTau D τ) = {-((eOf (D.hc τ) j : ℚ) : ℂ)} ∧
    D.naut.infG (μ j) (embTauBar D τ) = {((eOf (D.hc τ) j : ℚ) : ℂ)}) ∧
  (∀ τ, D.naut.infG D.naut.etaT (embTau D τ) = {1 / 2} ∧ D.naut.infG D.naut.etaT (embTauBar D τ) = {-1 / 2} ∧
    D.naut.infG D.naut.etaTinv (embTau D τ) = {-1 / 2} ∧ D.naut.infG D.naut.etaTinv (embTauBar D τ) = {1 / 2}) ∧
  (∀ j w, IsSplitPl D.host w → D.naut.unr (D.naut.locG (μ j) w) → D.naut.tempered (D.naut.locG (μ j) w)) ∧
  (∀ w, IsSplitPl D.host w → D.naut.tempered (D.naut.locG D.naut.etaTinv w)) ∧
  ∀ w (a : D.naut.LP w), D.naut.lpChar (D.naut.lpChar a (D.naut.locG D.naut.etaTinv w)) (D.naut.locG D.naut.etaT w) = a

section Iso
variable {D}
open GlobalTheory.HeightCounting

theorem isoLoc_perm {Pa Pb : List (Part D.naut.CG)} (h : Pa.Perm Pb) (w : PlE D.host) :
    isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pb w := by
  unfold isoLoc
  induction h with
  | nil => rfl
  | cons p _ ih => simp only [List.foldr_cons, ih]
  | swap p q l =>
    simp only [List.foldr_cons]
    rw [← D.naut.lpSum_assoc, D.naut.lpSum_comm (spehLoc D.nd D.naut q w), D.naut.lpSum_assoc]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem isoLoc_single (p : Part D.naut.CG) (hd : p.d = 1) (w : PlE D.host) :
    isoLoc D.nd D.naut [p] w = D.naut.locG p.π w := by
  obtain ⟨a, π, d⟩ := p
  simp only at hd
  subst hd
  simp [isoLoc, spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]

end Iso
end GlobalTheory.RowCuspPar
end
