import Mathlib
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.BottomMinor
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.EulerProductSatake

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory NumberField IsDedekindDomain
open Formalism.MainNotions.SchurIrreducible (IrrGK)
open GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts (delta wtK wtExt wtH IsLowestType IsKIntw)
open GlobalTheory.IndefiniteRowSideFullHecke.EulerProductLocalFactors (Place eulerProd dPart quadSign SatakeBound)
open scoped TensorProduct

namespace GlobalTheory.BlockSizes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def coverMap {p q : ℕ} (T : GrpData p q) (x : T.G) : UpqT p q := (⟨T.cov x, T.cov_mem x⟩ : Formalism.UG.Upq p q)

def IsStdHaar {p q : ℕ} (T : GrpData p q) : Prop :=
  Formalism.IndefR.Lev.IsMinf (Measure.map (coverMap T) T.haar)

def degOf {p q : ℕ} (ap : Fin p → ℕ) (am : Fin q → ℕ) : ℕ := ∑ i, ap i + ∑ i, am i

def IsRealFactor {p q n : ℕ} (hn : p + q < n) (ap : Fin p → ℕ) (am : Fin q → ℕ) (z : ℝ) : Prop :=
  ∃ (T0 : GrpData (p * n + q * 0) (p * 0 + q * n)) (T1 : GrpData p q) (T2 : GrpData n 0) (F : FockData T0 T1 T2)
    (D : DSRep T1) (W : Submodule ℂ D.HK.V) (M : GKMod n 0) (e0 : W) (v0 : M.V)
    (io : W ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0),
    IsStdHaar T1 ∧ IsLowestType D.HK (wtK n ap am) W ∧ (e0 : D.HK.V) ∈ wtSub D.HK.act (wtExt n ap am) ∧
    IrrGK M ∧ IsHW M.act (wtH n ap am) v0 ∧ IsKIntw F D.HK W M io ∧ io (e0 ⊗ₜ v0) = delta hn ap am ∧
    z = ‖F.ι (delta hn ap am)‖ ^ 2 * Module.finrank ℂ M.V * Module.finrank ℂ W / D.fdeg

def FormalDegreeUpper : Prop :=
  ∀ (p q n : ℕ), 1 ≤ p + q → p + q < n → ∀ (ap : Fin p → ℕ) (am : Fin q → ℕ), Antitone ap → Antitone am →
    (∀ i, 1 ≤ ap i) → (∀ i, 1 ≤ am i) → ∀ (T : GrpData p q) (D : DSRep T) (W : Submodule ℂ D.HK.V),
    IsStdHaar T → IsLowestType D.HK (wtK n ap am) W →
    Real.log D.fdeg ≤ 2 + ((p + q : ℕ) : ℝ) ^ 2 *
      Real.log (2 * Real.sqrt 2 * ((p + q : ℕ) : ℝ) ^ 2 * n * ((degOf ap am : ℝ) + 2))

def FormalDegreeLower : Prop :=
  ∀ (p q n : ℕ), 1 ≤ p + q → p + q < n → ∀ (ap : Fin p → ℕ) (am : Fin q → ℕ), Antitone ap → Antitone am →
    (∀ i, 1 ≤ ap i) → (∀ i, 1 ≤ am i) → ∀ (T : GrpData p q) (D : DSRep T) (W : Submodule ℂ D.HK.V),
    IsStdHaar T → IsLowestType D.HK (wtK n ap am) W →
    -Real.log D.fdeg ≤ 3 * ((p + q : ℕ) : ℝ) ^ 2 * Real.log (((p + q : ℕ) : ℝ) + 2)

def rowsP (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : Fin (D.R.sigW j).1) : ℕ := ⌊DV.aPlusQ D j τ i⌋₊

def rowsM (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : Fin (D.R.sigW j).2) : ℕ :=
  ⌊DV.aMinusQ D j τ ((D.R.sigW j).2 - 1 - i)⌋₊

theorem sig_add (R : Ranks) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ R.m) : (R.sigW j).1 + (R.sigW j).2 = R.r := by
  have := R.m_add_three_le_k
  simp only [Ranks.sigW, Ranks.r]
  omega

theorem sig_lt (R : Ranks) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ R.m) : (R.sigW j).1 + (R.sigW j).2 < R.nV := by
  have := R.rank_add_five_le
  rw [sig_add R h1 h2]
  simp only [Ranks.nV]
  omega

def ConjStable {K : Type} [Field K] [NumberField K] {r : ℕ} (T : Set (Place K)) (x : Place K → Fin r → ℂ) : Prop :=
  ∃ e : Equiv.Perm {w : Place K // w ∉ T}, ∀ w, ∃ s : Equiv.Perm (Fin r),
    ∀ i, x (e w).1 (s i) = starRingEnd ℂ (x w.1 i)

variable {D : D7} (X : Formalism.MainNotions.InnerProductFormulaField.Loc D)

def TieL : Prop :=
  ∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ π, ∃ (T : Set (Place D.host.E)) (x : Place D.host.E → Fin D.R.r → ℂ),
    SatakeBound T D.R.r ((1 + (D.R.t : ℝ)) / 2) x ∧ ConjStable T x ∧ X.LsS μ j π = eulerProd T Finset.univ x

def TieD : Prop := X.dFin D.R.r = dPart (F := D.host.F) ∅ (quadSign D.host.E) D.R.r D.R.t

def TieReal : Prop :=
  ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), ∃ z : D.what₂.Tau → ℝ,
    (∀ τ, IsRealFactor (sig_lt D.R h1 h2) (rowsP D j τ) (rowsM D j τ) (z τ)) ∧ X.ZSbR j = ∏ τ, z τ

def TieMass : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → X.cSb j = 1 ∧ X.massSb j = Formalism.HermitianLatticesTheory.mass (D.sp.V j).hT (D.sp.V j).L0

def Ties : Prop := TieL X ∧ TieD X ∧ TieReal X ∧ TieMass X

def WindowsLe (L : SizeData₂ D) : Prop := L.etaSz ≤ L.sc.b ∧ L.Sc ≤ L.sc.b

end GlobalTheory.BlockSizes

end
