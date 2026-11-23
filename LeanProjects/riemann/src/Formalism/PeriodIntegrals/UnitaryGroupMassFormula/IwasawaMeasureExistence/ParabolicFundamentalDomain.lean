import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwaStmt

noncomputable section

namespace PI.IwaMeasEx.Sk

open MeasureTheory
open scoped ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.DensDefs Formalism.L2.S.S7.WittLeviSubgroups
  Formalism.L2.S.S7.PositiveOrthantChangeOfVariables

section Data

variable {X : CData} {J : ℕ} (D : BaseDatum X.I J)

def Hyp (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ) : Prop :=
  X.HypB n₀ A ∧ X.FinVol ∧ 2 * X.qq + 2 ≤ X.I.n ∧ 1 ≤ J ∧ J ≤ X.qq

structure PK (μK : Measure X.I.GA) : Prop where
  univ : μK Set.univ = 1
  supp : μK (D.kZero : Set X.I.GA)ᶜ = 0
  inv : ∀ k ∈ D.kZero, μK.map (fun x => k * x) = μK

variable (c : Composition J)

def wgt (m : X.I.GA) : ℝ≥0∞ := ENNReal.ofReal (PI.IwaMeasEx.dInv D.toWittFrame c m)

def muP (μN μM : Measure X.I.GA) : Measure X.I.GA :=
  (μN.prod (μM.withDensity (wgt D c))).map (fun q => q.1 * q.2)

structure PN (μN : Measure X.I.GA) : Prop where
  sfin : SigmaFinite μN
  ne : μN ≠ 0
  supp : μN (D.toWittFrame.uniA c : Set X.I.GA)ᶜ = 0
  cpt : ∀ s : Set X.I.GA, IsCompact s → μN s ≠ ⊤
  inv : ∀ n ∈ D.toWittFrame.uniA c, μN.map (fun x => n * x) = μN
  modl : ∀ m ∈ D.toWittFrame.leviA c, μN.map (fun x => m * x * m⁻¹) = wgt D c m • μN

structure PM (μM : Measure X.I.GA) : Prop where
  sfin : SigmaFinite μM
  ne : μM ≠ 0
  supp : μM (D.toWittFrame.leviA c : Set X.I.GA)ᶜ = 0
  cpt : ∀ s : Set X.I.GA, IsCompact s → μM s ≠ ⊤
  inv : ∀ m ∈ D.toWittFrame.leviA c, μM.map (fun x => m * x) = μM

def IntF (μK μP : Measure X.I.GA) (cIw : ℝ≥0∞) : Prop :=
  cIw ≠ 0 ∧ cIw ≠ ⊤ ∧ ∀ Φ : X.I.GA → ℝ≥0∞, Measurable Φ →
    ∫⁻ x, Φ x ∂(X.I.muA X.μf) = cIw * ∫⁻ p, (∫⁻ k, Φ (p * k) ∂μK) ∂μP

def NF : Subgroup X.I.GA := PPF X.I (D.toWittFrame.flag c) ⊓ D.toWittFrame.uniA c

def MF : Subgroup X.I.GA := PPF X.I (D.toWittFrame.flag c) ⊓ D.toWittFrame.leviA c

def FdP (μN μM : Measure X.I.GA) (FN FM Om : Set X.I.GA) : Prop :=
  MeasurableSet FN ∧ MeasurableSet FM ∧ MeasurableSet Om ∧
    IsFundamentalDomain (PPF X.I (D.toWittFrame.flag c)) Om (muP D c μN μM) ∧
    (∀ n ∈ D.toWittFrame.uniA c, ∀ m ∈ D.toWittFrame.leviA c, n * m ∈ Om ↔ n ∈ FN ∧ m ∈ FM) ∧
    IsFundamentalDomain (NF D c) FN μN ∧ IsFundamentalDomain (MF D c) FM μM

def LeviP (μM : Measure X.I.GA) (FM : Set X.I.GA) (VM : ℝ≥0∞) : Prop :=
  ∀ Φ : (Fin c.length → ℝ) → ℝ≥0∞, Measurable Φ →
    ∫⁻ m in FM, Φ (PI.IwaMeasEx.tBlk D.toWittFrame c m) ∂μM =
      VM * ∫⁻ t in posO c.length, Φ t * ∏ i, ENNReal.ofReal (t i)⁻¹

end Data

def MulMeas : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → Measurable (fun q : X.I.GA × X.I.GA => q.1 * q.2)

def TMeas : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → ∀ (c : Composition J) (D : BaseDatum X.I J),
    Measurable (PI.IwaMeasEx.tBlk D.toWittFrame c)

def DMul : Prop :=
  ∀ (I : AutInst) (J : ℕ) (Fr : WittFrame I J) (c : Composition J), ∀ m ∈ Fr.leviA c, ∀ m' ∈ Fr.leviA c,
    PI.IwaMeasEx.dInv Fr c (m * m') = PI.IwaMeasEx.dInv Fr c m * PI.IwaMeasEx.dInv Fr c m'

def PDec : Prop :=
  ∀ (I : AutInst) (J : ℕ) (Fr : WittFrame I J) (c : Composition J), ∀ γ ∈ PPF I (Fr.flag c),
    ∃ n ∈ Fr.uniA c, ∃ m ∈ Fr.leviA c, γ = n * m

def ExK : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → ∀ D : BaseDatum X.I J, ∃ μK, PK D μK

def ExN : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → ∀ (c : Composition J) (D : BaseDatum X.I J),
    ∃ μN, PN D c μN

def ExM : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → ∀ (c : Composition J) (D : BaseDatum X.I J),
    ∃ μM, PM D c μM

def ParabolicMeasureInvariant : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → ∀ (c : Composition J) (D : BaseDatum X.I J),
    Measurable (fun q : X.I.GA × X.I.GA => q.1 * q.2) → Measurable (PI.IwaMeasEx.tBlk D.toWittFrame c) →
    (∀ m ∈ D.toWittFrame.leviA c, ∀ m' ∈ D.toWittFrame.leviA c,
      PI.IwaMeasEx.dInv D.toWittFrame c (m * m') =
        PI.IwaMeasEx.dInv D.toWittFrame c m * PI.IwaMeasEx.dInv D.toWittFrame c m') →
    ∀ μN μM : Measure X.I.GA, PN D c μN → PM D c μM →
      ∀ n ∈ D.toWittFrame.uniA c, ∀ m ∈ D.toWittFrame.leviA c,
        (muP D c μN μM).map (fun x => n * m * x) = muP D c μN μM

def IwasawaIntegrationFormula : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → ∀ (c : Composition J) (D : BaseDatum X.I J),
    Measurable (fun q : X.I.GA × X.I.GA => q.1 * q.2) → Measurable (PI.IwaMeasEx.tBlk D.toWittFrame c) →
    ∀ μK μN μM : Measure X.I.GA, PK D μK → PN D c μN → PM D c μM →
    (∀ n ∈ D.toWittFrame.uniA c, ∀ m ∈ D.toWittFrame.leviA c,
      (muP D c μN μM).map (fun x => n * m * x) = muP D c μN μM) →
    ∃ cIw, IntF μK (muP D c μN μM) cIw

def ParabolicFundamentalDomain : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → ∀ (c : Composition J) (D : BaseDatum X.I J),
    Measurable (fun q : X.I.GA × X.I.GA => q.1 * q.2) → Measurable (PI.IwaMeasEx.tBlk D.toWittFrame c) →
    ∀ μN μM : Measure X.I.GA, PN D c μN → PM D c μM →
    ∃ FN FM Om : Set X.I.GA, FdP D c μN μM FN FM Om

def LeviIntegralFormula : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → ∀ (c : Composition J) (D : BaseDatum X.I J),
    Measurable (fun q : X.I.GA × X.I.GA => q.1 * q.2) → Measurable (PI.IwaMeasEx.tBlk D.toWittFrame c) →
    ∀ (μM : Measure X.I.GA) (FM : Set X.I.GA), PM D c μM → MeasurableSet FM →
    IsFundamentalDomain (MF D c) FM μM → ∃ VM, LeviP D c μM FM VM

def IwasawaVolumeBound : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ) (J : ℕ), Hyp X n₀ A J → ∀ (c : Composition J) (D : BaseDatum X.I J),
    Measurable (fun q : X.I.GA × X.I.GA => q.1 * q.2) → Measurable (PI.IwaMeasEx.tBlk D.toWittFrame c) →
    ∀ (μK μN μM : Measure X.I.GA) (cIw : ℝ≥0∞) (FN FM Om : Set X.I.GA) (VM : ℝ≥0∞),
    PK D μK → PN D c μN → PM D c μM → IntF μK (muP D c μN μM) cIw →
    FdP D c μN μM FN FM Om → LeviP D c μM FM VM →
    cIw * μN FN * VM ≤ ENNReal.ofReal (X.I.vol X.μf X.fund * Formalism.L2.S.S7.DensityConstant.densityConstant X J c)

section Proved

variable {X : CData} {J : ℕ} (D : BaseDatum X.I J) (c : Composition J)

end Proved

end PI.IwaMeasEx.Sk

end
