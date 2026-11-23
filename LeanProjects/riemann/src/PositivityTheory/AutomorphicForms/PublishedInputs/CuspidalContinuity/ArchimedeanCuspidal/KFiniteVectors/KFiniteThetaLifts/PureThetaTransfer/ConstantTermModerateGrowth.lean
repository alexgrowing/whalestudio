import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.AdmM
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.TTRANS

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3.R (G2 Jd md KA LInv pri dia2 pt)
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.K.QuadraticBaseChangeGL3.Th

variable {K : Type} [Field K] [NumberField K]

def GrowOn (P : Set G2) (F : G2 → ℂ) : Prop := ∃ (C : ℝ) (N : ℕ), ∀ (x : 𝔸[ℚ]) (a z : Jd) (κ : KA),
  pt x a z κ.1 ∈ P → ‖F (pt x a z κ.1)‖ ≤ C * ((md a + (md a)⁻¹) * (md z + (md z)⁻¹)) ^ N

def EXTA : Prop := ∀ (D : Subgroup Jd) (Nm : Subgroup ℚˣ) (A A0 W : G2 → ℂ) (κ₀ : ℂ), IsOpen (D : Set Jd) →
  (∀ β : ℚˣ, pri β ∈ D ↔ β ∈ Nm) → κ₀ ≠ 0 →
  (∀ γ : GL (Fin 2) ℚ, (γ.val).det = 1 → ∀ g, GeneralLinearGroup.det g ∈ D → A (dia2 γ * g) = A g) →
  (∀ g, GeneralLinearGroup.det g ∈ D → HasSum (fun α : ℚˣ => κ₀ * W (dg2 (pri α) 1 * g)) (A g - A0 g)) →
  (∀ g, GeneralLinearGroup.det g ∈ D → ∀ x : 𝔸[ℚ], A0 (uni2 x * g) = A0 g) →
  (∀ g, GeneralLinearGroup.det g ∈ D → ∀ β ∈ Nm, A0 (dg2 (pri β) 1 * g) = A0 g) →
  (∀ z : Jd, ∃ u : ℂ, ‖u‖ = 1 ∧ (∀ g, W (dg2 z z * g) = u * W g) ∧
    ∀ g, GeneralLinearGroup.det g ∈ D → A0 (dg2 z z * g) = u * A0 g) →
  (∀ (x : 𝔸[ℚ]) g, W (uni2 x * g) = (adelicChar ℚ (-x) : ℂ) * W g) →
  (∀ g, GeneralLinearGroup.det g ∉ D → W g = 0) →
  ContinuousOn A {g | GeneralLinearGroup.det g ∈ D} → ContinuousOn A0 {g | GeneralLinearGroup.det g ∈ D} →
  Continuous W → GrowOn {g | GeneralLinearGroup.det g ∈ D} A0 →
  (∀ h, Summable (fun α : ℚˣ => ‖W (dg2 (pri α) 1 * h)‖)) →
  (∃ (C : ℝ) (N : ℕ), ∀ (x : 𝔸[ℚ]) (a z : Jd) (κ : KA),
    ∑' α : ℚˣ, ‖W (dg2 (pri α) 1 * pt x a z κ.1)‖ ≤ C * ((md a + (md a)⁻¹) * (md z + (md z)⁻¹)) ^ N) →
  Gau2 W → ∃ θ Cst : G2 → ℂ, ThX θ Cst W

def NmK (K : Type) [Field K] [NumberField K] : Subgroup ℚˣ := (Units.map (Algebra.norm ℚ : K →* ℚ)).range

variable (K) in

def GPD : Prop := Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (c : HeckeCharacter K) (M : ∀ v : Pl, LM c v), AdmM M →
  ∃ D : Subgroup Jd, IsOpen (D : Set Jd) ∧ Gp M = {g | GeneralLinearGroup.det g ∈ D} ∧ ∀ β : ℚˣ, pri β ∈ D ↔ β ∈ NmK K

variable (K) in

def CONTG : Prop := Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (DK : DatK K) c n t S, AdmK DK c n t S →
  ∀ M : ∀ v : Pl, LM c v, AdmM M → ∀ R Sv,
    ContinuousOn (thA R Sv n t M) (Gp M) ∧ ContinuousOn (th0 R Sv n t M) (Gp M)

variable (K) in

def ConstantTermModerateGrowth : Prop := Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (DK : DatK K) c n t S, AdmK DK c n t S →
  ∀ M : ∀ v : Pl, LM c v, AdmM M → ∀ R Sv, GrowOn (Gp M) (th0 R Sv n t M)

variable (K) in

def CENW : Prop := Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (DK : DatK K) c n t S, AdmK DK c n t S →
  ∀ M : ∀ v : Pl, LM c v, AdmM M → ∀ z : Jd, ∃ u : ℂ, ‖u‖ = 1 ∧ (∀ g, WM n t M (dg2 z z * g) = u * WM n t M g) ∧
    ∀ R Sv, ∀ g ∈ Gp M, th0 R Sv n t M (dg2 z z * g) = u * th0 R Sv n t M g

variable (K) in

def WPSI : Prop := Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v), AdmM M →
  ∀ (x : 𝔸[ℚ]) g, WM n t M (uni2 x * g) = (adelicChar ℚ (-x) : ℂ) * WM n t M g

variable (K) in

def WSUP : Prop := Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v), AdmM M →
  ∀ g ∉ Gp M, WM n t M g = 0

variable (K) in

def WCONT : Prop := Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v), AdmM M →
  Continuous (WM n t M)

variable (K) in

def WGAU : Prop := Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v), AdmM M →
  Gau2 (WM n t M)

variable (K) in

def WSUM : Prop := Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (n : ℤ) (t : ℝ) (M : ∀ v : Pl, LM c v), AdmM M →
  (∀ h, Summable (fun α : ℚˣ => ‖WM n t M (dg2 (pri α) 1 * h)‖)) ∧
  ∃ (C : ℝ) (N : ℕ), ∀ (x : 𝔸[ℚ]) (a z : Jd) (κ : KA),
    ∑' α : ℚˣ, ‖WM n t M (dg2 (pri α) 1 * pt x a z κ.1)‖ ≤ C * ((md a + (md a)⁻¹) * (md z + (md z)⁻¹)) ^ N

variable (K) in

def TASM : Prop := MEX K → THS K → AVG K → FEX K → GPD K → CONTG K → ConstantTermModerateGrowth K → CENW K → WPSI K → WSUP K → WCONT K →
  WGAU K → WSUM K → REALTH → EXTA → TPURE K

end Ad3.K.QuadraticBaseChangeGL3.Th
