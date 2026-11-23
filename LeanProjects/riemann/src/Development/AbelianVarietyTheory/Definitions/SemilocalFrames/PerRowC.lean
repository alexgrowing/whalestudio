import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DimFormC
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PairBdNonneg
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC

noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Obj
variable {D : D7} {X : HidaSetting D}

def DbL (D : D7) (j : ℕ) (δ : ℕ → D.host.E) : ℝ := ∏ l ∈ k2ends D j δ, ((Nloc (ddS D) D.R.rS l (δ l) : ℚ) : ℝ)

def AmpAt (large₂ : SizeData₂ D) (Y : Full X) (u : D.what₂.Word) (CH Cs C : ℝ) : Prop :=
  ∀ t ∈ relSet Y u, ‖(Y.tO u u).vec t‖ ≤
    Formalism.L2.SG.TermOp.wt t * Real.sqrt (dpiC X u) * (omT t * k2a large₂ CH Cs C (jT t) (labT t))

def PairsAt (large₂ : SizeData₂ D) (Y : Full X) (u : D.what₂.Word) (CH Ch Cp : ℝ) : Prop :=
  ∀ j' ∈ Finset.Icc 1 D.R.rS, ∀ j'' ∈ Finset.Icc 1 D.R.rS, ∀ (δ' δ'' : ℕ → D.host.E) (S : Finset (GTu Y u × GTu Y u)),
    (∀ p ∈ S, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ jT p.1 = j' ∧ jT p.2 = j'' ∧ labT p.1 = δ' ∧ labT p.2 = δ'') →
    ∑ p ∈ S, (Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2) ≤
      massC Y u * (k2e large₂ CH Ch Cp j' δ' * k2e large₂ CH Ch Cp j'' δ'')
end Obj

def TypeP : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ CH Ch Cp : ℝ, 0 ≤ CH ∧ 0 ≤ Ch ∧ 0 ≤ Cp ∧ ∀ Cs : ℝ, Cp + 4 ≤ Cs →
    ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
        Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → TypeAt large₂ Y u CH Cs C Ch Cp

def AmpP : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ CH : ℝ, 0 ≤ CH ∧ ∀ Cs : ℝ, 0 ≤ Cs →
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.BasicNotions.Ties D →
        Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → AmpAt large₂ Y u CH Cs C

def PairsP : Prop :=
  ∀ Cg cb Cw cT CT C0 CH : ℝ, 0 ≤ CH → ∃ Ch Cp : ℝ, 0 ≤ Ch ∧ 0 ≤ Cp ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → ConcTie X Y → PairsAt large₂ Y u CH Ch Cp

def NFExC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ t ∈ relSet Y u,
    ∃ N, AdT t N ∧ N.j = jT t ∧ N.T = Tu D u

def LabC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ (t : GTu Y u) N, AdT t N →
    N.j = jT t ∧ N.T = Tu D u ∧ N.Del = k2Del D (jT t) (labT t) ∧ N.Db = DbL D (jT t) (labT t) ∧
      GlobalTheory.DegAsm.lab (F0 X u) (Ft t) (jT t) = fun l => star (labT t l)

def PerRowC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ →
    ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype →
    ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (j' j'' : ℕ) (δ' δ'' : ℕ → D.host.E) (S : Finset (GTu Y u × GTu Y u)),
      (∀ p ∈ S, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ p.1.lam = Λ ∧ jT p.1 = j' ∧ jT p.2 = j'' ∧ labT p.1 = δ' ∧
        labT p.2 = δ'') →
      ENNReal.ofReal (∑ p ∈ S, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2)) ≤
        ∑ x ∈ Finset.Icc 1 ⌊k2Del D j' δ'⌋₊, ∑ x' ∈ Finset.Icc 1 ⌊k2Del D j'' δ''⌋₊,
          (((GlobalTheory.DegCnt.Trip HW (gS D) (GlobalTheory.DegAsm.lat0 (F0 X u) W.subtype Λ) D.R.rS x x').encard : ℕ∞) : ℝ≥0∞) *
            ENNReal.ofReal (GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ') (NT D u) x *
              GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'') (NT D u) x')

def ProdC : Prop :=
  ∀ Cs : ℝ, 0 ≤ Cs → ∃ C₁ : ℕ, 1 ≤ C₁ ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1)
    (CH : ℝ), Std D large₂ → 0 ≤ CH → 40 * D.R.rS ^ 4 ≤ D.R.k → 5 * D.R.rS ≤ D.R.k → ∀ t ∈ relSet Y u, ∀ hj : jT t ≤ D.R.rS, 1 ≤ jT t →
    ∃ (De : D.what₂.Tau → ℝ) (P : ℝ), 0 < P ∧ k2Del D (jT t) (labT t) = P ^ 2 ∧
      (∀ τ, GlobalTheory.Amp.DeOK D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (gamT C t τ) (De τ)) ∧
      ∏ τ, GlobalTheory.Amp.degBd D.R.k D.R.rS (jT t) (C₁ * D.R.k * D.R.rS) (H1C large₂ CH) (De τ)
          (GlobalTheory.Amp.Dj D.R.k D.R.rS hj (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (gamT C t τ))
          (GlobalTheory.Amp.sgV D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (gamT C t τ) (H1C large₂ CH)) ≤
        (16 * Real.pi * Real.exp 1 / D.R.k) ^ (jT t * (D.R.k - 1 - jT t) * D.R.f) * (P ^ (D.R.k - 1 - jT t))⁻¹ *
          (8 * D.R.rS * H1C large₂ CH) ^ (80 * D.R.rS ^ 4 * D.R.f) * k2S D (H1C large₂ CH) (jT t) (labT t) ^ (-(Cs * D.R.k))
end GlobalTheory.TypeAsm
