import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.VacAll

def MoveT {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (θ : InfFam (I.rec7 l Z)) (i : ℕ)
    (hi : i + 1 ≤ B.R.m) (c₀ : ℂ) (μ : (AE (I.rec7 l Z))ˣ →* Circle) (om : Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)))
    (vac : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ)
    (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)) (h : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X (i + 1))) : Prop :=
  ∀ N N', Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) g N → Moves _ (rankN (I.rec7 l Z) (i + 1) hi) h N' →
    ∀ x y, IsDetRoot _ g x → IsDetRoot _ h y →
      ColDat.xiS θ i hi (om (g, h) vac) = fun z => c₀ * (μ x : ℂ)⁻¹ * (μ y : ℂ) * I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N N' z

theorem vacT_iff {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {θ : InfFam (I.rec7 l Z)} {i : ℕ}
    {hi : i + 1 ≤ B.R.m} {c₀ : ℂ} {μ : (AE (I.rec7 l Z))ˣ →* Circle} {om : Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))}
    {vac : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ} :
    VacT I l Z θ i hi c₀ μ om vac ↔ ∀ g ∈ GfC _, ∀ h ∈ GfC _, MoveT I l Z θ i hi c₀ μ om vac g h := Iff.rfl

theorem xiS_smul {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} (θ : InfFam (I.rec7 l Z)) (i : ℕ)
    (hi : i + 1 ≤ B.R.m) (c : ℂ) (F : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ) :
    ColDat.xiS θ i hi (c • F) = fun z => c * ColDat.xiS θ i hi F z := by
  funext z
  simp only [ColDat.xiS, xiN, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.AdForm.VacAll
