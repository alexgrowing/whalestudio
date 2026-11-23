import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.DownLift.GenFinite

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def Ann (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) : Set (WO (Vc D i) (Wc D i) → ℂ) :=
  {φ | IsThetaFunO R.ψ (Vc D i) (Wc D i) φ ∧ ∀ l g, downInt R i t y φ l g = 0}

def Gen (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Set (WO (Vc D i) (Wc D i) → ℂ) :=
  {φ | ∃ (g : GA D (Wc D i)) (f : WO (Vc D i) (Wc D i) → ℂ), FinLike R i t f ∧ φ = R.ωP i t (1, g) f}

def TypeVec (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ ∀ κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t),
    R.ωP i t (κ, 1) f = (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • f

def TypeDiff (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Set (WO (Vc D i) (Wc D i) → ℂ) :=
  {φ | ∃ κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t), ∃ f : WO (Vc D i) (Wc D i) → ℂ,
    IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ φ = R.ωP i t (κ, 1) f - (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • f}

def IsLifts (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (κ : G → GA D (Vc D i)) : Prop :=
  ∀ g, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) (κ g)

def avgW (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool) (ε : ℤ)
    (κ : G → GA D (Vc D i)) (f : WO (Vc D i) (Wc D i) → ℂ) : WO (Vc D i) (Wc D i) → ℂ :=
  ∑ g, (mirC R i PP a tr ε g * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) • R.ωP i t ((κ g)⁻¹, 1) f

def AvgIm (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Set (WO (Vc D i) (Wc D i) → ℂ) :=
  {φ | ∃ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 ∧ ∃ (tr : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧
    ∃ κ : G → GA D (Vc D i), IsLifts R i t κ ∧ ∃ f : WO (Vc D i) (Wc D i) → ℂ,
      IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ φ = avgW R i t PP a tr ε κ f}

def Clean (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  ∀ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) →
    ∀ κ : G → GA D (Vc D i), IsLifts R i t κ → avgW R i t PP a tr ε κ f = 0

section ThetaAlg

variable {ψ : AddChar (AF D.host.F) ℂ} {S T' : HSp D}

theorem heisO_add' (u : WO S T') (f g : WO S T' → ℂ) : heisO ψ S T' u (f + g) = heisO ψ S T' u f + heisO ψ S T' u g := by
  funext w; simp only [heisO, Pi.add_apply]; ring

theorem theta_add {f g : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) (hg : IsThetaFunO ψ S T' g) :
    IsThetaFunO ψ S T' (f + g) where
  quasi γ w := by simp only [Pi.add_apply]; rw [hf.quasi, hg.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    obtain ⟨U', hUo', hU'⟩ := hg.level
    refine ⟨U ⊓ U', hUo.inter hUo', fun u hu hi => ?_⟩
    rw [heisO_add', hU u hu.1 hi, hU' u hu.2 hi]
  cont := hf.cont.add hg.cont
  smooth k L hL hfin w := (hf.smooth k L hL hfin w).add (hg.smooth k L hL hfin w)

theorem theta_smul (c : ℂ) {f : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) : IsThetaFunO ψ S T' (c • f) where
  quasi γ w := by simp only [Pi.smul_apply, smul_eq_mul]; rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U, hUo, fun u hu hi => ?_⟩
    have e : heisO ψ S T' u (c • f) = c • heisO ψ S T' u f := by
      funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, hU u hu hi]
  cont := continuous_const.mul hf.cont
  smooth k L hL hfin w := contDiff_const.mul (hf.smooth k L hL hfin w)

theorem theta_sub {f g : WO S T' → ℂ} (hf : IsThetaFunO ψ S T' f) (hg : IsThetaFunO ψ S T' g) :
    IsThetaFunO ψ S T' (f - g) := by
  have e : f - g = f + (-1 : ℂ) • g := by funext w; simp [sub_eq_add_neg]
  rw [e]
  exact theta_add hf (theta_smul (-1) hg)

theorem theta_sum {ι : Type} (s : Finset ι) (u : ι → WO S T' → ℂ)
    (f₀ : WO S T' → ℂ) (h₀ : IsThetaFunO ψ S T' f₀) (hu : ∀ k ∈ s, IsThetaFunO ψ S T' (u k)) :
    IsThetaFunO ψ S T' (∑ k ∈ s, u k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := theta_smul (0 : ℂ) h₀
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact theta_add (hu a (Finset.mem_insert_self _ _)) (ih fun k hk => hu k (Finset.mem_insert_of_mem hk))

end ThetaAlg

end GlobalTheory.DownLift.GenFinite

end
