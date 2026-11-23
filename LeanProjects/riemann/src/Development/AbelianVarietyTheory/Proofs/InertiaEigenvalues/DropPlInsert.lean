import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeisOAdd

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.GenFinite

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def OffPl {S T' : HSp D} (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (u : WO S T') : Prop :=
  u.map (infPart D) = 0 ∧
    ∀ v ∈ Sb, ∀ ε, IsPlaceIdem D v ε → ∀ i j, algebraMap (AF D.host.F) (AE D) ε * u i j = 0

def SuppIn (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (V : HSp D) (g : GA D V) : Prop :=
  (mt V g - 1).map (infPart D) = 0 ∧
    ∀ v, v ∉ Sb → ∀ ε, IsPlaceIdem D v ε → ∀ i j, algebraMap (AF D.host.F) (AE D) ε * (mt V g - 1) i j = 0

def Over (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal

def LikeOff (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ ∀ c : WO (Vc D i) (Wc D i) →₀ ℂ, (∀ u ∈ c.support, OffPl Sb u) →
    (c.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u (R.vP i t)) = 0 →
    (c.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u f) = 0

def TypeIn (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ ∀ κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t), SuppIn Sb (Vc D i) κ →
    R.ωP i t (κ, 1) f = (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • f

def CleanIn (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  ∀ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) →
    (∃ v ∈ Sb, Over PP.1 v) → ∀ κ : G → GA D (Vc D i), IsLifts R i t κ →
      (∀ g, mirC R i PP a tr ε g ≠ 0 → SuppIn Sb (Vc D i) (κ g)) → avgW R i t PP a tr ε κ f = 0

def StepGen (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    Set (WO (Vc D i) (Wc D i) → ℂ) :=
  {φ | ∃ (g : GA D (Wc D i)) (f : WO (Vc D i) (Wc D i) → ℂ),
    TypeIn R i t Sb f ∧ CleanIn R i t Sb f ∧ LikeOff R i t Sb f ∧ φ = R.ωP i t (1, g) f}

open Classical in

def dropPl (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  Sb.erase v

theorem dropPl_insert [DecidableEq (HeightOneSpectrum (𝓞 D.host.F))] {s : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ s) : dropPl (insert v s) v = s := by
  unfold dropPl
  convert Finset.erase_insert hv

end GlobalTheory.DownLift.GenFinite

end
