import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DropPlInsert
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.SplitCoef

variable {D : D7}

def InvForm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ u : WO S T, IsHalf (cA D a) u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f

open Classical in

def coef (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ) (f : WO S T → ℂ)
    (x : WO S T) : ℂ :=
  if IsHalf a x then ℓ (heisO ψ S T x f) else 0

def HasShape (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (Φ f : WO S T → ℂ) : Prop :=
  ∀ ℓ, InvForm ψ S T a ℓ → ∃ c : ℂ, ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) = c * Φ x

def locSpan (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (f : WO S T → ℂ) : Submodule ℂ (WO S T → ℂ) :=
  Submodule.span ℂ {φ | ∃ u : WO S T, IsHalf (a + cA D a) u ∧ φ = heisO ψ S T u f}

open Classical in

def adjDat (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D)
    (ω : (∀ PP : Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (kP PP)) → ℂ) (x : WO S T) : ℂ :=
  if IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) then ω (fun PP => redM PP (frMapAdj S T βS βT x)) else 0

def translT (S T : HSp D) (a : AE D) (Φ : WO S T → ℂ) : Set (WO S T → ℂ) :=
  {Ψ | ∃ g : GA D T, SuppAt a T g ∧ Ψ = fun x => Φ (actO S T 1 g x)}

abbrev latH (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : AddSubgroup (WO S T) :=
  latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True

def LevChart (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F))
    (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)) : Prop :=
  Function.Surjective φ ∧ (∀ z, φ z = 0 ↔ toEAf D e * z = 0) ∧
    (∀ z, toEAf D e * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ φ z ∈ v.adicCompletionIntegers D.host.F) ∧
    ∀ (s : Formalism.L2.Herm.intAf D.host.F D.host.E) (o : GlobalTheory.SplitHecke.Ov D v), (o : Fv D.host.F v) = φ s →
      ι (resS D.host.F PP s) = IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v) o

def rdAdj (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D))
    {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (x : WO S T) :
    Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) :=
  (frMapAdj S T βS βT x).map φ

end GlobalTheory.DownLift.SplitCoef

end
