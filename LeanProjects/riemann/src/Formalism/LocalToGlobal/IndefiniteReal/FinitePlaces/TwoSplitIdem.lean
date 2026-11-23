import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

def TwoSplits (D : D7) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 D.host.E), (2 : 𝓞 D.host.E) ∈ P.asIdeal → ¬ Lev.IsConjPl (D := D) P P

def TwoSplitIdem (D : D7) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 D.host.F), (2 : 𝓞 D.host.F) ∈ v.asIdeal →
    ∃ (e : AE D) (ε : AF D.host.F), IsSplitIdem D e ∧ IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε

def LatSelfDual (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
      (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT →
      IsCompact ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True :
          AddSubgroup (WO S T)) : Set (WO S T)) ∧
      IsOpen {w : WO S T | ∃ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
          (fun _ => True), (w - u).map (finPart D) = 0} ∧
      (∀ a : AE D, finPart D a ∈ intAE D →
        ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
          a • u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)) ∧
      ∀ x : WO S T, x.map (infPart D) = 0 →
        (x ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ↔
          ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
            ψ (symplO S T x u) = 1)

open Classical in

def IdemExists (D : D7) : Prop :=
  (∀ P : HeightOneSpectrum (𝓞 D.host.E), ¬ Lev.IsConjPl (D := D) P P → ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e P ∧
    ∀ v : HeightOneSpectrum (𝓞 D.host.F), P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal →
      ∃ ε : AF D.host.F, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧
  (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e e' : AE D), Formalism.L2.NTheta.IsIdemAt e P → Formalism.L2.NTheta.IsIdemAt e' P →
    e = e') ∧
  ∀ (gp : Fin 2 → ℕ) (pb : Fin 2 → 𝓞 D.host.E) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)),
    Lev.IsTypePlaces (D := D) gp pb Pg → Lev.IsTwistPlaces (D := D) gp Q → ∃ e : AE D, IsIdemSum e (Pg ∪ Q)

def LiftsExistB (D : D7) : Prop :=
  ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ)
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (gp : Fin 2 → ℕ) (pb : Fin 2 → 𝓞 D.host.E),
    Lev.IsBaseFrame V β Λ N → Lev.IsTypePlaces (D := D) gp pb L.Pg → Lev.IsTwistPlaces (D := D) gp L.Q →
      Lev.LiftsExist V β L

def HeisStable (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (w₀ : WO S T) (f : WO S T → ℂ),
    IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w₀ f)

def DRhoStable (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (S T : HSp D) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ),
      IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f)

def PtStable (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
      (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ)
      (P : MvPolynomial (FVar D T.rank S.rank) ℂ),
      IsThetaFunO ψ S T f → IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P)

end Formalism.IndefR.Fin

end
