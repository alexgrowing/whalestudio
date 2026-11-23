import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.UnitBracket
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicFormsHyp

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
  Formalism.IndefR.Fock.Sk MeasureTheory IsDedekindDomain NumberField Matrix

namespace Formalism.IndefR.WeilFull

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def SuppV (ε : AF D.host.F) (V : HSp D) (g : GA D V) : Prop :=
  ∀ i j, algebraMap (AF D.host.F) (AE D) ε * (mt V g - 1) i j = (mt V g - 1) i j

def UnrAtV (ε : AF D.host.F) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, (1 - algebraMap (AF D.host.F) (AE D) ε) * (x : AE D) = 1 - algebraMap (AF D.host.F) (AE D) ε →
    finPart D (x : AE D) ∈ intAE D → finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → χ x = 1

def SphInertAtO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop :=
  S.rank ≠ T.rank → (Even S.rank ∨ Even T.rank) →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
      IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)),
      Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT →
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
      (2 : 𝓞 D.host.F) ∉ v.asIdeal →
      (∀ e, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) ε = 0) →
      UnrAtV ε χS → UnrAtV ε χT →
    ∀ (g : GA D S) (h : GA D T), SuppV ε S g → SuppV ε T h →
      Lev.finE S g ∈ Formalism.L2.DIV.St βS → Lev.finE T h ∈ Formalism.L2.DIV.St βT →
    ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
      IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun w => w = v) f → om (g, h) f = f

def RealAtO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop :=
  LineAtExists D →
  ∀ (θ : InfFam D) sS sT BS BT (pS pT : D.what₂.Tau → ℕ), PairSetup ψ θ S T sS sT BS BT pS pT →
    ∀ (τ : D.what₂.Tau) (αS αT : ℚ), HasInfExp D χS τ αS → HasInfExp D χT τ αT →
    ∀ (XS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (XT : Matrix (Fin T.rank) (Fin T.rank) ℂ),
      XS ∈ lieAt S τ → XT ∈ lieAt T τ →
        ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f →
          ∀ (P : MvPolynomial (FVar D T.rank S.rank) ℂ) (x : WO S T),
            HasDerivAt (fun t : ℝ => om (oneP θ S τ XS t, oneP θ T τ XT t) (pureTensorO ψ θ S T sS sT BS BT f P) x)
              (pureTensorO ψ θ S T sS sT BS BT f
                (quadOp τ (sS τ) (BS τ) XS (sT τ) (BT τ) XT (pS τ) (pT τ) P +
                  (halfTrJ (sS τ) (BS τ) XS (sT τ) (BT τ) XT (pS τ) (pT τ) + (αS : ℂ) * XT.trace -
                    (αT : ℂ) * XS.trace) • P) x) 0

structure IsWeilFull (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop where
  datum : IsWeilDatumO ψ S T χS χT om
  inert : SphInertAtO ψ S T χS χT om
  real : RealAtO ψ S T χS χT om

def WeilExistsFull (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle),
    IsStdChar D ψ (-1) → IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank →
    ∃ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilFull ψ S T χS χT om

def InertAllO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → SphInertAtO ψ S T χS χT om

def RealAllO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → RealAtO ψ S T χS χT om

theorem weilExistsFull_of (h : AutomorphicFormsHyp.WeilExistsO D) (hi : InertAllO D) (hr : RealAllO D) : WeilExistsFull D := by
  intro ψ S T χS χT hψ hS hT hrS hrT
  obtain ⟨om, hom⟩ := h ψ S T χS χT hψ hS hT hrS hrT
  exact ⟨om, hom, hi ψ S T χS χT om hom, hr ψ S T χS χT om hom⟩

end Formalism.IndefR.WeilFull

end
