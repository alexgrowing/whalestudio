import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.ParabSt
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.CtFullSt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Tow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def liftO {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ν : Measure (GA D S))
    (𝓕 : Set (GA D S)) (f : WO S T → ℂ) (F : GA D S → ℂ) : GA D T → ℂ :=
  Formalism.IndefR.Lift.liftInt ν 𝓕 (fun (g' : GA D T) (h : GA D S) (s : WO S T → ℂ) => thetaKO om h g' s) f F

def CtInteg (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (μ : Measure (Mx D r S.rank)) (𝓕L : Set (Mx D r S.rank)) (νN : Measure (NI T C)) (𝓕N : Set (NI T C))
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ν : Measure (GA D S)) (𝓕 : Set (GA D S))
    (F : GA D S → ℂ) (g : GA D T) (f : WO S T → ℂ) : Prop :=
  Integrable (fun p : NI T C × GA D S => thetaKO om p.2 ((p.1 : GA D T) * g) f * F p.2)
      ((νN.restrict 𝓕N).prod (ν.restrict 𝓕)) ∧
    Integrable (fun h => ∑' q : Matrix (Fin T.rank) (Fin S.rank) D.host.E ⧸ perpSub S T C,
      ‖jX ψ C μ 𝓕L νN 𝓕N om f (Quotient.out q) h g‖ * ‖F h‖) (ν.restrict 𝓕) ∧
    ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, Measurable fun h => jX ψ C μ 𝓕L νN 𝓕N om f x h g

def ConstTermLow (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T T' : HSp D) (χS χT : (AE D)ˣ →* Circle),
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (r : ℕ) (C C' : Matrix (Fin T.rank) (Fin r) D.host.E) (B : Matrix (Fin T.rank) (Fin T'.rank) D.host.E),
      Formalism.IndefR.Mi.IsQuotFrame T C C' T' B →
      ∀ (μ : Measure (Mx D r S.rank)) (𝓕L : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (Formalism.IndefR.Eqv.ratMx D r S.rank) 𝓕L μ →
      ∀ (νN : Measure (NI T C)) (𝓕N : Set (NI T C)), νN.IsHaarMeasure → IsFundamentalDomain (NIQ T C) 𝓕N νN →
        SFinite (νN.restrict 𝓕N) →
        ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
          (om' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)),
          IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T' χS χT om' →
          Formalism.IndefR.Mi.IsDescOf ψ S T C C' T' B μ 𝓕L om om' →
          ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν →
            SFinite (ν.restrict 𝓕) →
            ∀ F : GA D S → ℂ, IsAutFun S F → IsCuspFun S F →
              ∀ (g : GA D T) (f : WO S T → ℂ), IsThetaFunO ψ S T f →
                CtInteg ψ C μ 𝓕L νN 𝓕N om ν 𝓕 F g f →
                ∫ n in 𝓕N, liftO om ν 𝓕 f F ((n : GA D T) * g) ∂νN =
                  κ * liftO om' ν 𝓕 (Formalism.IndefR.Mi.desc ψ S T C μ 𝓕L T' B (om (1, g) f)) F 1

def CuspOfLowVanish (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle),
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilDatumO ψ S T χS χT om →
    ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν →
      SFinite (ν.restrict 𝓕) →
      ∀ F : GA D S → ℂ, IsAutFun S F → IsCuspFun S F → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
        (∀ (r : ℕ) (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
          ∃ (T' : HSp D) (C' : Matrix (Fin T.rank) (Fin r) D.host.E) (B : Matrix (Fin T.rank) (Fin T'.rank) D.host.E),
            Formalism.IndefR.Mi.IsQuotFrame T C C' T' B) →
        (∀ (T' : HSp D) (r : ℕ) (C C' : Matrix (Fin T.rank) (Fin r) D.host.E)
          (B : Matrix (Fin T.rank) (Fin T'.rank) D.host.E), Formalism.IndefR.Mi.IsQuotFrame T C C' T' B →
          ∀ om' : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ), IsWeilDatumO ψ S T' χS χT om' →
            ∀ f' : WO S T' → ℂ, IsThetaFunO ψ S T' f' → liftO om' ν 𝓕 f' F 1 = 0) →
        (∀ (r : ℕ) (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
          ∀ (νN : Measure (NI T C)) (𝓕N : Set (NI T C)), νN.IsHaarMeasure → IsFundamentalDomain (NIQ T C) 𝓕N νN →
            ∃ (μ : Measure (Mx D r S.rank)) (𝓕L : Set (Mx D r S.rank)), μ.IsAddHaarMeasure ∧
              IsAddFundamentalDomain (Formalism.IndefR.Eqv.ratMx D r S.rank) 𝓕L μ ∧
              ∀ g : GA D T, CtInteg ψ C μ 𝓕L νN 𝓕N om ν 𝓕 F g f) →
        IsCuspFun T (liftO om ν 𝓕 f F)

end Formalism.IndefR.Tow

end
