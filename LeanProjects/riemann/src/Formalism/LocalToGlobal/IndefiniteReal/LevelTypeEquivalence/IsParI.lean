import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FuncSt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsParI (T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E) (m : GA D T) : Prop :=
  (∃ a : Matrix (Fin r) (Fin r) (AE D),
      HMul.hMul (Formalism.L2.Theta.mt T m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a) ∧
    ∀ x : Fin T.rank → D.host.E, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * T.gram).mulVec x = 0 →
      ∃ b : Fin r → AE D, (Formalism.L2.Theta.mt T m).mulVec (fun i => incA D (x i)) - (fun i => incA D (x i)) =
        (C.map (incA D)).mulVec b

def ParabM (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    Formalism.IndefR.Fin.SvNSchurO ψ S T →
    ∀ (r : ℕ) (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
      ∀ (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ →
        ∀ m : GA D T, IsParI T C m → ∃ c : ℂ, ∀ f, IsThetaFunO ψ S T f →
          ellI S T C μ 𝓕 (om (1, m) f) = c * ellI S T C μ 𝓕 f

end Formalism.IndefR.Eqv

end
