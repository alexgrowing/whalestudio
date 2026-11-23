import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FuncSt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def Red (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)) (f : WO S T → ℂ) : WO S T → ℂ :=
  fun w => ellI S T C μ 𝓕 (heisO ψ S T w f)

def IsPerpA (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E) (w : WO S T) : Prop :=
  ∀ a : Mx D r S.rank, symplO S T (embI S T C a) w = 0

def EllIndep (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (r : ℕ)
    (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
    ∀ (μ : Measure (Mx D r S.rank)) (𝓕 𝓕' : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ → IsAddFundamentalDomain (ratMx D r S.rank) 𝓕' μ →
      ∀ f, IsThetaFunO ψ S T f → ellI S T C μ 𝓕 f = ellI S T C μ 𝓕' f

def RedZero (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (r : ℕ) (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)) (f : WO S T → ℂ),
    Red ψ S T C μ 𝓕 f 0 = ellI S T C μ 𝓕 f

def RedLeft (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (r : ℕ)
    (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
    ∀ (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f → ∀ a w,
        Red ψ S T C μ 𝓕 f (embI S T C a + w) = ψ (-(symplOH S T (embI S T C a) w)) * Red ψ S T C μ 𝓕 f w

def RedPerp (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (r : ℕ) (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)) (w₀ : WO S T), IsPerpA S T C w₀ →
    ∀ f : WO S T → ℂ, Red ψ S T C μ 𝓕 (heisO ψ S T w₀ f) = heisO ψ S T w₀ (Red ψ S T C μ 𝓕 f)

def RedTheta (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (r : ℕ)
    (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
    ∀ (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f →
        (∀ x, IsPerpI S T C x → ∀ w,
          Red ψ S T C μ 𝓕 f (ratW T S x + w) = ψ (-(symplOH S T (ratW T S x) w)) * Red ψ S T C μ 𝓕 f w) ∧
        (∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ u ∈ U, IsPerpA S T C u →
          u.map (infPart D) = 0 → heisO ψ S T u (Red ψ S T C μ 𝓕 f) = Red ψ S T C μ 𝓕 f) ∧
        Continuous (Red ψ S T C μ 𝓕 f)

def RedInv (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D) (r : ℕ)
    (C : Matrix (Fin T.rank) (Fin r) D.host.E), IsIsoFrame T C →
    ∀ C' : Matrix (Fin T.rank) (Fin r) D.host.E,
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C' * T.gram * C = 1 →
    ∀ (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D r S.rank) 𝓕 μ → ∀ f, IsThetaFunO ψ S T f →
        Summable (fun b : Matrix (Fin r) (Fin S.rank) D.host.E =>
          ‖Red ψ S T C μ 𝓕 (heisO ψ S T (ratW T S (C' * b)) f) 0‖) ∧
        ((μ 𝓕).toReal : ℂ) * f 0 =
          ∑' b : Matrix (Fin r) (Fin S.rank) D.host.E, Red ψ S T C μ 𝓕 (heisO ψ S T (ratW T S (C' * b)) f) 0

end Formalism.IndefR.Eqv

end
