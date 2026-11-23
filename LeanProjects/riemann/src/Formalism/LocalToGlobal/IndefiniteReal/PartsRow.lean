import Formalism.LocalToGlobal.IndefiniteReal.IsMultMapUnivZero

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct InnerProductSpace
open IsDedekindDomain NumberField MeasureTheory

namespace Formalism.IndefR.RecTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section FromLinks

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure PartsRec (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) {n : ℕ}
    (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n)
    (eFT : D.what₂.FT ≃ principalLevelFrame.FTR R.θ PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b)))
      (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0))
    {Xd : DivX D} (E : EigIdx D Xd) (labPi : E.Pi → A.fam.base.Ix)
    (piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ)
    (prtE : D.what₂.FT → Submodule ℂ (AmbT (R.MY 0)))
    (prtWf : ∀ i : Fin D.R.m, D.what₂.FT → Submodule ℂ (AmbT (R.MW i (sg0 D A)))) : Prop where

  cOf : ∀ π, piOf (E.cOf π) = principalLevelFrame.cOfT (PW ⟨0, hm⟩)
    (levS _ (R.βW ⟨0, hm⟩) (R.datWp ⟨0, hm⟩ (R.levL F false (sg0 D A))))
    (levChi _ (R.βW ⟨0, hm⟩) (R.datWp ⟨0, hm⟩ (R.levL F false (sg0 D A)))) (SsetF R (tupT D.what₂.mu0)) (principalLevelFrame.rowRepR R.θ (eFT π))

  piOf_inj : Function.Injective piOf

  prt : ∀ π, prtE π ≤ (hPart (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (A.ok A.μ0) R.pl A.q
    (RealDat.polE (A := A) (labPi (E.cOf π)).1)).map (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap

  prtW : ∀ i π, prtWf i π ≤ (hPart (R.MW i (sg0 D A)) (levG _ (R.βW i) (R.datWp i R.triv)) (A.ok A.μ0) R.pl A.q
    (RealDat.polW (A := A) (labPi (E.cOf π)).1)).map (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A)) ≃ₗ[ℂ] _).toLinearMap

def PartsRow (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) {n : ℕ}
    (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n)
    (eFT : D.what₂.FT ≃ principalLevelFrame.FTR R.θ PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b)))
      (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0))
    (prtE : D.what₂.FT → Submodule ℂ (AmbT (R.MY 0)))
    (prtWf : ∀ i : Fin D.R.m, D.what₂.FT → Submodule ℂ (AmbT (R.MW i (sg0 D A)))) : Prop :=
  ∃ (Xd : DivX D) (E : EigIdx D Xd) (labPi : E.Pi → A.fam.base.Ix)
    (piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ),
    PartsRec R F tupT hm PY PW eFT E labPi piOf prtE prtWf

end FromLinks

end Formalism.IndefR.RecTie

end
