import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct

namespace GlobalTheory.Core.Rk

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000 in

structure Tower (D : D7) extends LevCh D Unit where

  θ : InfFam D

  ψ : AddChar (AF D.host.F) ℂ

  MY : ∀ j, DSModel (Yc D j) (parB (Ptw D) (min j D.R.m))

  MX : DSModel D.sp.X' (parB (Ptw D) D.R.m)

  νY : ∀ j, Measure (GA D (Yc D j))
  fdY : ∀ j, Set (GA D (Yc D j))

  νX : Measure (GA D D.sp.X')
  fdX : Set (GA D D.sp.X')

  ωY : ∀ k, GA D (Yc D k) × GA D (Yc D (k + 1)) →* Module.End ℂ (WO (Yc D k) (Yc D (k + 1)) → ℂ)

  ωX : GA D (Yc D (D.R.m - 1)) × GA D D.sp.X' →* Module.End ℂ (WO (Yc D (D.R.m - 1)) D.sp.X' → ℂ)

  vac : ∀ k, WO (Yc D k) (Yc D (k + 1)) → ℂ
  vacX : WO (Yc D (D.R.m - 1)) D.sp.X' → ℂ

  vY : ∀ k, WO (Yc D k) (Yc D (k + 1)) → ℂ
  vX : WO (Yc D (D.R.m - 1)) D.sp.X' → ℂ

  ItY : ∀ k, PolF D (Yc D (k + 1)).rank (Yc D k).rank →ₗ[ℂ] SmT (MY (k + 1)) →ₗ[ℂ] SmT (MY k)
  ItX : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank →ₗ[ℂ] SmT MX →ₗ[ℂ] SmT (MY (D.R.m - 1))

  ioY : ∀ k, MultT θ (MY (k + 1)) (levS _ (βY (k + 1)) (toLevCh.datYt () (k + 1) toLevCh.triv))
      (levChi _ (βY (k + 1)) (toLevCh.datYt () (k + 1) toLevCh.triv)) →ₗ[ℂ]
    MultT θ (MY k) (levS _ (βY k) (toLevCh.datYt () k toLevCh.triv)) (levChi _ (βY k) (toLevCh.datYt () k toLevCh.triv))

  ioX : MultT θ MX (levS _ βX (toLevCh.datXt ())) (levChi _ βX (toLevCh.datXt ())) →ₗ[ℂ]
    MultT θ (MY (D.R.m - 1)) (levS _ (βY (D.R.m - 1)) (toLevCh.datYt () (D.R.m - 1) toLevCh.triv))
      (levChi _ (βY (D.R.m - 1)) (toLevCh.datYt () (D.R.m - 1) toLevCh.triv))

namespace Tower

variable {D : D7} (W : Tower D)

abbrev Lv : Type := LevelP W.Pg D.R.r ℂ

abbrev CP (P : W.Lv) (j : ℕ) : Submodule ℂ (SmT (W.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) :=
  MultT W.θ (W.MY j) (levS _ (W.βY j) (W.datYt () j P)) (levChi _ (W.βY j) (W.datYt () j P))

abbrev CC (j : ℕ) : Submodule ℂ (SmT (W.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) := W.CP W.triv j

def datXP (P : W.Lv) : LevDat D.host.E ℂ D.sp.X'.rank :=
  datY _ D.R.r D.R.t D.R.m r_le_X W.Pg (W.Q ()) P W.chi (W.xiR ()) Frm.B

abbrev CXP (P : W.Lv) : Submodule ℂ (SmT W.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) :=
  MultT W.θ W.MX (levS _ W.βX (W.datXP P)) (levChi _ W.βX (W.datXP P))

abbrev CX : Submodule ℂ (SmT W.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) :=
  MultT W.θ W.MX (levS _ W.βX (W.datXt ())) (levChi _ W.βX (W.datXt ()))

def ptY (k : ℕ) : PolF D (Yc D (k + 1)).rank (Yc D k).rank → (WO (Yc D k) (Yc D (k + 1)) → ℂ) :=
  pureTensorO W.ψ W.θ (Yc D k) (Yc D (k + 1)) (cart (W.MY k)) (cart (W.MY (k + 1))) (onb (W.MY k)) (onb (W.MY (k + 1))) (W.vY k)

def ptX : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank → (WO (Yc D (D.R.m - 1)) D.sp.X' → ℂ) :=
  pureTensorO W.ψ W.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (W.MY (D.R.m - 1))) (cart W.MX) (onb (W.MY (D.R.m - 1))) (onb W.MX) W.vX

structure Pre : Prop where
  chars : W.toLevCh.Is ()
  inf : IsInfFam W.θ
  std : IsStdChar D W.ψ (-1)
  νY : ∀ j, j + 1 < D.R.m → IsMeasFD (Yc D j) (lev D.sp.cm (Yc D j).gram (W.βY j) (W.datYt () j W.triv)) (W.νY j) (W.fdY j)
  νY' : IsMeasDef (Yc D (D.R.m - 1))
    (lev D.sp.cm (Yc D (D.R.m - 1)).gram (W.βY (D.R.m - 1)) (W.datYt () (D.R.m - 1) W.triv)) (W.νY (D.R.m - 1)) (W.fdY (D.R.m - 1))
  νX : IsMeasDef D.sp.X' (lev D.sp.cm D.sp.X'.gram W.βX (W.datXt ())) W.νX W.fdX
  ωY : ∀ k, k + 1 < D.R.m → IsWeilDatumO W.ψ (Yc D k) (Yc D (k + 1)) (Lift.chrStep (W.toLevCh.mu ()) W.eta (k + 1)).1
    (Lift.chrStep (W.toLevCh.mu ()) W.eta (k + 1)).2 (W.ωY k)
  ωX : IsWeilDatumO W.ψ (Yc D (D.R.m - 1)) D.sp.X' (Lift.chrStep (W.toLevCh.mu ()) W.eta D.R.m).1
    (Lift.chrStep (W.toLevCh.mu ()) W.eta D.R.m).2 W.ωX
  vY : ∀ k, k + 1 < D.R.m → IsStepVecOf W.ψ W.θ (Yc D k) (Yc D (k + 1)) (cart (W.MY k)) (cart (W.MY (k + 1))) (W.ΛY k)
    (W.ΛY (k + 1)) (W.βY k) (W.βY (k + 1)) (W.datYt () k W.triv) (W.chi (k + 1)) (W.Q ()) (W.xiR ()) (W.vac k) (W.vY k)
  vX : IsStepVecOf W.ψ W.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (W.MY (D.R.m - 1))) (cart W.MX) (W.ΛY (D.R.m - 1)) W.ΛX
    (W.βY (D.R.m - 1)) W.βX (W.datYt () (D.R.m - 1) W.triv) (W.chi D.R.m) (W.Q ()) (W.xiR ()) W.vacX W.vX
  ptY : ∀ k, k + 1 < D.R.m → ∀ P, IsThetaFunO W.ψ (Yc D k) (Yc D (k + 1)) (W.ptY k P)
  ptX : ∀ P, IsThetaFunO W.ψ (Yc D (D.R.m - 1)) D.sp.X' (W.ptX P)
  ItY : ∀ k, k + 1 < D.R.m → IsItW W.θ (W.MY k) (W.MY (k + 1)) (W.ωY k) (W.ptY k) (W.ItY k)
  ItX : IsItW W.θ (W.MY (D.R.m - 1)) W.MX W.ωX W.ptX W.ItX

structure Is : Prop extends W.Pre where
  ioY : Lift.IsChainIo W.CC (D.R.m - 1) W.νY W.fdY (fun k => thetaKO (W.ωY k)) W.ptY W.ItY W.ioY
  ioX : Lift.IsIo W.νX W.fdX (thetaKO W.ωX) W.ptX W.ItX _ _ W.ioX

def thDn : W.CX →ₗ[ℂ] W.CC 0 := Lift.thetaDn W.CC W.ioY (D.R.m - 1) ∘ₗ W.ioX

def IsDn (T : SmT W.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) (T₀ : SmT (W.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) : Prop :=
  ∃ h : T ∈ W.CX, T₀ = (W.thDn ⟨T, h⟩ : W.CC 0)

def DnLev (P : W.Lv) : Prop := ∀ T ∈ W.CXP P, ∃ T₀ ∈ W.CP P 0, W.IsDn T T₀

def Onto (P : W.Lv) : Prop := ∀ T₀ ∈ W.CP P 0, ∃ T ∈ W.CXP P, W.IsDn T T₀

def Onto1 : Prop := Function.Surjective W.thDn

def StepsOnto : Prop := (∀ k, k + 1 < D.R.m → Function.Surjective (W.ioY k)) ∧ Function.Surjective W.ioX

end Tower

end GlobalTheory.Core.Rk

end
