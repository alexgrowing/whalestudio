import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalRingCardinality.PrincipalHermitianLattice
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix IsDedekindDomain NumberField
open Formalism.L2.Theta
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.RecTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {N : Type*} [AddCommGroup N] [Module ℂ N]

def HilbTie (C : Submodule ℂ N) (ip : N → N → ℂ) (j : X ≃ₗ[ℂ] C) : Prop :=
  ∀ x y, ⟪x, y⟫_ℂ = ip (j x) (j y)

def ProjTie {Y : Type*} (C : Submodule ℂ N) (ip : N → N → ℂ) (j : X ≃ₗ[ℂ] C) (f : Y → X) (g : Y → N) : Prop :=
  ∀ x y, ⟪x, f y⟫_ℂ = ip (j x) (g y)

theorem ProjTie.eq_of_mem {Y : Type*} {C : Submodule ℂ N} {ip : N → N → ℂ} {j : X ≃ₗ[ℂ] C} {f : Y → X} {g : Y → N}
    (hH : HilbTie C ip j) (hP : ProjTie C ip j f g) (y : Y) (hy : g y ∈ C) : ((j (f y) : C) : N) = g y := by
  have h1 : f y = j.symm ⟨g y, hy⟩ := by
    refine ext_inner_left ℂ fun x => ?_
    rw [hP x y, hH x (j.symm ⟨g y, hy⟩), LinearEquiv.apply_symm_apply]
  rw [h1, LinearEquiv.apply_symm_apply]

theorem hilbTie_top : HilbTie (⊤ : Submodule ℂ X) (fun a b => ⟪a, b⟫_ℂ) (Submodule.topEquiv.symm) :=
  fun _ _ => rfl

end Gen

section Pair

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

abbrev AmbT (M : Mult.DSModel V S) : Type := (⨂[ℂ] τ, M.sm τ) →ₗ[ℂ] (GA D V → ℂ)

def ipMT (M : Mult.DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (x y : AmbT M) : ℂ :=
  Mult.ipM M μ 𝓕 (PiTensorProduct.lift.symm x) (PiTensorProduct.lift.symm y)

def ipWT {W : HSp D} {κ : ∀ τ : D.what₂.Tau, Fin (W.sig (tauE D τ)).1 ⊕ Fin (W.sig (tauE D τ)).2 → ℤ}
    (M : Mult.DSModel W (Mult.parW W κ)) (μ : Measure (GA D W)) (𝓕 : Set (GA D W)) (x y : AmbT M) : ℂ :=
  Mult.ipW M μ 𝓕 (PiTensorProduct.lift.symm x) (PiTensorProduct.lift.symm y)

end Pair

structure ChainReal (D : D7) where

  θ : Datum.InfFam D

  ψ : AddChar (AF D.host.F) ℂ

  η : (AE D)ˣ →* Circle

  Ptw : TPar D

  Y : ℕ → HSp D

  SY : ℕ → D.what₂.Tau → SPar

  MY : ∀ j, Mult.DSModel (Y j) (SY j)

  X : HSp D

  MX : Mult.DSModel X (Mult.parB Ptw D.R.m)

  J : Bool → D.what₂.Tup → ∀ j, Set (GA D (Y j))

  χ : Bool → D.what₂.Tup → ∀ j, GA D (Y j) → ℂ

  JX : Bool → D.what₂.Tup → Set (GA D X)

  χX : Bool → D.what₂.Tup → GA D X → ℂ

  meas : Bool → D.what₂.Tup → ∀ j, Measure (GA D (Y j))

  fd : D.what₂.Tup → ∀ j, Set (GA D (Y j))

  measX : Bool → D.what₂.Tup → Measure (GA D X)

  fdX : D.what₂.Tup → Set (GA D X)

  measE : Bool → Measure (GA D (Y 0))
  fdE : Set (GA D (Y 0))

  chr : D.what₂.Tup → ℕ → (AE D)ˣ →* Circle

  Sinf : ℕ → Type
  [acgS : ∀ k, AddCommGroup (Sinf k)]
  [modS : ∀ k, Module ℂ (Sinf k)]

  pt : Bool → D.what₂.Tup → ∀ k, Sinf k → (Datum.WO (Y k) (Y (k + 1)) → ℂ)

  It : ∀ k, Sinf k →ₗ[ℂ] (⨂[ℂ] τ, (MY (k + 1)).sm τ) →ₗ[ℂ] (⨂[ℂ] τ, (MY k).sm τ)

  th : D.what₂.Tup → ∀ k, GA D (Y k) → GA D (Y (k + 1)) → (Datum.WO (Y k) (Y (k + 1)) → ℂ) → ℂ

  ioC : ∀ b μ k, Mult.MultT θ (MY (k + 1)) (J b μ (k + 1)) (χ b μ (k + 1)) →ₗ[ℂ]
    Mult.MultT θ (MY k) (J b μ k) (χ b μ k)

  SinfX : Type
  [acgX : AddCommGroup SinfX]
  [modX : Module ℂ SinfX]

  ptX : Bool → D.what₂.Tup → SinfX → (Datum.WO (Y (D.R.m - 1)) X → ℂ)

  ItX : SinfX →ₗ[ℂ] (⨂[ℂ] τ, MX.sm τ) →ₗ[ℂ] (⨂[ℂ] τ, (MY (D.R.m - 1)).sm τ)

  thX : D.what₂.Tup → GA D (Y (D.R.m - 1)) → GA D X → (Datum.WO (Y (D.R.m - 1)) X → ℂ) → ℂ

  ioX : ∀ b μ, Mult.MultT θ MX (JX b μ) (χX b μ) →ₗ[ℂ]
    Mult.MultT θ (MY (D.R.m - 1)) (J b μ (D.R.m - 1)) (χ b μ (D.R.m - 1))

  JE : Bool → Set (GA D (Y 0))

  χE : Bool → GA D (Y 0) → ℂ

  eE : Bool → (GA D (Y 0) → ℂ) →ₗ[ℂ] (GA D (Y 0) → ℂ)

  Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))

  volTop : ℝ

  JP : Bool → D.what₂.Tup → ∀ j, Set (GA D (Y j))

  χP : Bool → D.what₂.Tup → ∀ j, GA D (Y j) → ℂ

  JXP : Bool → D.what₂.Tup → Set (GA D X)

  χXP : Bool → D.what₂.Tup → GA D X → ℂ

  nrm : Bool → ℝ

attribute [instance] ChainReal.acgS ChainReal.modS ChainReal.acgX ChainReal.modX

namespace ChainReal

variable {D : D7} (C : ChainReal D)

abbrev Amb (j : ℕ) : Type := AmbT (C.MY j)

abbrev AmbX : Type := AmbT C.MX

abbrev CC (b : Bool) (μ : D.what₂.Tup) (j : ℕ) : Submodule ℂ (C.Amb j) :=
  Mult.MultT C.θ (C.MY j) (C.J b μ j) (C.χ b μ j)

abbrev CCX (b : Bool) (μ : D.what₂.Tup) : Submodule ℂ C.AmbX :=
  Mult.MultT C.θ C.MX (C.JX b μ) (C.χX b μ)

def ip (b : Bool) (μ : D.what₂.Tup) (j : ℕ) (x y : C.Amb j) : ℂ := ipMT (C.MY j) (C.meas b μ j) (C.fd μ j) x y

abbrev CCP (b : Bool) (μ : D.what₂.Tup) (j : ℕ) : Submodule ℂ (C.Amb j) :=
  Mult.MultT C.θ (C.MY j) (C.JP b μ j) (C.χP b μ j)

abbrev CCXP (b : Bool) (μ : D.what₂.Tup) : Submodule ℂ C.AmbX :=
  Mult.MultT C.θ C.MX (C.JXP b μ) (C.χXP b μ)

def ipX (b : Bool) (μ : D.what₂.Tup) (x y : C.AmbX) : ℂ :=
  (((∏ τ, (Module.finrank ℂ (C.MX.H τ) : ℝ)) / C.volTop : ℝ) : ℂ) * ipMT C.MX (C.measX b μ) (C.fdX μ) x y

def ipP (b : Bool) (μ : D.what₂.Tup) (j : ℕ) (x y : C.Amb j) : ℂ := (C.nrm b : ℂ) * C.ip b μ j x y

def ipXP (b : Bool) (μ : D.what₂.Tup) (x y : C.AmbX) : ℂ := (C.nrm b : ℂ) * C.ipX b μ x y

def ipE (b : Bool) (x y : C.Amb 0) : ℂ := ipMT (C.MY 0) (C.measE b) C.fdE x y

def EEc (b : Bool) : Submodule ℂ (C.Amb 0) :=
  (Mult.goodPart C.θ (C.MY 0) (C.JE b) (C.χE b) (C.eE b)).map
    (PiTensorProduct.lift : Mult.MMap (C.MY 0) ≃ₗ[ℂ] C.Amb 0).toLinearMap

def IoOK (b : Bool) (μ : D.what₂.Tup) : Prop :=
  Lift.IsChainIo (G := fun j => GA D (C.Y j)) (D := fun j => ⨂[ℂ] τ, (C.MY j).sm τ)
    (C.CC b μ) (D.R.m - 1) (C.meas b μ) (C.fd μ) (C.th μ) (C.pt b μ) C.It (C.ioC b μ) ∧
  (1 ≤ D.R.m → Lift.IsIo (C.measX b μ) (C.fdX μ) (C.thX μ) (C.ptX b μ) C.ItX (C.CCX b μ) (C.CC b μ (D.R.m - 1))
    (C.ioX b μ))

def partE (b : Bool) (c : HeightOneSpectrum (𝓞 D.host.E) → ℕ → ℂ) : Submodule ℂ (C.Amb 0) :=
  (Mult.part C.θ (C.MY 0) (C.JE b) (C.χE b) C.Sb c).map
    (PiTensorProduct.lift : Mult.MMap (C.MY 0) ≃ₗ[ℂ] C.Amb 0).toLinearMap

end ChainReal

def Used0 (D : D7) (μ : D.what₂.Tup) : Prop := μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w

section Rows

variable {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]

structure RowIds (X : RowSide D EE) (C : ChainReal D) (b : Bool) where

  jE : EE ≃ₗ[ℂ] C.EEc b

  jM : ∀ μ, Used0 D μ → ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m - 1 → (X.Mult μ j ≃ₗ[ℂ] C.CCP b μ j)

  jX : ∀ μ, Used0 D μ → (X.Mult μ D.R.m ≃ₗ[ℂ] C.CCXP b μ)

  prt : D.what₂.FT → Submodule ℂ (C.Amb 0)

structure RowSideReal (X : RowSide D EE) (C : ChainReal D) (b : Bool) (I : RowIds X C b) {n : ℕ}
    (bs : OrthonormalBasis (Fin n) ℂ EE) (ty : Fin n → D.what₂.FT) : Prop where

  parY : ∀ j, j ≤ D.R.m - 1 → C.SY j = Mult.parB C.Ptw j

  lvl : ∀ μ, Used0 D μ → C.EEc b ≤ C.CC b μ 0

  lvlP : ∀ μ, Used0 D μ → ∀ j, 1 ≤ j → j ≤ D.R.m - 1 → C.CCP b μ j ≤ C.CC b μ j

  lvlX : ∀ μ, Used0 D μ → C.CCXP b μ ≤ C.CCX b μ

  ee : HilbTie (C.EEc b) (C.ipE b) I.jE

  mult : ∀ μ (hμ : Used0 D μ) j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m - 1), HilbTie (C.CCP b μ j) (C.ipP b μ j) (I.jM μ hμ j h1 h2)

  multX : 1 ≤ D.R.m → ∀ μ (hμ : Used0 D μ), HilbTie (C.CCXP b μ) (C.ipXP b μ) (I.jX μ hμ)

  io0 : ∀ (h : 2 ≤ D.R.m) μ (hμ : Used0 D μ), C.IoOK b μ → ProjTie (C.EEc b) (C.ipE b) I.jE
    (fun x : X.Mult μ 1 => X.multZero μ (X.io μ 0 x))
    (fun x => ((C.ioC b μ 0 (Submodule.inclusion (lvlP μ hμ 1 le_rfl (by omega)) (I.jM μ hμ 1 le_rfl (by omega) x)) :
      C.CC b μ 0) : C.Amb 0))

  io0X : ∀ (h : D.R.m = 1) μ (hμ : Used0 D μ), C.IoOK b μ → ProjTie (C.EEc b) (C.ipE b) I.jE
    (fun x : X.Mult μ 1 => X.multZero μ (X.io μ 0 x))
    (fun x => cast (congrArg C.Amb (show D.R.m - 1 = 0 by omega))
      ((C.ioX b μ (Submodule.inclusion (lvlX μ hμ) (I.jX μ hμ (cast (congrArg (X.Mult μ) h.symm) x))) :
        C.CC b μ (D.R.m - 1)) : C.Amb (D.R.m - 1)))

  io : ∀ μ (hμ : Used0 D μ), C.IoOK b μ → ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j + 1 ≤ D.R.m - 1),
    ProjTie (C.CCP b μ j) (C.ipP b μ j) (I.jM μ hμ j h1 (by omega)) (fun x : X.Mult μ (j + 1) => X.io μ j x)
      (fun x => ((C.ioC b μ j (Submodule.inclusion (lvlP μ hμ (j + 1) (by omega) h2) (I.jM μ hμ (j + 1) (by omega) h2 x)) :
        C.CC b μ j) : C.Amb j))

  ioTop : ∀ (h : 2 ≤ D.R.m) μ (hμ : Used0 D μ), C.IoOK b μ →
    ProjTie (C.CCP b μ (D.R.m - 1)) (C.ipP b μ (D.R.m - 1)) (I.jM μ hμ (D.R.m - 1) (by omega) le_rfl)
      (fun x : X.Mult μ D.R.m => X.io μ (D.R.m - 1) (cast (congrArg (X.Mult μ) (by omega)) x))
      (fun x => ((C.ioX b μ (Submodule.inclusion (lvlX μ hμ) (I.jX μ hμ x)) : C.CC b μ (D.R.m - 1)) : C.Amb (D.R.m - 1)))

  ft : ∀ σ, ((I.jE (bs σ) : C.EEc b) : C.Amb 0) ∈ I.prt (ty σ)

  prt_disj : ∀ π π', π ≠ π' → I.prt π ⊓ I.prt π' = ⊥

structure RowSideKer (C : ChainReal D) (b : Bool) : Prop where

  isIo : ∀ μ, Lift.IsChainIo (G := fun j => GA D (C.Y j)) (D := fun j => ⨂[ℂ] τ, (C.MY j).sm τ)
    (C.CC b μ) (D.R.m - 1) (C.meas b μ) (C.fd μ) (C.th μ) (C.pt b μ) C.It (C.ioC b μ)

  isIoX : 1 ≤ D.R.m → ∀ μ, Lift.IsIo (C.measX b μ) (C.fdX μ) (C.thX μ) (C.ptX b μ) C.ItX (C.CCX b μ)
    (C.CC b μ (D.R.m - 1)) (C.ioX b μ)

  kernel : ∀ μ, Lift.IsChainKernel C.ψ (C.chr μ) C.η (D.R.m - 1) C.Y (C.th μ)

  kernelX : 1 ≤ D.R.m → ∀ μ, Lift.IsStepKernel C.ψ (C.chr μ) C.η D.R.m (C.Y (D.R.m - 1)) C.X (C.thX μ)

  chars : ∀ μ, Lift.CharsOK (C.chr μ) C.η D.R.m

  ptTh : ∀ μ k, k + 1 < D.R.m → Lift.PtTheta C.ψ (C.Y k) (C.Y (k + 1)) (C.pt b μ k)

  ptThX : 1 ≤ D.R.m → ∀ μ, Lift.PtTheta C.ψ (C.Y (D.R.m - 1)) C.X (C.ptX b μ)

end Rows

structure LiftReal (D : D7) (C : ChainReal D) where

  V : Fin D.R.m → HSp D

  W : Fin D.R.m → HSp D

  κ : ∀ i (τ : D.what₂.Tau), Fin ((W i).sig (tauE D τ)).1 ⊕ Fin ((W i).sig (tauE D τ)).2 → ℤ

  SW : Fin D.R.m → D.what₂.Tau → SPar

  MW : ∀ i, Mult.DSModel (W i) (SW i)

  JW : ∀ i, Set (GA D (W i))

  χW : ∀ i, GA D (W i) → ℂ

  eW : ∀ i, (GA D (W i) → ℂ) →ₗ[ℂ] (GA D (W i) → ℂ)

  JA : ∀ i, Set (GA D (W i))

  χA : ∀ i, GA D (W i) → ℂ

  measW : ∀ i, Measure (GA D (W i))

  fdW : ∀ i, Set (GA D (W i))

  SbW : Finset (HeightOneSpectrum (𝓞 D.host.F))

  TauV : Fin D.R.m → Type
  [acgT : ∀ i, AddCommGroup (TauV i)]
  [modT : ∀ i, Module ℂ (TauV i)]

  Amt : D.what₂.Tup → ∀ i, Submodule ℂ (GA D (V i) → TauV i)

  ipA : D.what₂.Tup → ∀ i, (GA D (V i) → TauV i) → (GA D (V i) → TauV i) → ℂ

  measV : D.what₂.Tup → ∀ i, Measure (GA D (V i))

  fdV : D.what₂.Tup → ∀ i, Set (GA D (V i))

  TK : Fin D.R.m → Type
  [acgK : ∀ i, AddCommGroup (TK i)]
  [modK : ∀ i, Module ℂ (TK i)]

  embK : ∀ i, TK i →ₗ[ℂ] ⨂[ℂ] τ, (MW i).sm τ

  Sinf' : Fin D.R.m → Type
  [acgP : ∀ i, AddCommGroup (Sinf' i)]
  [modP : ∀ i, Module ℂ (Sinf' i)]

  ioK : ∀ i, TK i →ₗ[ℂ] TauV i →ₗ[ℂ] Sinf' i

  ptW : D.what₂.Tup → ∀ i, Sinf' i → (Datum.WO (V i) (W i) → ℂ)

  thW : D.what₂.Tup → ∀ i, GA D (W i) → GA D (V i) → (Datum.WO (V i) (W i) → ℂ) → ℂ

  thC : ∀ μ i, Amt μ i →ₗ[ℂ] (TK i →ₗ[ℂ] (GA D (W i) → ℂ))

attribute [instance] LiftReal.acgT LiftReal.modT LiftReal.acgK LiftReal.modK LiftReal.acgP LiftReal.modP

namespace LiftReal

variable {D : D7} {C : ChainReal D} (L : LiftReal D C)

abbrev AmbW (i : Fin D.R.m) : Type := AmbT (L.MW i)

abbrev MultW (i : Fin D.R.m) : Submodule ℂ (L.AmbW i) := Mult.MultT C.θ (L.MW i) (L.JA i) (L.χA i)

def Wc (i : Fin D.R.m) : Submodule ℂ (L.AmbW i) :=
  (Mult.goodPart C.θ (L.MW i) (L.JW i) (L.χW i) (L.eW i)).map
    (PiTensorProduct.lift : Mult.MMap (L.MW i) ≃ₗ[ℂ] L.AmbW i).toLinearMap

def ipWc (i : Fin D.R.m) (x y : L.AmbW i) : ℂ :=
  (∏ τ, ((Mult.dimK _ _ (L.κ i τ) : ℚ) : ℂ)) * ipMT (L.MW i) (L.measW i) (L.fdW i) x y

def partW (i : Fin D.R.m) (c : HeightOneSpectrum (𝓞 D.host.E) → ℕ → ℂ) : Submodule ℂ (L.AmbW i) :=
  (Mult.part C.θ (L.MW i) (L.JW i) (L.χW i) L.SbW c).map
    (PiTensorProduct.lift : Mult.MMap (L.MW i) ≃ₗ[ℂ] L.AmbW i).toLinearMap

end LiftReal

section Lifts

variable {D : D7} {C : ChainReal D}

structure LiftIds (L : LiftReal D C) where

  jMj : ∀ i : Fin D.R.m, D.what₂.Mj (i + 1) ≃ₗ[ℂ] L.Wc i

  jMt : ∀ μ, Used0 D μ → ∀ (i : Fin D.R.m), D.what₂.Mt μ (i + 1) ≃ₗ[ℂ] L.Amt μ i

  prtW : ∀ i : Fin D.R.m, D.what₂.FT → Submodule ℂ (L.AmbW i)

structure LiftTie (L : LiftReal D C) (I : LiftIds L) : Prop where

  hol : ∀ i, L.SW i = Mult.parW (L.W i) (L.κ i)

  mj : ∀ i, HilbTie (L.Wc i) (L.ipWc i) (I.jMj i)

  mt : ∀ μ (hμ : Used0 D μ) i, HilbTie (L.Amt μ i) (L.ipA μ i) (I.jMt μ hμ i)

  theta : ∀ μ (hμ : Used0 D μ) (i : Fin D.R.m) (x : D.what₂.Mt μ (i + 1)) (w : L.AmbW i),
    Lift.IsThetaP (L.measV μ i) (L.fdV μ i) (L.thW μ i) (L.ptW μ i) (L.ioK i) (L.Amt μ i) (L.thC μ i) → w ∈ L.MultW i →
    w ∘ₗ L.embK i = L.thC μ i (I.jMt μ hμ i x) → L.eW i ∘ₗ w ∈ L.Wc i →
    ((I.jMj i (D.what₂.thetaP μ (i + 1) x) : L.Wc i) : L.AmbW i) = L.eW i ∘ₗ w

  isot : ∀ (i : Fin D.R.m) π y, y ∈ D.what₂.isot (i + 1) π ↔
    ((I.jMj i y : L.Wc i) : L.AmbW i) ∈ I.prtW i π

  prtW_disj : ∀ i π π', π ≠ π' → I.prtW i π ⊓ I.prtW i π' = ⊥

  lamP : ∀ μ, Used0 D μ → ∀ (i : Fin D.R.m) π (c : ℝ), D.what₂.isot (i + 1) π ≠ ⊥ →
    (∀ y ∈ D.what₂.isot (i + 1) π, D.what₂.thetaP μ (i + 1) (D.what₂.thetaT μ (i + 1) y) = (c : ℂ) • y) →
    D.what₂.lamP μ (i + 1) π = c

structure LiftKer (L : LiftReal D C) : Prop where

  thP : ∀ μ i, Lift.IsThetaP (L.measV μ i) (L.fdV μ i) (L.thW μ i) (L.ptW μ i) (L.ioK i) (L.Amt μ i) (L.thC μ i)

  ptTh : ∀ μ i, Lift.PtTheta C.ψ (L.V i) (L.W i) (L.ptW μ i)

  kerP : ∀ μ (i : Fin D.R.m), Lift.IsThPKernel C.ψ (C.chr μ) C.η (i + 1) (L.V i) (L.W i) (L.thW μ i)

end Lifts

structure ColReal (D : D7) where

  xi : D.what₂.Tup → (AE D)ˣ →* Circle

structure ColTieR {D : D7} (C : ChainReal D) (K : ColReal D) : Prop where

  tup : ∀ μ, Used0 D μ → ∀ j, 1 ≤ j → j ≤ D.R.m → C.chr μ j = Lift.tup (C.chr D.what₂.mu0) (K.xi μ) j

  xi0 : K.xi D.what₂.mu0 = 1

  bu : ∀ u, (∀ φ F, F ∈ D.what₂.V0 D.what₂.mu0 → D.what₂.iota D.what₂.mu0 F = 0 → D.what₂.perCol u D.what₂.mu0 φ F = 0) →
    ∀ φ F, F ∈ D.what₂.V0 D.what₂.mu0 → D.what₂.perCol u D.what₂.mu0 φ F = D.what₂.Bu u φ (D.what₂.iota D.what₂.mu0 F)

structure RecTied (D : D7) (X0 : BaseLevelRowSide D) (C : ChainReal D) (Ish : RowIds (RowSide.sharp D) C true)
    (I0 : RowIds X0.s C false) (L : LiftReal D C) (IL : LiftIds L) (K : ColReal D) : Prop where

  sharp : RowSideReal (RowSide.sharp D) C true Ish D.what₂.onb D.what₂.ft

  base : RowSideReal X0.s C false I0 D.what₂.onb0 D.what₂.ft0

  lift : LiftTie L IL

  col : ColTieR C K

structure LatReal (D : D7) (C : ChainReal D) (L : LiftReal D C) where

  Ks : Type
  [fKs : Field Ks]
  [nKs : NumberField Ks]
  [aKs : Algebra Ks D.what₂.LL]

  WL : ℕ → Type
  [acgW : ∀ j, AddCommGroup (WL j)]
  [mLL : ∀ j, Module D.what₂.LL (WL j)]
  [mKs : ∀ j, Module Ks (WL j)]
  [tKs : ∀ j, IsScalarTower Ks D.what₂.LL (WL j)]
  [mO : ∀ j, Module (𝓞 D.what₂.LL) (WL j)]
  [tO : ∀ j, IsScalarTower (𝓞 D.what₂.LL) D.what₂.LL (WL j)]
  [mOK : ∀ j, Module (𝓞 Ks) (WL j)]
  [tOK : ∀ j, IsScalarTower (𝓞 Ks) Ks (WL j)]

  Wσ : ℕ → (D.what₂.LL →+* ℂ) → Type
  [nW : ∀ j σ, NormedAddCommGroup (Wσ j σ)]
  [iW : ∀ j σ, InnerProductSpace ℂ (Wσ j σ)]

  G0 : Type
  [gG : Group G0]
  [fG : Fintype G0]

  A : ∀ j, Arith.FormsL D.what₂.LL Ks (WL j) (Wσ j) G0

  J0 : Subgroup G0
  lam0 : J0 →* D.what₂.LLˣ

  eC : G0 → D.what₂.LL

  eG : G0 ≃* Formalism.BasicNotions.G0g D.nd

  jL : ∀ j : Fin D.R.m, (A (j + 1)).Wgood J0 lam0 eC →ₛₗ[D.what₂.embLL] D.what₂.Mj (j + 1)

  eWc : ∀ i : Fin D.R.m, Wσ (i + 1) D.what₂.embLL →ₗ[ℂ] L.AmbW i

attribute [instance] LatReal.fKs LatReal.nKs LatReal.aKs LatReal.acgW LatReal.mLL LatReal.mKs LatReal.tKs LatReal.mO
  LatReal.tO LatReal.mOK LatReal.tOK LatReal.nW LatReal.iW LatReal.gG LatReal.fG

structure LatTie {D : D7} {C : ChainReal D} {L : LiftReal D C} (IL : LiftIds L) (Q : LatReal D C L) : Prop where

  e0 : ∀ g, D.what₂.embLL (Q.eC g) = D.ntypes.e0.coeff (Q.eG g)

  ana : ∀ (j : Fin D.R.m) (x : (Q.A (j + 1)).Wgood Q.J0 Q.lam0 Q.eC),
    ((IL.jMj j (Q.jL j x) : L.Wc j) : L.AmbW j) = Q.eWc j ((Q.A (j + 1)).j D.what₂.embLL x)

  gen : ∀ (j : Fin D.R.m), ∀ v ∈ (D.what₂.MjLat (j + 1)).gen, v ∈ Set.range (Q.jL j)

  lat : ∀ (j : Fin D.R.m) (x : (Q.A (j + 1)).Wgood Q.J0 Q.lam0 Q.eC), (x : Q.WL (j + 1)) ∈ (Q.A (j + 1)).Mj Q.J0 Q.lam0 Q.eC ↔
    ∃ c : D.what₂.Mj (j + 1) → 𝓞 D.what₂.LL,
      Q.jL j x = ∑ v ∈ (D.what₂.MjLat (j + 1)).gen, D.what₂.embLL (c v : D.what₂.LL) • v

end Formalism.IndefR.RecTie

end
