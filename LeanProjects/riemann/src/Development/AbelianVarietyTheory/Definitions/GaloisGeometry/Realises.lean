import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
import Formalism.LocalToGlobal.InertKernelTheory.ProjRSurj
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts

noncomputable section

namespace GlobalTheory.TwV.DelA

open Formalism.BasicNotions NumberField Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG
open Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

def posJ : ∀ j, (Σ v : Fin (X.Pj j).nV, Fin ((X.Pj j).n' v)) ≃ D.what₂.Tau
  | 0 => pos
  | _ + 1 => pos

def wT (j : ℕ) (τ : D.what₂.Tau) : ℤ := X.w (pos.symm τ).1 (j + 1) (pos.symm τ).2

abbrev Fr1 (n : ℕ) : Type := Frames (fun _ : D.what₂.Tau => (1 : Matrix (Fin n) (Fin n) ℂ))

abbrev ev1 (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) : XR (X.Pj i) ℂ →ₗ[ℂ] (Fr1 D n → ℂ) :=
  evC (X.Pj i) h (posJ X D pos i) (fun _ => 1) (fun _ => 1)

def Realises (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (a : D.what₂.Tau → ℤ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (R : XR (X.Pj i) ℂ) : Prop :=
  ∀ f : Fr1 D n, ev1 X D pos i h R f = (∏ τ, (f.1 τ).det ^ (-(a τ))) * GL3Theta.evFr D Q f.1

def relPhi (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (a : D.what₂.Tau → ℤ) :
    Submodule ℂ (MvPolynomial (GL3Theta.FrV D n) ℂ × XR (X.Pj i) ℂ) where
  carrier := {q | Realises X D pos i h a q.1 q.2}
  add_mem' := by
    intro x y hx hy f
    have h1 := hx f
    have h2 := hy f
    simp only [GL3Theta.evFr, Prod.fst_add, Prod.snd_add, map_add, Pi.add_apply] at h1 h2 ⊢
    rw [h1, h2, mul_add]
  zero_mem' := by
    intro f
    simp only [GL3Theta.evFr, Prod.fst_zero, Prod.snd_zero, map_zero, Pi.zero_apply, mul_zero]
  smul_mem' := by
    intro r x hx f
    have h1 := hx f
    simp only [GL3Theta.evFr, Prod.smul_fst, Prod.smul_snd, map_smul, Pi.smul_apply, smul_eq_mul, MvPolynomial.smul_eval] at h1 ⊢
    rw [h1]
    ring

def phiC (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (a : D.what₂.Tau → ℤ) : MvPolynomial (GL3Theta.FrV D n) ℂ →ₗ[ℂ] XR (X.Pj i) ℂ :=
  selOf (relPhi X D pos i h a)

open Classical in

def phi0 {Kc : Type} [Field Kc] (ι : ℂ →+* Kc) (j : ℕ) :
    MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →ₛₗ[ι] XspC (X.Pj (j + 1)) Kc :=
  if h : (X.Pj (j + 1)).m + 1 = D.R.N (j + 1) then (mapSL ι).comp (phiC X D pos (j + 1) h (wT X D pos j)) else 0

def NuIs (j : ℕ) {n : ℕ} (ν : D.what₂.Tau → Fin n → ℕ) : Prop :=
  ∀ τ (i : Fin n), X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (i.val + 1) = (ν τ i : ℤ)

def szT (j : ℕ) (τ : D.what₂.Tau) : ℤ := szMu X j (pos.symm τ).1 (pos.symm τ).2

def sgRev (n : ℕ) : ℂ := ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ)

def sgO (j : ℕ) : ℂ :=
  ∏ τ, if IsOddPos (pos.symm τ).2 then (sgRev (D.R.N j) * sgRev (D.R.N (j + 1))) ^ wT X D pos j τ else 1

def cOp (j : ℕ) (s : D.what₂.Tau → ℂ) : ℂ := sgO X D pos j * ∏ τ, s τ ^ (-(szT X D pos j τ))

def PosTie (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v) : Prop :=
  ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : D.host.E),
    ι (embT D (pos ⟨v, s⟩) x) = Formalism.L2.G.Pend.tw X Kc v s (ρ v (if IsOddPos s then star x else x))

def StdU {n : ℕ} (M : GL (Fin n) D.host.E) : Prop := star (M : Matrix (Fin n) (Fin n) D.host.E) * (M : Matrix (Fin n) (Fin n) D.host.E) = 1

def atR {n : ℕ} (M : GL (Fin n) D.host.E) : D.what₂.Tau → GL (Fin n) ℂ := fun τ => Matrix.GeneralLinearGroup.map (embT D τ) M

def actC (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (M : GL (Fin n) D.host.E) : XR (X.Pj i) ℂ →ₗ[ℂ] XR (X.Pj i) ℂ :=
  natActR (X.Pj i) ℂ (hAt (X.Pj i) h (posJ X D pos i) (fun _ => 1) (atR D M))

variable {X D}

def FrIs (fd : FData X D) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v) (j : ℕ) (La : X.Lt j) {n : ℕ} (h : (X.Pj j).m + 1 = n)
    (M : GL (Fin n) D.host.E) : Prop :=
  ∀ v, fd.frM j La v = (((M : Matrix (Fin n) (Fin n) D.host.E)).map (ρ v)).submatrix (finCongr h) (finCongr h)

def gmOf (fd : FData X D) (j : ℕ) (La : X.Lt j) (G : (X.Pj j).Xsp) : (X.Pj j).Xsp :=
  (X.Pj j).natAct (fun v => (SecondKernelHermitian.glInv X j (SecondKernelHermitian.BOf fd j La) v)⁻¹) G

variable (X D)

structure WtOK (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ) : Prop where
  rk : RankTie X D j
  nu : NuIs X D pos j (nuT D u j)
  sh : ∀ τ, wT X D pos j τ = (D.chTw u μ).sSharp j τ - CmpJ.cTw D j
  dv : ∀ τ, wT X D pos j τ = (D.chTw u μ).sDiv j τ - CmpJ.cTw D (j + 1)

end GlobalTheory.TwV.DelA

end
