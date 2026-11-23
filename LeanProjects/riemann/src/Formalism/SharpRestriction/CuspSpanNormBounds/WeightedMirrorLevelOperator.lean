import Formalism.SharpRestriction.CuspSpanNormBounds.AuxiliarySlotStates

noncomputable section

namespace Formalism.MainNotions.S.LevR

open Formalism.QuantumDeterminants

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Dr {r : ℕ} (x : Fin (r + 1) → ℂ) : ℂ := ∏ a : Fin r, cOf x a

def Dr1 {r : ℕ} (x : Fin (r + 1) → ℂ) : ℂ := Dr x * zOf x

def GG {r : ℕ} (T T' : ℝ) (x : Fin (r + 1) → ℂ) : ℂ := ((Complex.normSq (zOf x) - T * T' : ℝ) : ℂ)

def Gfn {r : ℕ} (T T' : ℝ) (x : Fin (r + 1) → ℂ) : ℂ :=
  ((Complex.normSq (Dr x) : ℝ) : ℂ) * GG T T' x

def mulF {m : ℕ} (f : (Fin m → ℂ) → ℂ) : Op m E := fun φ x => f x • φ x

def mulE {m : ℕ} (e : (Fin m → ℂ) → E →L[ℂ] E) : Op m E := fun φ x => e x (φ x)

def one {m : ℕ} : Op m E := fun φ => φ

def vecT {m : ℕ} (M : Matrix (Fin 2) (Fin 2) (Op m E)) (v : Fin 2 → Op m E) : Fin 2 → Op m E :=
  fun a => ∑ b : Fin 2, M a b ∘ v b

def vv {r : ℕ} (Y : ℂ) : (i : ℕ) → i ≤ r → Fin 2 → Op (r + 1) E
  | 0, _ => ![one, 0]
  | i + 1, h => vecT (Tmat (⟨i, by omega⟩ : Fin (r + 1)) Y) (vv Y i (by omega))

def vvV {r : ℕ} (Y : ℂ) : (i : ℕ) → i ≤ r → Fin 2 → Op (r + 1) E
  | 0, _ => ![one, 0]
  | i + 1, h => vecT (TmatV (⟨i, by omega⟩ : Fin (r + 1)) Y) (vvV Y i (by omega))

def Ar (r : ℕ) (Y : ℂ) : Op (r + 1) E := vv Y r le_rfl 0

def Br (r : ℕ) (Y : ℂ) : Op (r + 1) E := vv Y r le_rfl 1

def ArV (r : ℕ) (Y : ℂ) : Op (r + 1) E := vvV Y r le_rfl 0

def BrV (r : ℕ) (Y : ℂ) : Op (r + 1) E := vvV Y r le_rfl 1

def Ahat (r : ℕ) (Y : ℂ) : Op (r + 1) E := mulF Dr ∘ Ar r Y

def AhatV (r : ℕ) (Y : ℂ) : Op (r + 1) E := mulF (fun x => star (Dr x)) ∘ ArV r Y

def Rhat (r : ℕ) (Q : ℂ → Matrix (Fin 2) (Fin 2) (Op (r + 1) E)) (Y : ℂ) : Op (r + 1) E :=
  mulF (fun x => star (Dr x)) ∘ (Q Y 1 0 ∘ Ar r Y + Q Y 1 1 ∘ Br r Y)

def dZ (r : ℕ) : Op (r + 1) E := wirt (Fin.last r)

def dZb (r : ℕ) : Op (r + 1) E := wirtBar (Fin.last r)

def nabla (r : ℕ) (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Op (r + 1) E := dZ r + mulE h

def l0 (r : ℕ) (T T' : ℝ) (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) : Op (r + 1) E :=
  -nabla r h - mulF (fun x => (Y + 1 / 2) * star (zOf x) / GG T T' x)

def m0 (r : ℕ) (T T' : ℝ) (hs : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) : Op (r + 1) E :=
  dZb r - mulE hs - mulF (fun x => (Y - 1 / 2) * zOf x / GG T T' x)

section Lines

variable {k0 : ℕ} {Rho : Type*}

def xFib {r : ℕ} (ρp : Rho → Fin k0 → ℝ) (P : Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) :
    (Fin (r + 1) → ℂ) → E →L[ℂ] E :=
  fun x => ∑ᶠ ρ, xPoly (ρp ρ) Y • P ρ x

def xInvFib {r : ℕ} (ρp : Rho → Fin k0 → ℝ) (P : Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) :
    (Fin (r + 1) → ℂ) → E →L[ℂ] E :=
  fun x => ∑ᶠ ρ, (xPoly (ρp ρ) Y)⁻¹ • P ρ x

def shInv {r : ℕ} (ρp : Rho → Fin k0 → ℝ) (P : Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E) (l : Fin k0)
    (Y : ℂ) : (Fin (r + 1) → ℂ) → E →L[ℂ] E :=
  fun x => ∑ᶠ ρ, (Y + (ρp ρ l : ℂ))⁻¹ • P ρ x

def tauInv {r : ℕ} (T T' : ℝ) (ρp : Rho → Fin k0 → ℝ) (P : Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E)
    (Y : ℂ) : Op (r + 1) E :=
  mulF (fun x => (GG T T' x)⁻¹) ∘ mulE (xInvFib ρp P Y)

def IsTauInv {r : ℕ} (T T' : ℝ) (ρp : Rho → Fin k0 → ℝ) (P : Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E)
    (Q : ℂ → Matrix (Fin 2) (Fin 2) (Op (r + 1) E)) (cls : Set ((Fin (r + 1) → ℂ) → E))
    (Dom : Set (Fin (r + 1) → ℂ)) (Y : ℂ) : Prop :=
  ∀ φ ∈ cls, ∀ x ∈ Dom, tauInv T T' ρp P Y (Q Y 1 1 φ) x = φ x

def lOp {r : ℕ} (T T' : ℝ) (ρp : Rho → Fin k0 → ℝ) (P : Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E)
    (Q : ℂ → Matrix (Fin 2) (Fin 2) (Op (r + 1) E)) (Y : ℂ) : Op (r + 1) E :=
  tauInv T T' ρp P Y ∘ Q Y 1 0

def mOp {r : ℕ} (T T' : ℝ) (ρp : Rho → Fin k0 → ℝ) (P : Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E)
    (Q : ℂ → Matrix (Fin 2) (Fin 2) (Op (r + 1) E)) (Y : ℂ) : Op (r + 1) E :=
  tauInv T T' ρp P Y ∘ Q Y 0 1

def lDec {r : ℕ} (T T' : ℝ) (ρp : Rho → Fin k0 → ℝ) (P : Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E)
    (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) :
    Op (r + 1) E :=
  l0 r T T' h Y + mulF (fun x => (GG T T' x)⁻¹) ∘ ∑ l : Fin k0, mulE (shInv ρp P l Y) ∘ mulE (SS l)

end Lines

def SSnat {r : ℕ} (s : (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Op (r + 1) E :=
  mulF (fun x => star (Dr x) / Dr x) ∘ mulE s

def R0 (r : ℕ) (T T' : ℝ) (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) : Op (r + 1) E :=
  mulF (fun x => star (Dr x) * GG T T' x) ∘ (l0 r T T' h Y ∘ Ar r Y + Br r Y)

def weightedMirrorLevelOperator (r : ℕ) (T T' : ℝ) (hs : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) : Op (r + 1) E :=
  mulF (fun x => Dr x * GG T T' x) ∘ (m0 r T T' hs Y ∘ ArV r Y + BrV r Y)

end Formalism.MainNotions.S.LevR

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.S.LevR

open Formalism.QuantumDeterminants

structure Base (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] where

  k0 : ℕ
  T : ℝ
  T' : ℝ
  u : Fin (k0 + 1) → ℝ
  u' : Fin (k0 + 1) → ℝ
  I : Set ℝ

  sgn : ℂ

  hs : E → E → ℂ

  fadj : (E →L[ℂ] E) → (E →L[ℂ] E)

  Rho : Type

  IsType : Rho → Prop

  rhoP : Rho → Fin k0 → ℝ

structure Ctx {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (B : Base E) (r : ℕ) where

  Dom : Set (Fin (r + 1) → ℂ)

  cls : Set ((Fin (r + 1) → ℂ) → E)

  clsF : Set ((Fin (r + 1) → ℂ) → E)

  beta : ((Fin (r + 1) → ℂ) → E) → ((Fin (r + 1) → ℂ) → E) → ℂ

  P : B.Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E

  Q : ℂ → Matrix (Fin 2) (Fin 2) (Op (r + 1) E)

  AA : Set (Op (r + 1) E)

  RR : (w : List (Bool × ℝ)) → Matrix (Fin w.length → Fin 2) (Fin w.length → Fin 2) (Op (r + 1) E)

  TT : (w : List (Bool × ℝ)) → ℂ →
    Matrix (Fin 2) (Fin 2) (Matrix (Fin w.length → Fin 2) (Fin w.length → Fin 2) (Op (r + 1) E))

  qw : List (Bool × ℝ) → ℂ → ℂ

  uw : (w : List (Bool × ℝ)) → (Fin w.length → Fin 2) → Op (r + 1) E

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace Ctx

variable {B : Base E} {r : ℕ} (C : Ctx B r)

def OpEq (A A' : Op (r + 1) E) : Prop := ∀ φ ∈ C.cls, ∀ x ∈ C.Dom, A φ x = A' φ x

def IsAdj (A A' : Op (r + 1) E) : Prop := ∀ φ ∈ C.clsF, ∀ ψ ∈ C.clsF, C.beta (A φ) ψ = C.beta φ (A' ψ)

def gg (C : Ctx B r) (x : Fin (r + 1) → ℂ) : ℂ := GG B.T B.T' x

def fstar (C : Ctx B r) (e : (Fin (r + 1) → ℂ) → E →L[ℂ] E) : (Fin (r + 1) → ℂ) → E →L[ℂ] E :=
  fun x => B.fadj (e x)

abbrev AM (C : Ctx B r) (n : ℕ) := Matrix (Fin n → Fin 2) (Fin n → Fin 2) (Op (r + 1) E)

abbrev FM (C : Ctx B r) (n : ℕ) := Matrix (Fin n → Fin 2) (Fin n → Fin 2) ((Fin (r + 1) → ℂ) → E →L[ℂ] E)

def amul (C : Ctx B r) {n : ℕ} (M N : C.AM n) : C.AM n := fun s t => ∑ v, M s v ∘ N v t

def aapp (C : Ctx B r) {n : ℕ} (M : C.AM n) (φ : (Fin n → Fin 2) → (Fin (r + 1) → ℂ) → E) :
    (Fin n → Fin 2) → (Fin (r + 1) → ℂ) → E := fun s => ∑ t, M s t (φ t)

def adiag (C : Ctx B r) {n : ℕ} (f : (Fin n → Fin 2) → Op (r + 1) E) : C.AM n := fun s t => if s = t then f s else 0

def ascal (C : Ctx B r) {n : ℕ} (A : Op (r + 1) E) : C.AM n := C.adiag (fun _ => A)

def alm (C : Ctx B r) {n : ℕ} (A : Op (r + 1) E) (M : C.AM n) : C.AM n := fun s t => A ∘ M s t

def ablk (C : Ctx B r) {n : ℕ} (B : Fin 2 → Fin 2 → C.AM n) : C.AM (n + 1) :=
  fun s t => B (s 0) (t 0) (Fin.tail s) (Fin.tail t)

def toAM (C : Ctx B r) {n : ℕ} (M : C.FM n) : C.AM n := fun s t => mulE (M s t)

def fmul (C : Ctx B r) {n : ℕ} (M N : C.FM n) : C.FM n := fun s t x => ∑ v, (M s v x).comp (N v t x)

def fblk (C : Ctx B r) {n : ℕ} (B : Fin 2 → Fin 2 → C.FM n) : C.FM (n + 1) :=
  fun s t => B (s 0) (t 0) (Fin.tail s) (Fin.tail t)

def fscal (C : Ctx B r) {n : ℕ} (f : (Fin (r + 1) → ℂ) → ℂ) : C.FM n :=
  fun s t x => if s = t then f x • ContinuousLinearMap.id ℂ E else 0

def fdiag {n : ℕ} (a : (Fin n → Fin 2) → B.Rho → ℂ) : C.FM n :=
  fun s t x => if s = t then ∑ᶠ ρ, a s ρ • C.P ρ x else 0

def fadjM (C : Ctx B r) {n : ℕ} (M : C.FM n) : C.FM n := fun s t x => B.fadj (M t s x)

def xw (C : Ctx B r) : (w : List (Bool × ℝ)) → ℂ → (Fin w.length → Fin 2) → B.Rho → ℂ
  | [], Y, _, ρ => B.sgn * xPoly (B.rhoP ρ) Y
  | (true, ya) :: w, Y, s, ρ =>
      (if s 0 = 0 then (Y - ya) / (Y - ya - 1) else 1) * xw C w Y (Fin.tail s) ρ
  | (false, yb) :: w, Y, s, ρ =>
      (if s 0 = 0 then ((yb : ℂ) - Y) / ((yb : ℂ) - Y - 1) else 1) * xw C w Y (Fin.tail s) ρ

def cw : (w : List (Bool × ℝ)) → (Fin w.length → Fin 2) → B.Rho → ℂ
  | [], _, _ => 1
  | (true, ya) :: w, s, ρ =>
      cw w (Fin.tail s) ρ *
        (if s 0 = 0 then C.qw w ya / C.xw w ((ya : ℂ) + 1) (Fin.tail s) ρ else C.xw w ya (Fin.tail s) ρ)
  | (false, yb) :: w, s, ρ =>
      cw w (Fin.tail s) ρ *
        (if s 0 = 0 then C.qw w ((yb : ℂ) - 1) / C.xw w ((yb : ℂ) - 1) (Fin.tail s) ρ
          else C.xw w yb (Fin.tail s) ρ)

def xM (w : List (Bool × ℝ)) (Y : ℂ) : C.FM w.length := C.fdiag (C.xw w Y)

def xMinv (w : List (Bool × ℝ)) (Y : ℂ) : C.FM w.length := C.fdiag (fun s ρ => (C.xw w Y s ρ)⁻¹)

def ee (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) :
    (w : List (Bool × ℝ)) → ℂ → C.FM w.length
  | [], Y => fun s t x => if s = t then
      (zOf x / star (zOf x)) • ∑ l, (shInv B.rhoP C.P l Y x).comp (SS l x) else 0
  | (true, ya) :: w, Y =>
      C.fblk ![![ee SS w Y - ((Y - ya)⁻¹ • (ee SS w Y - ee SS w ya)) +
          C.fscal (fun x => ((B.T * B.T' : ℝ) : ℂ) / star (zOf x)),
        C.fscal (fun _ => -(Y - ya)⁻¹)],
        ![0, C.fmul (C.xMinv w ya) (C.fmul (ee SS w Y) (C.xM w ya))]]
  | (false, yb) :: w, Y =>
      C.fblk ![![ee SS w Y, 0],
        ![(-(C.qw w ((yb : ℂ) - 1) / ((yb : ℂ) - Y - 1))) •
            C.fmul (C.xMinv w yb) (C.xMinv w ((yb : ℂ) - 1)),
          C.fmul (C.xMinv w yb) (C.fmul (ee SS w Y) (C.xM w yb)) - ((Y - yb)⁻¹ • (ee SS w Y - ee SS w yb)) +
            C.fscal (fun x => ((B.T * B.T' : ℝ) : ℂ) / star (zOf x))]]

def dM (w : List (Bool × ℝ)) : C.AM w.length :=
  C.alm (mulF (fun x => ((Complex.normSq (zOf x) : ℂ) / C.gg x) ^ w.length)) (C.toAM (C.fdiag (C.cw w)))

def dMinv (w : List (Bool × ℝ)) : C.AM w.length :=
  C.alm (mulF (fun x => ((Complex.normSq (zOf x) : ℂ) / C.gg x) ^ w.length)⁻¹)
    (C.toAM (C.fdiag (fun s ρ => (C.cw w s ρ)⁻¹)))

def lfr (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E)
    (w : List (Bool × ℝ)) (Y : ℂ) : C.AM w.length :=
  C.ascal (l0 r B.T B.T' h Y) +
    C.alm (mulF (fun x => star (zOf x) / (zOf x * C.gg x))) (C.toAM (C.ee SS w Y))

def mfr (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E)
    (w : List (Bool × ℝ)) (Yb : ℂ) : C.AM w.length :=
  C.amul (C.dMinv w) (C.amul
    (C.ascal (n := w.length) (m0 r B.T B.T' (C.fstar h) Yb) +
      (Matrix.of fun s t => mulE (C.fadjM (C.ee SS w (Yb - 1)) s t) ∘ mulF (fun x => zOf x / (star (zOf x) * C.gg x)) :
        C.AM w.length))
    (C.dM w))

def F (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) :
    (w : List (Bool × ℝ)) → C.AM w.length
  | [] => C.ascal one
  | (true, ya) :: w =>
      C.ablk ![![C.alm (mulF (fun x => (zOf x)⁻¹)) (F h SS w), 0],
        ![C.alm (mulF (fun x => (star (zOf x))⁻¹ * C.gg x)) (C.amul (C.lfr h SS w ya) (F h SS w)),
          C.alm (mulF (fun x => (star (zOf x))⁻¹ * C.gg x)) (F h SS w)]]
  | (false, yb) :: w =>
      C.ablk ![![C.alm (mulF (fun x => (star (zOf x))⁻¹)) (F h SS w), 0],
        ![C.alm (mulF (fun x => (zOf x)⁻¹ * C.gg x)) (C.amul (C.mfr h SS w yb) (F h SS w)),
          C.alm (mulF (fun x => (zOf x)⁻¹ * C.gg x)) (F h SS w)]]

def form {n : ℕ} (M : C.AM n) (φ ψ : (Fin n → Fin 2) → (Fin (r + 1) → ℂ) → E) : ℂ :=
  ∑ s, ∑ t, C.beta (M s t (φ t)) (ψ s)

def bsum {n : ℕ} (φ ψ : (Fin n → Fin 2) → (Fin (r + 1) → ℂ) → E) : ℂ := ∑ s, C.beta (φ s) (ψ s)

def IsPlus (w : List (Bool × ℝ)) : Prop := ∀ a ∈ w, a.1 = true

def pts (w : List (Bool × ℝ)) : List ℝ := w.map Prod.snd

end Ctx

end Formalism.MainNotions.S.LevR

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.S.LevR

open Formalism.QuantumDeterminants

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

abbrev GOp (n : ℕ) (E : Type*) := (Matrix (Fin n) (Fin n) ℂ → E) → Matrix (Fin n) (Fin n) ℂ → E

structure GCtx (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (r : ℕ) where

  nV : ℕ

  Eop : Fin nV → Fin nV → GOp nV E

  H : Matrix (Fin nV) (Fin nV) ℂ

  eIdx : Fin r → Fin nV

  Rad : GOp nV E → Op (r + 1) E → Prop

  PolyInv : Set (GOp nV E)

namespace GCtx

variable {r : ℕ} (Γ : GCtx E r)

def form (v w : Fin Γ.nV → ℂ) : ℂ := ∑ i, ∑ j, star (w i) * Γ.H i j * v j

def cminor (n : ℕ) (hn : n ≤ r) (u : ℂ) : GOp Γ.nV E := fun f g =>
  ∑ b : Fin n → Fin Γ.nV, if StrictMono b then
    (Matrix.det (Matrix.of fun (a j : Fin n) =>
      Γ.form (g.mulVec (Pi.single (b j) 1)) (Pi.single (Γ.eIdx ⟨a, by omega⟩) 1))) •
      qminorOp Γ.Eop (fun a : Fin n => Γ.eIdx ⟨a, by omega⟩) b u f g
  else 0

end GCtx

def DnVn {r : ℕ} (n : ℕ) (hn : n ≤ r) (Y : ℂ) (i : Fin 2) : Op (r + 1) E :=
  mulF (fun x => ∏ a : Fin n, cOf x ⟨a, by omega⟩) ∘ vv Y n hn i

def NoPoleRho (B : Base E) (Y : ℂ) : Prop := ∀ ρ : B.Rho, B.IsType ρ → ∀ l : Fin B.k0, Y + (B.rhoP ρ l : ℂ) ≠ 0

namespace Ctx

variable {B : Base E} {r : ℕ} (C : Ctx B r)

def RhatV (Y : ℂ) : Op (r + 1) E :=
  mulF Dr ∘ (C.Q Y 0 1 ∘ ArV r Y + C.Q Y 1 1 ∘ BrV r Y)

inductive IsEeP (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) :
    ((Fin (r + 1) → ℂ) → E →L[ℂ] E) → Prop
  | const (a : ℂ) : IsEeP SS (fun _ => a • ContinuousLinearMap.id ℂ E)
  | cst (a : B.Rho → ℂ) : IsEeP SS (fun x => ∑ᶠ ρ, a ρ • C.P ρ x)
  | tt : IsEeP SS (fun x => (((B.T * B.T' : ℝ) : ℂ) * star (Dr x) / star (Dr1 x)) • ContinuousLinearMap.id ℂ E)
  | ttc : IsEeP SS (fun x => (((B.T * B.T' : ℝ) : ℂ) * Dr x / Dr1 x) • ContinuousLinearMap.id ℂ E)
  | ss (l : Fin B.k0) :
      IsEeP SS (fun x => (Dr1 x / star (Dr1 x) * (star (Dr x) / Dr x)) • SS l x)
  | ssa (l : Fin B.k0) :
      IsEeP SS (fun x => (star (Dr1 x) / Dr1 x * (Dr x / star (Dr x))) • B.fadj (SS l x))
  | add {e f} : IsEeP SS e → IsEeP SS f → IsEeP SS (e + f)
  | mul {e f} : IsEeP SS e → IsEeP SS f → IsEeP SS (fun x => (e x).comp (f x))
  | congr {e f} : IsEeP SS e → (∀ x ∈ C.Dom, f x = e x) → IsEeP SS f

inductive IsBdd (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) :
    ((Fin (r + 1) → ℂ) → E →L[ℂ] E) → Prop
  | one : IsBdd SS (fun _ => ContinuousLinearMap.id ℂ E)
  | f1 : IsBdd SS (fun x => (Dr x / Dr1 x) • ContinuousLinearMap.id ℂ E)
  | f2 : IsBdd SS (fun x => (Dr1 x / star (Dr1 x)) • ContinuousLinearMap.id ℂ E)
  | f1c : IsBdd SS (fun x => (star (Dr x) / star (Dr1 x)) • ContinuousLinearMap.id ℂ E)
  | f2c : IsBdd SS (fun x => (star (Dr1 x) / Dr1 x) • ContinuousLinearMap.id ℂ E)
  | f3 : IsBdd SS (fun x => (Gfn B.T B.T' x / ((Complex.normSq (Dr1 x) : ℝ) : ℂ)) • ContinuousLinearMap.id ℂ E)
  | pr (ρ : B.Rho) : IsBdd SS (C.P ρ)
  | sn (l : Fin B.k0) : IsBdd SS (fun x => (star (Dr x) / Dr x) • SS l x)
  | sna (l : Fin B.k0) : IsBdd SS (fun x => (Dr x / star (Dr x)) • B.fadj (SS l x))
  | smul (a : ℂ) {e} : IsBdd SS e → IsBdd SS (a • e)
  | add {e f} : IsBdd SS e → IsBdd SS f → IsBdd SS (e + f)
  | mul {e f} : IsBdd SS e → IsBdd SS f → IsBdd SS (fun x => (e x).comp (f x))
  | congr {e f} : IsBdd SS e → (∀ x ∈ C.Dom, f x = e x) → IsBdd SS f

inductive IsEePM (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) (b : Bool) : (n : ℕ) → C.FM n → Prop
  | scal {n} (c : ℂ) : IsEePM SS b n (C.fscal (fun _ => c))
  | cst {n} (a : (Fin n → Fin 2) → B.Rho → ℂ) : IsEePM SS b n (C.fdiag a)
  | cstOff {n} (s0 t0 : Fin n → Fin 2) (a : B.Rho → ℂ) :
      IsEePM SS b n (fun s t x => if s = s0 ∧ t = t0 then ∑ᶠ ρ, a ρ • C.P ρ x else 0)
  | tt {n} : b = true → IsEePM SS b n (C.fscal (fun x => ((B.T * B.T' : ℝ) : ℂ) / star (zOf x)))
  | ss {n} (l : Fin B.k0) :
      IsEePM SS b n (fun s t x => if s = t then (zOf x / star (zOf x)) • SS l x else 0)
  | add {n M N} : IsEePM SS b n M → IsEePM SS b n N → IsEePM SS b n (M + N)
  | mul {n M N} : IsEePM SS b n M → IsEePM SS b n N → IsEePM SS b n (C.fmul M N)
  | blk {n} (K : Fin 2 → Fin 2 → C.FM n) : (∀ i j, IsEePM SS b n (K i j)) → IsEePM SS b (n + 1) (C.fblk K)
  | congr {n M N} : IsEePM SS b n M → (∀ s t, ∀ x ∈ C.Dom, N s t x = M s t x) → IsEePM SS b n N

inductive IsFac (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) :
    ℂ → Op (r + 1) E → Prop
  | lA (Y : ℂ) : IsFac h SS Y (mulF (fun x => (Dr1 x)⁻¹) ∘ Ahat r Y)
  | lR (Y : ℂ) : IsFac h SS Y (mulF (fun x => (star (Dr1 x))⁻¹) ∘ R0 r B.T B.T' h Y)
  | lAv (Y : ℂ) : IsFac h SS Y (mulF (fun x => (star (Dr1 x))⁻¹) ∘ AhatV r Y)
  | lRv (Y : ℂ) : IsFac h SS Y (mulF (fun x => (Dr1 x)⁻¹) ∘ weightedMirrorLevelOperator r B.T B.T' (C.fstar h) Y)
  | ee (Y : ℂ) {e} : C.IsEeP SS e → IsFac h SS Y (mulE e)
  | wG (Y : ℂ) (s : ℤ) : s = 1 ∨ s = -1 → IsFac h SS Y (mulF (fun x => Gfn B.T B.T' x ^ s))
  | wD (Y : ℂ) (s : ℤ) : s = 1 ∨ s = -1 → IsFac h SS Y (mulF (fun x => Dr1 x ^ s))
  | wDb (Y : ℂ) (s : ℤ) : s = 1 ∨ s = -1 → IsFac h SS Y (mulF (fun x => star (Dr1 x) ^ s))

def blk4 (i : Fin 4) (Y : ℂ) : Op (r + 1) E :=
  match i with
  | 0 => Ahat r Y
  | 1 => Rhat r C.Q Y
  | 2 => AhatV r Y
  | 3 => C.RhatV Y

def compL (C : Ctx B r) : List (Op (r + 1) E) → Op (r + 1) E
  | [] => one
  | A :: l => A ∘ compL C l

def PiL (x : Fin (r + 1) → ℂ) : E →L[ℂ] E := ∑ᶠ ρ, C.P ρ x

def IsFrameDatum (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Prop :=
  (∀ Y : ℂ, NoPoleRho B Y → C.OpEq (lOp B.T B.T' B.rhoP C.P C.Q Y) (lDec B.T B.T' B.rhoP C.P h SS Y)) ∧
  (∀ x ∈ C.Dom, ∀ e : E, dZ r (fun y => C.PiL y e) x + h x (C.PiL x e) = C.PiL x (h x e)) ∧
  (∀ x ∈ C.Dom, ∀ e : E, h x (e - C.PiL x e) - C.PiL x (h x (e - C.PiL x e)) = 0) ∧
  (∀ l, ∀ x ∈ C.Dom, SS l x = (C.PiL x).comp ((SS l x).comp (C.PiL x)))

def SSnatS (C : Ctx B r) (s : (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Op (r + 1) E :=
  mulF (fun x => Dr x / star (Dr x)) ∘ mulE (C.fstar s)

end Ctx

namespace Ctx

section Shape

variable {B : Base E} {r : ℕ} {C : Ctx B r} {SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E} {b : Bool}

theorem IsEePM.smul {n : ℕ} (c : ℂ) {M : C.FM n} (h : IsEePM C SS b n M) : IsEePM C SS b n (c • M) := by
  have e : c • M = C.fmul (C.fscal (fun _ => c)) M := by
    funext s t x
    simp only [Ctx.fmul, Ctx.fscal, Matrix.smul_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single s]
    · simp
    · intro v _ hv
      simp [Ne.symm hv]
    · simp
  rw [e]
  exact IsEePM.mul (IsEePM.scal c) h

theorem IsEePM.zero {n : ℕ} : IsEePM C SS b n (0 : C.FM n) := by
  have e : (0 : C.FM n) = C.fscal (fun _ => (0 : ℂ)) := by
    funext s t x
    simp [Ctx.fscal]
  rw [e]
  exact IsEePM.scal 0

theorem IsEePM.sub {n : ℕ} {M N : C.FM n} (h : IsEePM C SS b n M) (h' : IsEePM C SS b n N) :
    IsEePM C SS b n (M - N) := by
  have e : M - N = M + (-1 : ℂ) • N := by simp [sub_eq_add_neg]
  rw [e]
  exact IsEePM.add h (IsEePM.smul _ h')

theorem IsEePM.sum {n : ℕ} {ι : Type*} (s : Finset ι) (M : ι → C.FM n) (h : ∀ i ∈ s, IsEePM C SS b n (M i)) :
    IsEePM C SS b n (∑ i ∈ s, M i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsEePM.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact IsEePM.add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem fmul_sub_mid {n : ℕ} (X M N Z : C.FM n) :
    C.fmul X (C.fmul M Z) - C.fmul X (C.fmul N Z) = C.fmul X (C.fmul (M - N) Z) := by
  funext s t x
  simp only [Ctx.fmul, Matrix.sub_apply, Pi.sub_apply, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    Finset.sum_sub_distrib]

theorem fblk_sub {n : ℕ} (K K' : Fin 2 → Fin 2 → C.FM n) :
    C.fblk K - C.fblk K' = C.fblk (fun i j => K i j - K' i j) := rfl

theorem ee_nil_eq (Y : ℂ) :
    C.ee SS [] Y = ∑ l : Fin B.k0, C.fmul (C.fdiag (fun _ ρ => (Y + (B.rhoP ρ l : ℂ))⁻¹))
      (fun s t x => if s = t then (zOf x / star (zOf x)) • SS l x else 0) := by
  funext s t x
  have sub : ∀ a c : Fin ([] : List (Bool × ℝ)).length → Fin 2, a = c := fun a c => funext fun i => absurd i.2 (by simp)
  have hst : s = t := sub _ _
  subst hst
  simp only [Ctx.ee, Ctx.fmul, Ctx.fdiag, shInv, if_true, Matrix.sum_apply, Finset.sum_apply]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single s]
  · simp
  · intro v _ hv
    exact absurd (sub _ _) hv
  · intro hs
    exact absurd (Finset.mem_univ s) hs

theorem ee_nil_mem (Y : ℂ) : IsEePM C SS b 0 (C.ee SS [] Y) := by
  rw [ee_nil_eq]
  exact IsEePM.sum _ _ fun l _ => IsEePM.mul (IsEePM.cst _) (IsEePM.ss l)

theorem ee_mem : ∀ (w : List (Bool × ℝ)) (Y : ℂ), IsEePM C SS true w.length (C.ee SS w Y)
  | [], Y => ee_nil_mem Y
  | (true, ya) :: w, Y => by
      rw [Ctx.ee]
      refine IsEePM.blk _ fun i j => ?_
      fin_cases i <;> fin_cases j
      · exact IsEePM.add (IsEePM.sub (ee_mem w Y) (IsEePM.smul _ (IsEePM.sub (ee_mem w Y) (ee_mem w ya))))
          (IsEePM.tt rfl)
      · exact IsEePM.scal _
      · exact IsEePM.zero
      · exact IsEePM.mul (IsEePM.cst _) (IsEePM.mul (ee_mem w Y) (IsEePM.cst _))
  | (false, yb) :: w, Y => by
      rw [Ctx.ee]
      refine IsEePM.blk _ fun i j => ?_
      fin_cases i <;> fin_cases j
      · exact ee_mem w Y
      · exact IsEePM.zero
      · exact IsEePM.smul _ (IsEePM.mul (IsEePM.cst _) (IsEePM.cst _))
      · exact IsEePM.add (IsEePM.sub (IsEePM.mul (IsEePM.cst _) (IsEePM.mul (ee_mem w Y) (IsEePM.cst _)))
          (IsEePM.smul _ (IsEePM.sub (ee_mem w Y) (ee_mem w yb)))) (IsEePM.tt rfl)

theorem IsEePM.of_eq {n : ℕ} {M N : C.FM n} (h : IsEePM C SS b n M) (e : M = N) : IsEePM C SS b n N := e ▸ h

theorem ee_diff_mem : ∀ (w : List (Bool × ℝ)) (Y Y' : ℂ), IsEePM C SS false w.length (C.ee SS w Y - C.ee SS w Y')
  | [], Y, Y' => IsEePM.sub (ee_nil_mem Y) (ee_nil_mem Y')
  | (true, ya) :: w, Y, Y' => by
      rw [Ctx.ee, Ctx.ee, fblk_sub]
      refine IsEePM.blk _ fun i j => ?_
      fin_cases i <;> fin_cases j
      · refine IsEePM.of_eq (IsEePM.add (IsEePM.sub (ee_diff_mem w Y Y')
          (IsEePM.smul (Y - ya)⁻¹ (ee_diff_mem w Y ya))) (IsEePM.smul (Y' - ya)⁻¹ (ee_diff_mem w Y' ya))) ?_
        show _ = (C.ee SS w Y - ((Y - ya)⁻¹ • (C.ee SS w Y - C.ee SS w ya)) + C.fscal _) -
          (C.ee SS w Y' - ((Y' - ya)⁻¹ • (C.ee SS w Y' - C.ee SS w ya)) + C.fscal _)
        abel
      · exact IsEePM.sub (IsEePM.scal _) (IsEePM.scal _)
      · exact IsEePM.sub IsEePM.zero IsEePM.zero
      · exact IsEePM.of_eq (IsEePM.mul (IsEePM.cst _) (IsEePM.mul (ee_diff_mem w Y Y') (IsEePM.cst _)))
          (fmul_sub_mid _ _ _ _).symm
  | (false, yb) :: w, Y, Y' => by
      rw [Ctx.ee, Ctx.ee, fblk_sub]
      refine IsEePM.blk _ fun i j => ?_
      fin_cases i <;> fin_cases j
      · exact ee_diff_mem w Y Y'
      · exact IsEePM.sub IsEePM.zero IsEePM.zero
      · exact IsEePM.sub (IsEePM.smul _ (IsEePM.mul (IsEePM.cst _) (IsEePM.cst _)))
          (IsEePM.smul _ (IsEePM.mul (IsEePM.cst _) (IsEePM.cst _)))
      · refine IsEePM.of_eq (IsEePM.add (IsEePM.sub
          (IsEePM.mul (IsEePM.cst (fun s ρ => (C.xw w yb s ρ)⁻¹)) (IsEePM.mul (ee_diff_mem w Y Y') (IsEePM.cst (C.xw w yb))))
          (IsEePM.smul (Y - yb)⁻¹ (ee_diff_mem w Y yb))) (IsEePM.smul (Y' - yb)⁻¹ (ee_diff_mem w Y' yb))) ?_
        rw [← fmul_sub_mid]
        show C.fmul (C.xMinv w yb) (C.fmul (C.ee SS w Y) (C.xM w yb)) -
            C.fmul (C.xMinv w yb) (C.fmul (C.ee SS w Y') (C.xM w yb)) - _ + _ = (C.fmul (C.xMinv w yb) (C.fmul (C.ee SS w Y) (C.xM w yb)) -
            ((Y - yb)⁻¹ • (C.ee SS w Y - C.ee SS w yb)) + C.fscal _) -
          (C.fmul (C.xMinv w yb) (C.fmul (C.ee SS w Y') (C.xM w yb)) -
            ((Y' - yb)⁻¹ • (C.ee SS w Y' - C.ee SS w yb)) + C.fscal _)
        abel

end Shape

end Ctx

def gw {B : Base E} {r : ℕ} (Cr : Ctx B 0) (C0 : Ctx B r) (lift : Op 1 E → Op (r + 1) E)
    (h : (Fin 1 → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin 1 → ℂ) → E →L[ℂ] E) (w : List (Bool × ℝ)) :
    (Fin w.length → Fin 2) → Op (r + 1) E :=
  fun v => ∑ t, lift (Cr.F h SS w v t) ∘ C0.uw w t

def prW (k : ℕ) (zb : Fin (k + 1) → ℂ) (v : Fin (k + 1) → ℂ) : Fin (k + 1) → ℂ :=
  v - (herm (Hb k) v zb / herm (Hb k) zb zb) • zb

def omF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Fin (k + 1) → ℂ :=
  Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ • prW k (wbPart k r z) (Matrix.mulVec μ (wbPart k r z'))

def omF' (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Fin (k + 1) → ℂ :=
  star (Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩) • prW k (wbPart k r z') (Matrix.mulVec μ⁻¹ (wbPart k r z))

def bordDet (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (w : Fin (2 * r + k + 1) → ℂ) : ℂ :=
  Matrix.det (Matrix.of fun (a b : Fin (r + 1)) =>
    herm (Hpk k r) (Matrix.mulVec g (fvec k r z' b)) (if a = Fin.last r then w else fvec k r z a))

def omG (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Fin (k + 1) → ℂ :=
  prW k (wbPart k r z) (fun j => Hb k j j * bordDet k r z z' g (bvec (wI k r j)))

def omG' (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Fin (k + 1) → ℂ :=
  omG k r z' z (Hpk k r * g.conjTranspose * Hpk k r)

def OmSlice (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Prop :=
  inWb k r z → inWb k r z' → ∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) → μ ∈ UH (Hb k) →
    omG k r z z' (bigCell k r c μ) = omF k r z z' c μ ∧ omG' k r z z' (bigCell k r c μ) = omF' k r z z' c μ

def OmNInv (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Prop :=
  inWb k r z → inWb k r z' → ∀ g, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r,
    omG k r z z' (n * g * n') = omG k r z z' g ∧ omG' k r z z' (n * g * n') = omG' k r z z' g

def evG {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ) : ℂ :=
  MvPolynomial.eval (Sum.elim (fun ij => g ij.1 ij.2) (fun ij => star (g ij.1 ij.2))) p

end Formalism.MainNotions.S.LevR

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.S.LevR

open Formalism.QuantumDeterminants
open Formalism.MainNotions.S.TopsChoicePartA

def hsAdj (L : Lev) (a : L.Hom →L[ℂ] L.Hom) : L.Hom →L[ℂ] L.Hom := by
  classical
  exact if h : ∃ b : L.Hom →L[ℂ] L.Hom, ∀ X Y, Formalism.MainNotions.S.hsInner (a X) Y = Formalism.MainNotions.S.hsInner X (b Y)
    then Classical.choose h else 0

def baseOf (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ) (I : Set ℝ) : Base L.Hom where
  k0 := L.k0
  T := L.T
  T' := L.T'
  u := u
  u' := u'
  I := I
  sgn := ((sCut u u' I : ℝ) : ℂ)
  hs := Formalism.MainNotions.S.hsInner
  fadj := hsAdj L
  Rho := Fin L.k0 → ℝ
  IsType := fun ρ => Interlace u ρ ∧ Interlace u' ρ ∧ ∀ j, ∃ m : ℤ, ρ j = m + ((L.k0 : ℝ) - 1) / 2
  rhoP := id

def ctxR (Lt : Lev) (u u' : Fin (Lt.k0 + 1) → ℝ) (I : Set ℝ) (hr : Lt.r + 0 = Lt.r)
    (R : ℂ → Matrix (Fin 2) (Fin 2) (Lt.down Lt.r 0 hr).POp)
    (clsF : Set (Lt.down Lt.r 0 hr).PF) : Ctx (baseOf Lt u u' I) 0 where
  Dom := (Lt.down Lt.r 0 hr).BD
  cls := (Lt.down Lt.r 0 hr).Img
  clsF := clsF
  beta := (Lt.down Lt.r 0 hr).betaB
  P := fun ρ x => (Lt.down Lt.r 0 hr).lineP ((Lt.down Lt.r 0 hr).pt x) ρ
  Q := R
  AA := {O | ∃ Θ ∈ (Lt.down Lt.r 0 hr).AA, (Lt.down Lt.r 0 hr).Rad Θ O}
  RR := fun w => ((Lt.down Lt.r 0 hr).wmod R (sCut u u' I) u u' w).RR
  TT := fun w Y a b s t => ((Lt.down Lt.r 0 hr).wmod R (sCut u u' I) u u' w).TT Y (a, s) (b, t)
  qw := fun w => ((Lt.down Lt.r 0 hr).wmod R (sCut u u' I) u u' w).q
  uw := fun w => uw (m := 0) w 0 le_rfl

def ctx0 (Lt : Lev) (u u' : Fin (Lt.k0 + 1) → ℝ) (I : Set ℝ) (hr : Lt.r + 0 = Lt.r)
    (R : ℂ → Matrix (Fin 2) (Fin 2) (Lt.down Lt.r 0 hr).POp) : Ctx (baseOf Lt u u' I) Lt.r where
  Dom := Lt.BD
  cls := Lt.Img
  clsF := Lt.Img
  beta := Lt.betaB
  P := fun ρ x => Lt.lineP (Lt.pt x) ρ
  Q := fun Y a b => Lt.liftDown Lt.r 0 hr (R Y a b)
  AA := {O | ∃ Θ ∈ Lt.AA, Lt.Rad Θ O}
  RR := fun w s t => Lt.liftDown Lt.r 0 hr (((Lt.down Lt.r 0 hr).wmod R (sCut u u' I) u u' w).RR s t)
  TT := fun w Y a b s t =>
    Lt.liftDown Lt.r 0 hr (((Lt.down Lt.r 0 hr).wmod R (sCut u u' I) u u' w).TT Y (a, s) (b, t))
  qw := fun w => ((Lt.down Lt.r 0 hr).wmod R (sCut u u' I) u u' w).q
  uw := fun w => uw (m := Lt.r) w Lt.r le_rfl

def baseLevelContext (Lt : Lev) (u u' : Fin (Lt.k0 + 1) → ℝ) (I : Set ℝ) (hr : Lt.r + 0 = Lt.r)
    (R : ℂ → Matrix (Fin 2) (Fin 2) (Lt.down Lt.r 0 hr).POp) (clsF : Set Lt.PF) : Ctx (baseOf Lt u u' I) Lt.r :=
  { ctx0 Lt u u' I hr R with clsF := clsF }

def gctxOf (L : Lev) : GCtx L.Hom L.r where
  nV := 2 * L.r + (L.k0 + 1) + 1
  Eop := EabH (Hpk (L.k0 + 1) L.r)
  H := Hpk (L.k0 + 1) L.r
  eIdx := eI (L.k0 + 1) L.r
  Rad := L.Rad
  PolyInv := L.AApoly

def pullZ {r : ℕ} {X : Type*} (e : (Fin 1 → ℂ) → X) : (Fin (r + 1) → ℂ) → X := fun x => e (fun _ => zOf x)

end Formalism.MainNotions.S.LevR
