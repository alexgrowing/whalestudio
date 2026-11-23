import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

open Matrix MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.S.TopsChoicePartA

open Formalism.QuantumDeterminants

abbrev Mat (k0 r : ℕ) := Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ

abbrev Vec (k0 r : ℕ) := Fin (2 * r + (k0 + 1) + 1) → ℂ

structure Lev where
  k0 : ℕ
  r : ℕ
  z : Vec k0 r
  z' : Vec k0 r
  Wp : Type
  Wq : Type
  [nWp : NormedAddCommGroup Wp]
  [iWp : InnerProductSpace ℂ Wp]
  [fWp : FiniteDimensional ℂ Wp]
  [nWq : NormedAddCommGroup Wq]
  [iWq : InnerProductSpace ℂ Wq]
  [fWq : FiniteDimensional ℂ Wq]
  π : Mat k0 r → (Wp →L[ℂ] Wp)
  π' : Mat k0 r → (Wq →L[ℂ] Wq)
  μsec : ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ

attribute [instance] Lev.nWp Lev.iWp Lev.fWp Lev.nWq Lev.iWq Lev.fWq

namespace Lev

abbrev Hom (L : Lev) := L.Wq →L[ℂ] L.Wp

abbrev PF (L : Lev) := (Fin (L.r + 1) → ℂ) → L.Hom

abbrev POp (L : Lev) := Op (L.r + 1) L.Hom

abbrev GF (L : Lev) := Mat L.k0 L.r → L.Hom

def T (L : Lev) : ℝ := Tz (L.k0 + 1) L.r L.z
def T' (L : Lev) : ℝ := Tz (L.k0 + 1) L.r L.z'

def HC (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ) : Prop :=
  Formalism.MainNotions.S.IsHCTypeW (L.k0 + 1) L.r L.z u L.π ∧ Formalism.MainNotions.S.IsHCTypeW (L.k0 + 1) L.r L.z' u' L.π' ∧
    ∀ i, ∃ m : ℤ, u i - u' i = m

def Std (L : Lev) : Prop :=
  inWb (L.k0 + 1) L.r L.z ∧ inWb (L.k0 + 1) L.r L.z' ∧ 0 < L.T ∧ 0 < L.T' ∧
    IsSection (L.k0 + 1) L.r L.z L.z' L.μsec

def xv (L : Lev) : Vec L.k0 L.r := if h : 0 < L.r then bvec (eI (L.k0 + 1) L.r ⟨0, h⟩) else L.z
def xv' (L : Lev) : Vec L.k0 L.r := if h : 0 < L.r then bvec (eI (L.k0 + 1) L.r ⟨0, h⟩) else L.z'

def flat (L : Lev) (v : Vec L.k0 L.r) : Vec L.k0 L.r := fun j => herm (Hpk (L.k0 + 1) L.r) (bvec j) v

def yv (L : Lev) (g : Mat L.k0 L.r) : Vec L.k0 L.r := g⁻¹ *ᵥ L.xv

def QQ (L : Lev) (Y : ℂ) : Fin 2 → Fin 2 → (L.GF → L.GF) :=
  QQop (m := 2 * L.r + L.k0) (EabH (Hpk (L.k0 + 1) L.r)) (((2 * L.r + L.k0 + 1 : ℕ) : ℂ) / 2) Y
    (fun g => L.yv g) (fun g => L.flat (L.yv g)) L.xv' (L.flat L.xv')

def Cap (L : Lev) (Y : ℂ) : L.GF → L.GF :=
  capelliH (Hpk (L.k0 + 1) L.r) (Y + ((2 * L.r + L.k0 + 1 : ℕ) : ℂ) / 2)

def KKop (L : Lev) : Set L.GF :=
  EqF (L.k0 + 1) L.r L.z L.z' cStd L.π L.π' ∩ {J | ∃ ε : ℝ, 0 < ε ∧ J ∈ KKeps (L.k0 + 1) L.r L.z L.z' ε}

def B (L : Lev) (J : L.GF) : L.PF := Btr (L.k0 + 1) L.r L.z L.z' L.μsec J

def Img (L : Lev) : Set L.PF := {φ | ∃ J ∈ L.KKop, φ = L.B J}

def Rad (L : Lev) (Θ : L.GF → L.GF) (R : L.POp) : Prop :=
  HasRadialPart (L.k0 + 1) L.r L.z L.z' cStd L.π L.π' L.μsec L.KKop Θ R

def BD (L : Lev) : Set (Fin (L.r + 1) → ℂ) := BDom (L.k0 + 1) L.r L.z L.z'

def IsRadQQ (L : Lev) (R : ℂ → Matrix (Fin 2) (Fin 2) L.POp) : Prop :=
  ∀ (Y : ℂ) (a b : Fin 2), L.Rad (L.QQ Y a b) (R Y a b) ∧ LocalOn L.BD (R Y a b) ∧
    ∀ U : Set (Fin (L.r + 1) → ℂ), IsOpen U → U ⊆ L.BD → LocalOn U (R Y a b)

end Lev

section OpMat

variable {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]

def scalOp (s : ℂ) : Op m E := fun f => s • f

def idOp : Op m E := fun f => f

def zeroOp : Op m E := fun _ => 0

def omMul {ι κ ν : Type*} [Fintype κ] (M : Matrix ι κ (Op m E)) (N : Matrix κ ν (Op m E)) :
    Matrix ι ν (Op m E) :=
  fun a b f => ∑ c, M a c (N c b f)

def omApply {ι κ : Type*} [Fintype κ] (M : Matrix ι κ (Op m E)) (x : κ → (Fin m → ℂ) → E) :
    ι → (Fin m → ℂ) → E :=
  fun a => ∑ b, M a b (x b)

def smat {ι κ : Type*} (S : Matrix ι κ ℂ) : Matrix ι κ (Op m E) := fun a b => scalOp (S a b)

def oneOM {ι : Type*} [DecidableEq ι] : Matrix ι ι (Op m E) := fun a b => if a = b then idOp else zeroOp

def EqOn' {ι κ : Type*} (S : Set ((Fin m → ℂ) → E)) (D : Set (Fin m → ℂ)) (M N : Matrix ι κ (Op m E)) : Prop :=
  ∀ a b, ∀ φ ∈ S, ∀ x ∈ D, M a b φ x = N a b φ x

def t1 {A : Type*} [Zero A] (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  fun ik jl => if ik.2 = jl.2 then M ik.1 jl.1 else 0

def t2 {A : Type*} [Zero A] (M : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
  fun ik jl => if ik.1 = jl.1 then M ik.2 jl.2 else 0

end OpMat

def Pflip : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun ik jl => if ik.1 = jl.2 ∧ ik.2 = jl.1 then 1 else 0

def Rh (D : ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun ik jl => ((if ik = jl then D else 0) - Pflip ik jl) / (D - 1)

def J2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

def Us (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; -s, 1]

def UsInv (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; s, 1]

abbrev Letter := Bool × ℝ

abbrev Word := List Letter

abbrev AuxiliarySlotStates (n : ℕ) := Fin n → Fin 2

def e1s (n : ℕ) : AuxiliarySlotStates n := fun _ => 0

structure Mod (m : ℕ) (E : Type*) (n : ℕ) where
  RR : Matrix (AuxiliarySlotStates n) (AuxiliarySlotStates n) (Op m E)
  TT : ℂ → Matrix (Fin 2 × AuxiliarySlotStates n) (Fin 2 × AuxiliarySlotStates n) (Op m E)
  q : ℂ → ℂ

section Words

variable {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]

def modStart (Q : ℂ → Matrix (Fin 2) (Fin 2) (Op m E)) (q : ℂ → ℂ) : Mod m E 0 where
  RR := oneOM
  TT := fun Y a b => Q Y a.1 b.1
  q := q

def stepPlus {n : ℕ} (Ya : ℝ) (M : Mod m E n) : Mod m E (n + 1) where
  RR := fun α β f => ∑ γ : AuxiliarySlotStates n, M.RR (Fin.tail α) γ (M.TT (Ya : ℂ) (α 0, γ) (β 0, Fin.tail β) f)
  TT := fun Y a b f => ∑ ρ : Fin 2,
    M.TT Y (a.1, Fin.tail a.2) (ρ, Fin.tail b.2) (Rh (Y - (Ya : ℂ)) (ρ, a.2 0) (b.1, b.2 0) • f)
  q := fun Y => M.q Y * ((Y - (Ya : ℂ)) + 1) / (Y - (Ya : ℂ))

def stepMinus {n : ℕ} (Yb : ℝ) (M : Mod m E n) : Mod m E (n + 1) where
  RR := fun α β f => ∑ γ : AuxiliarySlotStates n, M.RR (Fin.tail α) γ (M.TT (Yb : ℂ) (β 0, γ) (α 0, Fin.tail β) f)
  TT := fun Y a b f => ∑ ρ : Fin 2,
    Rh ((Yb : ℂ) - Y) (a.1, b.2 0) (ρ, a.2 0) • M.TT Y (ρ, Fin.tail a.2) (b.1, Fin.tail b.2) f
  q := fun Y => M.q Y * ((Yb : ℂ) - Y) / (((Yb : ℂ) - Y) - 1)

def step {n : ℕ} (l : Letter) (M : Mod m E n) : Mod m E (n + 1) :=
  if l.1 then stepPlus l.2 M else stepMinus l.2 M

def wordMod (Q : ℂ → Matrix (Fin 2) (Fin 2) (Op m E)) (q : ℂ → ℂ) : (w : Word) → Mod m E w.length
  | [] => modStart Q q
  | l :: w => step l (wordMod Q q w)

end Words

def Generic (w : Word) : Prop := w.Pairwise (fun a b => a.2 ≠ b.2 ∧ a.2 - b.2 ≠ 1 ∧ b.2 - a.2 ≠ 1)

def OffPoles (w : Word) (Y : ℂ) : Prop :=
  ∀ l ∈ w, Y ≠ (l.2 : ℂ) ∧ Y ≠ (l.2 : ℂ) + 1 ∧ Y ≠ (l.2 : ℂ) - 1

def Admissible (I : Set ℝ) (w : Word) : Prop :=
  (∀ l ∈ w, l.2 ∈ I) ∧ w.Pairwise (fun a b => 2 < |a.2 - b.2|)

def Interlace {k0 : ℕ} (u : Fin (k0 + 1) → ℝ) (ρ : Fin k0 → ℝ) : Prop :=
  ∀ j : Fin k0, ρ j < u j.castSucc ∧ u j.succ < ρ j

section Vectors

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def vLetter (c : Fin m) (l : Letter) : Matrix (Fin 2) (Fin 2) (Op m E) :=
  if l.1 then Tmat c (l.2 : ℂ) else TmatV c (l.2 : ℂ)

def vLetterStar (c : Fin m) (l : Letter) : Matrix (Fin 2) (Fin 2) (Op m E) :=
  if l.1 then TmatStar c (l.2 : ℂ) else (Tmat c (l.2 : ℂ)).transpose

def bT (c : Fin m) : (w : Word) → Matrix (AuxiliarySlotStates w.length) (AuxiliarySlotStates w.length) (Op m E)
  | [] => oneOM
  | l :: w => fun α β f => vLetter c l (α 0) (β 0) (bT c w (Fin.tail α) (Fin.tail β) f)

def bTstar (c : Fin m) : (w : Word) → Matrix (AuxiliarySlotStates w.length) (AuxiliarySlotStates w.length) (Op m E)
  | [] => oneOM
  | l :: w => fun α β f => bTstar c w (Fin.tail α) (Fin.tail β) (vLetterStar c l (α 0) (β 0) f)

end Vectors

namespace Lev

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def betaB (L : Lev) (φ ψ : L.PF) : ℂ :=
  ∫ x : Fin (L.r + 1) → ℂ, (((∏ a : Fin L.r, Complex.normSq (cOf x a))⁻¹ : ℝ) : ℂ) *
    Formalism.MainNotions.S.hsInner (φ x) (ψ x)

def form (L : Lev) {ι : Type*} [Fintype ι] (M : Matrix ι ι L.POp) (x y : ι → L.PF) : ℂ :=
  ∑ a, L.betaB (omApply M x a) (y a)

def HermOn (L : Lev) {ι : Type*} [Fintype ι] (S : Set L.PF) (M : Matrix ι ι L.POp) : Prop :=
  ∀ x y : ι → L.PF, (∀ a, x a ∈ S) → (∀ a, y a ∈ S) →
    L.form M x y = ∑ a, L.betaB (x a) (omApply M y a)

def PosOn (L : Lev) {ι : Type*} [Fintype ι] (S : Set L.PF) (M : Matrix ι ι L.POp) : Prop :=
  ∀ x : ι → L.PF, (∀ a, x a ∈ S) → (L.form M x x).im = 0 ∧ 0 ≤ (L.form M x x).re

def matNorm {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖g i j‖

def Eword (L : Lev) (w : List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1))) (F : L.GF) :
    L.GF :=
  w.foldr (fun ab f => EabH (Hpk (L.k0 + 1) L.r) ab.1 ab.2 f) F

def CC (L : Lev) (A : ℝ) (mm : ℕ) (F : L.GF) : Prop :=
  (∃ U : Set (Mat L.k0 L.r), IsOpen U ∧ UH (Hpk (L.k0 + 1) L.r) ⊆ U ∧ ContDiffOn ℝ (mm : ℕ∞) F U) ∧
    ∀ w : List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1)), w.length ≤ mm →
      ∃ C : ℝ, ∀ g ∈ UH (Hpk (L.k0 + 1) L.r), ‖L.Eword w F g‖ ≤ C * (1 + matNorm g) ^ (-A)

structure Haar (L : Lev) where
  μW : Measure (Mt (L.k0 + 1) L.r)
  μN : Measure (Mt (L.k0 + 1) L.r)
  μW' : Measure (Mt (L.k0 + 1) L.r)

def Haar.Ok {L : Lev} (h : L.Haar) : Prop :=
  Formalism.MainNotions.S.IsHaarOn (UWset (L.k0 + 1) L.r L.z) h.μW ∧ Formalism.MainNotions.S.IsHaarOn (Nset (L.k0 + 1) L.r) h.μN ∧
    Formalism.MainNotions.S.IsHaarOn (UWset (L.k0 + 1) L.r L.z') h.μW'

def KK (L : Lev) (h : L.Haar) (A : ℝ) (mm : ℕ) : Set L.GF :=
  {J | ∃ F : L.GF, L.CC A mm F ∧ (∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ tsupport F, ε ≤ Gf (L.k0 + 1) L.r L.z L.z' g) ∧
    J = besselJ (L.k0 + 1) L.r L.z L.z' cStd L.π L.π' h.μW h.μN h.μW' F}

def ImgK (L : Lev) (h : L.Haar) (A : ℝ) (mm : ℕ) : Set L.PF :=
  {φ | ∃ J ∈ L.KK h A mm, ContDiffOn ℝ ∞ (L.B J) L.BD ∧ φ = L.B J}

end Lev

def liftVectorLevel {k0 r : ℕ} (v : Vec k0 r) : Vec k0 (r + 1) :=
  fun p => liftVec (k0 + 1) 1 r v (Fin.cast (by omega) p)

def ι1 {k0 r : ℕ} (g : Mat k0 r) : Mat k0 (r + 1) :=
  fun p q => ιLev (k0 + 1) 1 r g (Fin.cast (by omega) p) (Fin.cast (by omega) q)

def Lev.up (L : Lev) (pb : Mat L.k0 (L.r + 1) → (L.Wp →L[ℂ] L.Wp))
    (pb' : Mat L.k0 (L.r + 1) → (L.Wq →L[ℂ] L.Wq)) : Lev where
  k0 := L.k0
  r := L.r + 1
  z := liftVectorLevel L.z
  z' := liftVectorLevel L.z'
  Wp := L.Wp
  Wq := L.Wq
  π := pb
  π' := pb'
  μsec := L.μsec

def Lev.Compat (L : Lev) (pb : Mat L.k0 (L.r + 1) → (L.Wp →L[ℂ] L.Wp))
    (pb' : Mat L.k0 (L.r + 1) → (L.Wq →L[ℂ] L.Wq)) : Prop :=
  ∀ g : Mat L.k0 L.r, L.π g = pb (ι1 g) ∧ L.π' g = pb' (ι1 g)

def liftOM {ι κ : Type*} {m : ℕ} {E : Type*} (M : Matrix ι κ (Op m E)) : Matrix ι κ (Op (m + 1) E) :=
  fun a b => liftOp (M a b)

def fs {m : ℕ} (s : ℂ) (x : Fin (m + 1) → ℂ) : ℂ := Complex.exp (s * x 0 - star s * star (x 0))

def fsC (s c : ℂ) : ℂ := Complex.exp (s * c - star s * star c)

def UUs (s : ℂ) : (w : Word) → Matrix (AuxiliarySlotStates w.length) (AuxiliarySlotStates w.length) ℂ
  | [] => 1
  | l :: w => fun α β => (if l.1 then Us s else Us (star s)) (α 0) (β 0) * UUs s w (Fin.tail α) (Fin.tail β)

def UUsInv (s : ℂ) : (w : Word) → Matrix (AuxiliarySlotStates w.length) (AuxiliarySlotStates w.length) ℂ
  | [] => 1
  | l :: w => fun α β =>
      (if l.1 then UsInv s else UsInv (star s)) (α 0) (β 0) * UUsInv s w (Fin.tail α) (Fin.tail β)

section Waves

variable {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]

def Vop (s : ℂ) (w : Word) : Matrix (AuxiliarySlotStates w.length) (AuxiliarySlotStates w.length) (Op (m + 1) E) :=
  fun α β φ x => (fs s x * UUsInv s w α β) • φ x

def VopStar (s : ℂ) (w : Word) : Matrix (AuxiliarySlotStates w.length) (AuxiliarySlotStates w.length) (Op (m + 1) E) :=
  fun α β φ x => (star (fs s x) * star (UUsInv s w β α)) • φ x

def VopInv (s : ℂ) (w : Word) : Matrix (AuxiliarySlotStates w.length) (AuxiliarySlotStates w.length) (Op (m + 1) E) :=
  fun α β φ x => ((fs s x)⁻¹ * UUs s w α β) • φ x

def actOnPositions {n : ℕ} (M : Matrix (AuxiliarySlotStates n) (AuxiliarySlotStates n) (Op m E)) : Matrix (Fin 2 × AuxiliarySlotStates n) (Fin 2 × AuxiliarySlotStates n) (Op m E) :=
  fun a b => if a.1 = b.1 then M a.2 b.2 else 0

def onPosition0 {n : ℕ} (S : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2 × AuxiliarySlotStates n) (Fin 2 × AuxiliarySlotStates n) (Op m E) :=
  fun a b => if a.2 = b.2 then scalOp (S a.1 b.1) else 0

def one_le_card_tops {n : ℕ} (M : Matrix (Fin 2 × AuxiliarySlotStates n) (Fin 2 × AuxiliarySlotStates n) (Op m E)) :
    Matrix (Fin 2 × Fin 2 × AuxiliarySlotStates n) (Fin 2 × Fin 2 × AuxiliarySlotStates n) (Op m E) :=
  fun a b => if a.2.1 = b.2.1 then M (a.1, a.2.2) (b.1, b.2.2) else 0

def tensorSecondPosition {n : ℕ} (M : Matrix (Fin 2 × AuxiliarySlotStates n) (Fin 2 × AuxiliarySlotStates n) (Op m E)) :
    Matrix (Fin 2 × Fin 2 × AuxiliarySlotStates n) (Fin 2 × Fin 2 × AuxiliarySlotStates n) (Op m E) :=
  fun a b => if a.1 = b.1 then M (a.2.1, a.2.2) (b.2.1, b.2.2) else 0

def Rh12 {n : ℕ} (D : ℂ) : Matrix (Fin 2 × Fin 2 × AuxiliarySlotStates n) (Fin 2 × Fin 2 × AuxiliarySlotStates n) (Op m E) :=
  fun a b => if a.2.2 = b.2.2 then scalOp (Rh D (a.1, a.2.1) (b.1, b.2.1)) else 0

def tr0 {n : ℕ} (M : Matrix (Fin 2 × AuxiliarySlotStates n) (Fin 2 × AuxiliarySlotStates n) (Op m E)) :
    Matrix (Fin 2 × AuxiliarySlotStates n) (Fin 2 × AuxiliarySlotStates n) (Op m E) :=
  fun a b => M (b.1, a.2) (a.1, b.2)

def JRR {n : ℕ} (M : Matrix (AuxiliarySlotStates n) (AuxiliarySlotStates n) (Op m E)) : Matrix (AuxiliarySlotStates (n + 1)) (AuxiliarySlotStates (n + 1)) (Op m E) :=
  fun α β f => J2 (α 0) (β 0) • M (Fin.tail α) (Fin.tail β) f

def capProd (sg : ℂ) (t11 : ℂ → Op m E) : Word → Op m E
  | [] => idOp
  | l :: w => fun φ => capProd sg t11 w (sg • t11 (l.2 : ℂ) φ)

end Waves

namespace Lev

def UUset (L : Lev) (g : Mat L.k0 L.r) : Set (Mat L.k0 L.r) :=
  {h | h ∈ UWset (L.k0 + 1) L.r L.z' ∧ h *ᵥ (g⁻¹ *ᵥ L.z) = g⁻¹ *ᵥ L.z}

def blockU (L : Lev) (h : Matrix (Fin L.k0) (Fin L.k0) ℂ) : Mat L.k0 L.r :=
  fun i j =>
    if hi : L.r ≤ i.val ∧ i.val < L.r + L.k0 then
      (if hj : L.r ≤ j.val ∧ j.val < L.r + L.k0 then h ⟨i.val - L.r, by omega⟩ ⟨j.val - L.r, by omega⟩ else 0)
    else (if i = j then 1 else 0)

def IsFrameU (L : Lev) (g f : Mat L.k0 L.r) : Prop :=
  f ∈ UH (Hpk (L.k0 + 1) L.r) ∧
    (∀ a : Fin L.r, f *ᵥ bvec (eI (L.k0 + 1) L.r a) = bvec (eI (L.k0 + 1) L.r a) ∧
      f *ᵥ bvec (esI (L.k0 + 1) L.r a) = bvec (esI (L.k0 + 1) L.r a)) ∧
    ∀ j : Fin L.k0,
      herm (Hpk (L.k0 + 1) L.r) (f *ᵥ bvec (wI (L.k0 + 1) L.r j.castSucc.castSucc)) (g⁻¹ *ᵥ L.z) = 0 ∧
      herm (Hpk (L.k0 + 1) L.r) (f *ᵥ bvec (wI (L.k0 + 1) L.r j.castSucc.castSucc)) L.z' = 0

open Classical in

def frameU (L : Lev) (g : Mat L.k0 L.r) : Mat L.k0 L.r :=
  if h : ∃ f, L.IsFrameU g f then Classical.choose h else 1

def isoSub (L : Lev) (g : Mat L.k0 L.r) (ρ : Fin L.k0 → ℝ) : Submodule ℂ L.Wq :=
  sSup {S | Formalism.MainNotions.S.IsKTypeOf (Formalism.MainNotions.S.allPos L.k0)
    (fun h => L.π' (L.frameU g * L.blockU h * (L.frameU g)⁻¹)) (lowK (Formalism.MainNotions.S.allPos L.k0) ρ) S}

def HomU (L : Lev) (g : Mat L.k0 L.r) : Set L.Hom :=
  {T | ∀ h ∈ L.UUset g, (L.π (g * h * g⁻¹)).comp T = T.comp (L.π' h)}

def lineSet (L : Lev) (g : Mat L.k0 L.r) (ρ : Fin L.k0 → ℝ) : Set L.Hom :=
  {T | T ∈ L.HomU g ∧ ∀ v ∈ (L.isoSub g ρ)ᗮ, T v = 0}

def IsHSProj (L : Lev) (P : L.Hom →L[ℂ] L.Hom) (S : Set L.Hom) : Prop :=
  P.comp P = P ∧ (∀ A B, Formalism.MainNotions.S.hsInner (P A) B = Formalism.MainNotions.S.hsInner A (P B)) ∧
    (∀ A, P A ∈ S) ∧ ∀ A ∈ S, P A = A

open Classical in

def lineP (L : Lev) (g : Mat L.k0 L.r) (ρ : Fin L.k0 → ℝ) : L.Hom →L[ℂ] L.Hom :=
  if h : ∃ P, L.IsHSProj P (L.lineSet g ρ) then Classical.choose h else 0

def pt (L : Lev) (x : Fin (L.r + 1) → ℂ) : Mat L.k0 L.r := bigCell (L.k0 + 1) L.r (cOf x) (L.μsec (zOf x))

def GGx (L : Lev) (x : Fin (L.r + 1) → ℂ) : ℝ := Complex.normSq (zOf x) - L.T * L.T'

end Lev

noncomputable def sCut {k0 : ℕ} (u u' : Fin (k0 + 1) → ℝ) (I : Set ℝ) : ℝ := by
  classical
  exact if h : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ ρ : Fin k0 → ℝ, Interlace u ρ → Interlace u' ρ →
      ∀ Y ∈ I, 0 < s * (xPoly ρ (Y : ℂ)).re then Classical.choose h else 1

def castOp {E : Type*} {a b : ℕ} (h : a = b) (R : Op a E) : Op b E := h ▸ R

def liftK {m : ℕ} {E : Type*} : (i : ℕ) → Op m E → Op (m + i) E
  | 0, R => R
  | i + 1, R => liftOp (liftK i R)

def Lev.down (Lt : Lev) (i r' : ℕ) (h : i + r' = Lt.r) : Lev where
  k0 := Lt.k0
  r := r'
  z := fun p => Lt.z ⟨p.val + i, by omega⟩
  z' := fun p => Lt.z' ⟨p.val + i, by omega⟩
  Wp := Lt.Wp
  Wq := Lt.Wq
  π := fun g => Lt.π (fun p q => ιLev (Lt.k0 + 1) i r' g (Fin.cast (by omega) p) (Fin.cast (by omega) q))
  π' := fun g => Lt.π' (fun p q => ιLev (Lt.k0 + 1) i r' g (Fin.cast (by omega) p) (Fin.cast (by omega) q))
  μsec := Lt.μsec

def Lev.liftDown (Lt : Lev) (i r' : ℕ) (h : i + r' = Lt.r) (R : (Lt.down i r' h).POp) : Lt.POp :=
  castOp (by show r' + 1 + i = Lt.r + 1; omega) (liftK i R)

section Prods

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Tprod (Y : ℂ) : (i : ℕ) → i ≤ m → Matrix (Fin 2) (Fin 2) (Op (m + 1) E)
  | 0, _ => oneOM
  | i + 1, h => omMul (Tmat (⟨i, by omega⟩ : Fin (m + 1)) Y) (Tprod Y i (by omega))

def TprodStar (Y : ℂ) : (i : ℕ) → i ≤ m → Matrix (Fin 2) (Fin 2) (Op (m + 1) E)
  | 0, _ => oneOM
  | i + 1, h => omMul (TprodStar Y i (by omega)) (TmatStar (⟨i, by omega⟩ : Fin (m + 1)) Y)

def bTprod (w : Word) : (i : ℕ) → i ≤ m → Matrix (AuxiliarySlotStates w.length) (AuxiliarySlotStates w.length) (Op (m + 1) E)
  | 0, _ => oneOM
  | i + 1, h => omMul (bT (⟨i, by omega⟩ : Fin (m + 1)) w) (bTprod w i (by omega))

def uw (w : Word) (i : ℕ) (h : i ≤ m) : AuxiliarySlotStates w.length → Op (m + 1) E :=
  fun β => bTprod w i h β (e1s _)

end Prods

namespace Lev

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def Dom (L : Lev) : Set (Fin (L.r + 1) → ℂ) := {p | 0 < L.GGx p ∧ zOf p ≠ 0}

def IsDiffZ (L : Lev) (O : L.POp) : Prop :=
  ∃ (N : ℕ) (a : Fin N → Fin N → (Fin (L.r + 1) → ℂ) → (L.Hom →L[ℂ] L.Hom)),
    (∀ i j, ContDiffOn ℝ ∞ (a i j) L.Dom) ∧
    ∀ φ : L.PF, ∀ p ∈ L.Dom, O φ p =
      ∑ i : Fin N, ∑ j : Fin N, a i j p ((wirt (Fin.last L.r))^[i] ((wirtBar (Fin.last L.r))^[j] φ) p)

def IsTriDiff (L : Lev) {n : ℕ} (F : Matrix (AuxiliarySlotStates n) (AuxiliarySlotStates n) L.POp) : Prop :=
  (∀ α β, L.IsDiffZ (F α β)) ∧
    (∃ e : AuxiliarySlotStates n ≃ Fin (Fintype.card (AuxiliarySlotStates n)), ∀ α β, e α < e β → ∀ φ : L.PF, ∀ p ∈ L.Dom, F α β φ p = 0) ∧
    ∀ α, ∃ a : (Fin (L.r + 1) → ℂ) → (L.Hom →L[ℂ] L.Hom),
      (∀ p ∈ L.Dom, IsUnit (a p)) ∧ ∀ φ : L.PF, ∀ p ∈ L.Dom, F α α φ p = a p (φ p)

def dw (L : Lev) {n : ℕ} (N : ℕ) (c : AuxiliarySlotStates n → (Fin L.k0 → ℝ) → ℝ) (α : AuxiliarySlotStates n)
    (p : Fin (L.r + 1) → ℂ) (A : L.Hom) : L.Hom :=
  ((Complex.normSq (zOf p) / L.GGx p) ^ N : ℝ) • ∑ᶠ ρ : Fin L.k0 → ℝ, ((c α ρ : ℝ) : ℂ) • L.lineP (L.pt p) ρ A

def act (L : Lev) (h n h' n' : Mat L.k0 L.r) (F : L.GF) : L.GF := fun g =>
  (psi (L.k0 + 1) L.r L.z cStd n * star (psi (L.k0 + 1) L.r L.z' cStd n')) •
    ((L.π h).comp ((F (h⁻¹ * n⁻¹ * g * n' * h')).comp (L.π' h'⁻¹)))

def IsInv (L : Lev) (Θ : L.GF → L.GF) : Prop :=
  ∀ h ∈ UWset (L.k0 + 1) L.r L.z, ∀ n ∈ Nset (L.k0 + 1) L.r, ∀ h' ∈ UWset (L.k0 + 1) L.r L.z',
    ∀ n' ∈ Nset (L.k0 + 1) L.r, ∀ F : L.GF, SmoothOnH (Hpk (L.k0 + 1) L.r) F →
      ∀ g ∈ UH (Hpk (L.k0 + 1) L.r), Θ (L.act h n h' n' F) g = L.act h n h' n' (Θ F) g

def EwordV (L : Lev) {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (w : List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1))) (a : Mat L.k0 L.r → V) :
    Mat L.k0 L.r → V :=
  w.foldr (fun ab f => EabH (Hpk (L.k0 + 1) L.r) ab.1 ab.2 f) a

def AA (L : Lev) : Set (L.GF → L.GF) :=
  {Θ | L.IsInv Θ ∧ ∃ (N : ℕ) (ws : Fin N → List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1)))
    (a : Fin N → Mat L.k0 L.r → (L.Hom →L[ℂ] L.Hom)),
    (∀ j, ∃ U : Set (Mat L.k0 L.r), IsOpen U ∧
      UH (Hpk (L.k0 + 1) L.r) ∩ {g | 0 < Gf (L.k0 + 1) L.r L.z L.z' g} ⊆ U ∧ ContDiffOn ℝ ∞ (a j) U) ∧
    (∀ j, ∀ w : List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1)), ∀ ε : ℝ, 0 < ε →
      ∃ (C : ℝ) (d : ℕ), ∀ g ∈ UH (Hpk (L.k0 + 1) L.r),
        ε ≤ Gf (L.k0 + 1) L.r L.z L.z' g → ‖L.EwordV w (a j) g‖ ≤ C * (1 + matNorm g) ^ d) ∧
    ∀ F : L.GF, SmoothOnH (Hpk (L.k0 + 1) L.r) F → ∀ g ∈ UH (Hpk (L.k0 + 1) L.r),
      0 < Gf (L.k0 + 1) L.r L.z L.z' g → Θ F g = ∑ j, a j g (L.Eword (ws j) F g)}

def wmod (L : Lev) (R : ℂ → Matrix (Fin 2) (Fin 2) L.POp) (sg : ℝ) (u u' : Fin (L.k0 + 1) → ℝ)
    (w : Word) : Mod (L.r + 1) L.Hom w.length :=
  wordMod (fun Y a b => fun φ => ((sg : ℝ) : ℂ) • R Y a b φ) (fun Y => qPoly L.T L.T' u u' Y) w

end Lev

def Big (C : ℝ) (L : Lev) (N : ℕ) (A : ℝ) (mm : ℕ) : Prop :=
  C * ((L.r : ℝ) + 1) ^ 4 * ((N : ℝ) * ((2 * L.r + L.k0 + 2 : ℕ) : ℝ) ^ 2 + ((2 * L.r + L.k0 + 2 : ℕ) : ℝ) ^ 3) ≤ A ∧
  C * ((L.r : ℝ) + 1) ^ 4 * ((N : ℝ) * ((2 * L.r + L.k0 + 2 : ℕ) : ℝ) ^ 2 + ((2 * L.r + L.k0 + 2 : ℕ) : ℝ) ^ 3) ≤ (mm : ℝ)

def HypC (L : Lev) (u u' : Fin (L.k0 + 1) → ℝ) (I : Set ℝ) : Prop :=
  L.Std ∧ L.HC u u' ∧ Formalism.MainNotions.S.IsCutS u u' I ∧ ∃ ρ : Fin L.k0 → ℝ, Interlace u ρ ∧ Interlace u' ρ

namespace Lev

def IsPolyCoef (L : Lev) (a : Mat L.k0 L.r → ℂ) : Prop :=
  ∃ P : MvPolynomial ((Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1)) ⊕
      (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1))) ℂ,
    ∀ g, a g = MvPolynomial.eval (Sum.elim (fun ij => g ij.1 ij.2) (fun ij => star (g ij.1 ij.2))) P

def AApoly (L : Lev) : Set (L.GF → L.GF) :=
  {Θ | L.IsInv Θ ∧ ∃ (N : ℕ) (ws : Fin N → List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1)))
    (a : Fin N → Mat L.k0 L.r → ℂ), (∀ j, L.IsPolyCoef (a j)) ∧
    ∀ F : L.GF, SmoothOnH (Hpk (L.k0 + 1) L.r) F → ∀ g ∈ UH (Hpk (L.k0 + 1) L.r),
      Θ F g = ∑ j, a j g • L.Eword (ws j) F g}

end Lev

def blockK {k : ℕ} (h : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  fun i j => if hi : i.val < k then (if hj : j.val < k then h ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0)
    else (if i = j then 1 else 0)

def isoK {k : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ → (H →L[ℂ] H)) (u : Fin k → ℝ) : Submodule ℂ H :=
  sSup {S | Formalism.MainNotions.S.IsKTypeOf (Formalism.MainNotions.S.allPos k) (fun h => σ (blockK h)) (lowK (Formalism.MainNotions.S.allPos k) u) S}

def lJ (L : Lev) (h : L.Haar) (F : L.GF) : L.GF :=
  besselJ (L.k0 + 1) L.r L.z L.z' cStd L.π L.π' h.μW h.μN h.μW' F

def lbeta (L : Lev) (h : L.Haar) (F F' : L.GF) : ℂ := L.betaB (L.B (lJ L h F)) (L.B (lJ L h F'))

def SuppGe (L : Lev) (ε : ℝ) (F : L.GF) : Prop := ∀ g ∈ tsupport F, ε ≤ Gf (L.k0 + 1) L.r L.z L.z' g

section Deg

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def AAdeg (L : Lev) (ε Dg : ℝ) (d : ℕ) (Θ : L.GF → L.GF) : Prop :=
  ∃ (N : ℕ) (ws : Fin N → List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1)))
    (a : Fin N → Mat L.k0 L.r → (L.Hom →L[ℂ] L.Hom)),
    (∀ j, (ws j).length ≤ d) ∧
    (∀ j, ∃ U : Set (Mat L.k0 L.r), IsOpen U ∧
      UH (Hpk (L.k0 + 1) L.r) ∩ {g | 0 < Gf (L.k0 + 1) L.r L.z L.z' g} ⊆ U ∧ ContDiffOn ℝ ∞ (a j) U) ∧
    (∀ j, ∀ w : List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1)), w.length ≤ d + 5 →
      ∃ C : ℝ, ∀ g ∈ UH (Hpk (L.k0 + 1) L.r), ε ≤ Gf (L.k0 + 1) L.r L.z L.z' g →
        ‖L.EwordV w (a j) g‖ ≤ C * (1 + Lev.matNorm g) ^ Dg) ∧
    ∀ F : L.GF, SmoothOnH (Hpk (L.k0 + 1) L.r) F → ∀ g ∈ UH (Hpk (L.k0 + 1) L.r),
      0 < Gf (L.k0 + 1) L.r L.z L.z' g → Θ F g = ∑ j, a j g (L.Eword (ws j) F g)

end Deg

def LemmaBCont (CB : ℝ) : Prop :=
  ∀ L : Lev, L.Std → ∀ u u', L.HC u u' → ∀ (A : ℝ) (mm : ℕ), Big CB L 0 A mm →
    ∀ h : L.Haar, h.Ok → ∃ C : ℝ, ∀ (F F' : L.GF) (ν ν' : ℝ), L.CC A mm F → L.CC A mm F' →
      (∀ w : List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1)), w.length ≤ mm →
        ∀ g ∈ UH (Hpk (L.k0 + 1) L.r), (1 + Lev.matNorm g) ^ A * ‖L.Eword w F g‖ ≤ ν) →
      (∀ w : List (Fin (2 * L.r + (L.k0 + 1) + 1) × Fin (2 * L.r + (L.k0 + 1) + 1)), w.length ≤ mm →
        ∀ g ∈ UH (Hpk (L.k0 + 1) L.r), (1 + Lev.matNorm g) ^ A * ‖L.Eword w F' g‖ ≤ ν') →
      ‖lbeta L h F F'‖ ≤ C * ν * ν'

def LemmaBAdj (CB : ℝ) : Prop :=
  ∀ L : Lev, L.Std → ∀ u u', L.HC u u' → ∀ μG : Measure (Mt (L.k0 + 1) L.r), Formalism.MainNotions.S.IsHaarOn (UH (Hpk (L.k0 + 1) L.r)) μG →
    ∀ Θ Θs : L.GF → L.GF, Θ ∈ L.AA → Θs ∈ L.AA →
      (∀ F F' : L.GF, SmoothOnH (Hpk (L.k0 + 1) L.r) F → SmoothOnH (Hpk (L.k0 + 1) L.r) F' →
        HasCompactSupport F → HasCompactSupport F' → (∃ ε : ℝ, 0 < ε ∧ SuppGe L ε F ∧ SuppGe L ε F') →
        ∫ x, Formalism.MainNotions.S.hsInner (Θ F (Matrix.of x)) (F' (Matrix.of x)) ∂μG =
          ∫ x, Formalism.MainNotions.S.hsInner (F (Matrix.of x)) (Θs F' (Matrix.of x)) ∂μG) →
    ∀ (ε Dg : ℝ) (d : ℕ), 0 < ε → 0 ≤ Dg → AAdeg L ε Dg d Θ → AAdeg L ε Dg d Θs →
    ∀ (A : ℝ) (mm : ℕ), Big CB L 0 A mm → ∀ h : L.Haar, h.Ok →
      ∀ F F' : L.GF, SmoothOnH (Hpk (L.k0 + 1) L.r) F → SmoothOnH (Hpk (L.k0 + 1) L.r) F' →
        L.CC (A + Dg) (mm + d) F → L.CC (A + Dg) (mm + d) F' → SuppGe L ε F → SuppGe L ε F' →
        lbeta L h (Θ F) F' = lbeta L h F (Θs F')

def LemmaBRad (CB : ℝ) : Prop :=
  ∀ L : Lev, L.Std → ∀ u u', L.HC u u' → ∀ Θ : L.GF → L.GF, Θ ∈ L.AA →
    ∀ (ε Dg : ℝ) (d : ℕ), 0 < ε → 0 ≤ Dg → AAdeg L ε Dg d Θ →
    ∀ (A : ℝ) (mm : ℕ), Big CB L 0 A mm → ∀ h : L.Haar, h.Ok →
      ∀ F : L.GF, SmoothOnH (Hpk (L.k0 + 1) L.r) F → L.CC (A + Dg) (mm + d) F → SuppGe L ε F →
        ∀ g ∈ UH (Hpk (L.k0 + 1) L.r), 0 < Gf (L.k0 + 1) L.r L.z L.z' g →
          (∀ l, Dmin (L.k0 + 1) L.r L.z L.z' g l ≠ 0) →
          ∀ J' : L.GF, SmoothOnH (Hpk (L.k0 + 1) L.r) J' →
            (∃ U : Set (Mat L.k0 L.r), IsOpen U ∧ g ∈ U ∧
              ∀ g' ∈ U, g' ∈ UH (Hpk (L.k0 + 1) L.r) → J' g' = lJ L h F g') →
            lJ L h (Θ F) g = Θ J' g

def LemmaBInt (CB : ℝ) : Prop :=
  ∀ L : Lev, L.Std → ∀ u u', L.HC u u' → ∀ (A : ℝ) (mm : ℕ), Big CB L 0 A mm →
    ∀ h : L.Haar, h.Ok → ∀ F F' : L.GF, L.CC A mm F → L.CC A mm F' →
      MeasureTheory.Integrable (fun x : Fin (L.r + 1) → ℂ => (((∏ a : Fin L.r, Complex.normSq (cOf x a))⁻¹ : ℝ) : ℂ) *
        Formalism.MainNotions.S.hsInner (L.B (lJ L h F) x) (L.B (lJ L h F') x))

theorem lbeta_eq_integral (L : Lev) (h : L.Haar) (F F' : L.GF) :
    lbeta L h F F' = ∫ x : Fin (L.r + 1) → ℂ, (((∏ a : Fin L.r, Complex.normSq (cOf x a))⁻¹ : ℝ) : ℂ) *
      Formalism.MainNotions.S.hsInner (L.B (lJ L h F) x) (L.B (lJ L h F') x) := rfl

def LemmaBThreeClauses (CB : ℝ) : Prop := LemmaBCont CB ∧ LemmaBAdj CB ∧ LemmaBRad CB

def LemmaB (CB : ℝ) : Prop := LemmaBCont CB ∧ LemmaBAdj CB ∧ LemmaBRad CB ∧ LemmaBInt CB

end Formalism.MainNotions.S.TopsChoicePartA
