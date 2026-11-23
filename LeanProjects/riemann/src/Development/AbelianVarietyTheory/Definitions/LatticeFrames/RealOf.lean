import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)

def JetS (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z)) (s : ℕ → ℂ) : Prop :=
  ∀ j (hj : j + 1 ≤ B.R.m), s j ≠ 0 ∧ ∀ f, IsHol θ ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) ψ f → ∀ P,
    pureTensorO ψ θ _ _ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 =
      jetP _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) (s j) (ColDat.xiS θ j hj f) P

def lowOf : (FrN (I.rec7 l Z) (B.R.N B.R.m) → ℂ) →ₗ[ℂ] (FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) :=
  fnOf _ (shiftOf (sgT (D := I.rec7 l Z) u)) 1 ∘ₗ (I.perIn u I.mu0).br B.fields.emb B.embLL (B.hcW u) ∘ₗ
    Formalism.L2.Col.polOf _ (shiftOf (Formalism.L2.Forms.lamT (D := I.rec7 l Z) u B.R.m)) ⟨fun _ => 1, fun _ => by simp⟩

variable {I l Z} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z))

@[reducible] def realOf (s : ℕ → ℂ)
    (J : SmT R.MX → GA (I.rec7 l Z) (I.rec7 l Z).sp.X' → FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) : RealD (commOf R u g) where
  N := B.R.N
  hN := rankN (I.rec7 l Z)
  NT := B.R.N B.R.m - 1
  hT := rankP (I.rec7 l Z)
  fr := fun _ => ⟨fun y => ⟨y.1, y.2⟩, fun y => ⟨y.1, y.2⟩, fun _ => rfl, fun _ => rfl⟩
  lam := Formalism.L2.Forms.lamT (D := I.rec7 l Z) u
  n := fun j τ => (shiftOf (Formalism.L2.Forms.lamT (D := I.rec7 l Z) u j) τ + (I.chain l u I.mu0).sSharp j τ).toNat
  sS := (I.chain l u I.mu0).sSharp
  sD := (I.chain l u I.mu0).sDiv
  sc := fun j τ => if s j = 0 then 1 else s j / I.J.cD τ
  BT := fun _ => 1
  sg := sgT (D := I.rec7 l Z) u
  J := J
  low := fun _ h => Eq.rec (motive := fun n _ => (FrN (I.rec7 l Z) (B.R.N n) → ℂ) →ₗ[ℂ] (FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ))
    (lowOf I l Z u) h.symm

def JOf (j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ))
    (J : SmT R.MX → GA (I.rec7 l Z) (I.rec7 l Z).sp.X' → FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) : Prop :=
  ∀ v, ∀ k ∈ GinfC (I.rec7 l Z).sp.X', ∀ z z' : FrN (I.rec7 l Z) (B.R.N B.R.m - 1),
    IsTr (infM R.θ _ (rankP (I.rec7 l Z)) k) z z' → J v k z' = j v ⟨z.1, z.2⟩

variable (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) {t : T} (r : RowCh R P u g t) {a : I.ι} (k : ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u a))
  (tl : ColT I l u a B.R.m → CXP R P t → ℂ)

@[reducible] def clsKOf (s : ℕ → ℂ)
    (J : SmT R.MX → GA (I.rec7 l Z) (I.rec7 l Z).sp.X' → FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) (A : TwDat I l Z u a k.Ch) :
    ClsK (realOf u R g s J) (tupOf R P u g t r k tl) where
  cl := fun j β => {c // A.chOf j c = β}
  fin := fun j _ => letI := (I.chain l u a).clsFin j; Subtype.fintype _
  U := A.U
  chi := A.chi
  h := A.h
  val := fun _ _ ψ c z => ψ c.1 ⟨z.1, z.2⟩
  abelian₂ := fun j _ _ c c' => A.abelian₂ j c.1 c'.1

def PinCh (c₀ : ℕ → ℂ) (A : TwDat I l Z u a k.Ch) (w : ∀ j, k.Ch j → k.Ch (j + 1) → ℂ) : Prop :=
  PinColT A R.ψ R.θ g.x g.vac c₀ k.kom k.dd w k.Ram k.rd k.cK

end GlobalTheory.AdForm
