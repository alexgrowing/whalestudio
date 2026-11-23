import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.TwTrSum

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

def Keeps (B : Block E) (Q : Submodule ℂ B.Hb) : Prop :=
  ∀ (Φ : Matrix B.I B.I (H E B.a B.b → ℂ)) (T : B.Hb →L[ℂ] B.Hb), IsTestM Φ → IsROp B.D Φ T → ∀ f ∈ Q, T f ∈ Q

def Tests (B : Block E) (Q : Submodule ℂ B.Hb) (g : ℕ → B.Hb) : Prop :=
  (∀ j, g j ∈ Qᗮ) ∧
    ∀ j i (M : ℕ), ∫⁻ x, ENNReal.ofReal (wt x ^ (2 * M)) * ‖(g j i : H E B.a B.b → ℂ) x‖ₑ ^ 2 ∂B.D.ν < ⊤

def OrthTo (B : Block E) (g : ℕ → B.Hb) (f : B.I → H E B.a B.b → ℂ) : Prop :=
  ∀ j, ∑ i, ∫ x, starRingEnd ℂ ((g j i : H E B.a B.b → ℂ) x) * f i x ∂B.D.ν = 0

structure GenOk {B : Block E} {Γ : Type} (t : Γ → PT B) : Prop where
  ok : ∀ x, (t x).Ok
  comm : ∀ x y, Commute (t x).op (t y).op
  commStar : ∀ x y, Commute (t x).op (star (t y).op)

structure Eig {B : Block E} {Γ : Type} (t : Γ → PT B) (s : Γ → ℂ) (f : B.I → H E B.a B.b → ℂ) : Prop where
  cont : ∀ i, Continuous (f i)
  ne : f ≠ 0
  inv : LeftInv f
  wl : ∃ M, WL2 B.D M f
  eig : ∀ x, PositivityTheory.Rg.BcB.E.conv B.D.μ (t x).Φ f = s x • f

def Realised {B : Block E} {Γ : Type} (t : Γ → PT B) (a₀ : Γ) (g : ℕ → B.Hb) (s : Γ → ℂ) : Prop :=
  ∃ (sk : ℕ → Γ → ℂ) (f : ℕ → B.I → H E B.a B.b → ℂ), (∀ x, Tendsto (fun k => sk k x) atTop (𝓝 (s x))) ∧
    ∀ k, sk k a₀ ≠ 0 ∧ Eig t (sk k) (f k) ∧ OrthTo B g (f k)

structure Cmb (B : Block E) : Type 1 where
  J : Type
  s : Finset J
  c : J → ℂ
  t : J → PT B

namespace Cmb

variable {B : Block E} (C : Cmb B)

def Φ : Matrix B.I B.I (H E B.a B.b → ℂ) := ∑ j ∈ C.s, C.c j • (C.t j).Φ

def op : B.Hb →L[ℂ] B.Hb := ∑ j ∈ C.s, C.c j • (C.t j).op

def val (χa : InfinitePlace E → Inf B.a) (χb : InfinitePlace E → Inf B.b) : ℂ := ∑ j ∈ C.s, C.c j * (C.t j).val χa χb

def Ok (ψ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ)) (R : ℝ) : Prop :=
  ∀ j ∈ C.s, (C.t j).Ok ∧ (C.t j).ψ = ψ ∧ (C.t j).T ≤ R ∧ (C.t j).r ≤ R

end Cmb

def Rep (B : Block E) (χa : InfinitePlace E → Inf B.a) (χb : InfinitePlace E → Inf B.b)
    (ψ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ)) (v : ℂ) (R : ℝ) (U : B.Hb →L[ℂ] B.Hb) : Prop :=
  ∃ C : Cmb B, C.Ok ψ R ∧ C.val χa χb = v ∧ C.op = U

def Ml (l : InfinitePlace E → DomWeight n) : Mods E n := fun v => lefE n (l v).w

def Tl (l : InfinitePlace E → DomWeight n) : Ops (Ml l) := fun v => lefT n (l v).w

def chi (l : InfinitePlace E → DomWeight n) : InfinitePlace E → Inf n := fun v => infOf (l v).w

structure Ar (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b) (D : Dom E a b) where
  μa : Measure (G a)
  μb : Measure (G b)
  ν : Measure (Hf E a b)
  ha : μa.IsHaarMeasure
  hb : μb.IsHaarMeasure
  hν : ν.IsHaarMeasure
  hν' : ν.IsMulRightInvariant
  compat : Compat D μa μb ν
  c : ℝ
  c_nonneg : 0 ≤ c
  ca : ∀ g h : GA E a, logSize (g * h) ≤ logSize g + logSize h + c
  cb : ∀ g h : GA E b, logSize (g * h) ≤ logSize g + logSize h + c
  bump : ℝ → ℝ
  T : ℝ
  T_nonneg : 0 ≤ T
  isBump : IsBump bump T
  ka : List (Bool × ℕ) → Kers (Ml l₁)
  kb : List (Bool × ℕ) → Kers (Ml l₂)
  kera : ∀ w v, IsKer μa (Ml l₁ v) w bump (ka w v)
  kerb : ∀ w v, IsKer μb (Ml l₂ v) w bump (kb w v)
  one : (∏ v, coshT bump (cas (chi l₁ v))) * ∏ v, coshT bump (cas (chi l₂ v)) = 1

structure Lv (a b : ℕ) (Z : Finset (Pl E)) where
  L₁ : ∀ w : Pl E, Subgroup (GLw a w)
  L₂ : ∀ w : Pl E, Subgroup (GLw b w)
  open₁ : ∀ w, IsOpen (L₁ w : Set (GLw a w))
  open₂ : ∀ w, IsOpen (L₂ w : Set (GLw b w))
  le₁ : ∀ w, L₁ w ≤ KGL w a
  le₂ : ∀ w, L₂ w ≤ KGL w b
  off : ∀ w ∉ Z, L₁ w = KGL w a ∧ L₂ w = KGL w b

def Lv.ln {Z : Finset (Pl E)} (L : Lv a b Z) (w : Pl E) : LF a b w :=
  (((L.L₁ w).prod (L.L₂ w) : Subgroup _) : Set (GLw a w × GLw b w)).indicator
    fun _ => ((((L.L₁ w).prod (L.L₂ w)).relIndex (K2 a b w) : ℕ) : ℂ)

def Lv.Fix {Z : Finset (Pl E)} (L : Lv a b Z) (φ : ∀ w : Pl E, LF a b w) : Prop :=
  ∀ w ∈ Z, IsHecke ((L.L₁ w).prod (L.L₂ w)) (φ w)

def Kg (S : Set (Pl E)) (L : ∀ w : Pl E, Subgroup (GLw n w)) : Subgroup (GL (Fin n) (Af E)) :=
  ⨅ w ∈ S, (L w).comap (GeneralLinearGroup.map (pLoc E w)) ⊓
    if IsSplitAt w then (L w).comap ((GeneralLinearGroup.map (pLoc E w)).comp (thF E n)) else ⊤

abbrev Gam (a b : ℕ) (S : Set (Pl E)) (Z : Finset (Pl E)) : Type :=
  Unit ⊕ (InfinitePlace E × Bool × ℕ × Bool) ⊕ ({w : Pl E // w ∈ S ∧ w ∉ Z} × (Fin (a + 1) × Fin (b + 1)) × Bool) ⊕ Unit

def Gam.arch {S : Set (Pl E)} {Z : Finset (Pl E)} : Gam a b S Z → Prop
  | .inl _ => True
  | .inr (.inl _) => True
  | .inr (.inr _) => False

namespace Ar

variable {l₁ : InfinitePlace E → DomWeight a} {l₂ : InfinitePlace E → DomWeight b} {D : Dom E a b} (A : Ar l₁ l₂ D)

abbrev blk : Block E :=
  ⟨a, b, D, Ml l₁, Ml l₂, Unit, A.μa, A.μb, A.ν, A.ha, A.hb, A.hν, A.hν', A.compat, A.c, A.c_nonneg, A.ca, A.cb⟩

def valW {m : ℕ} (w : List (Bool × ℕ)) (χ : Inf m) : ℂ := zVal w χ * coshT A.bump (cas χ)

def pt (wa wb : InfinitePlace E → List (Bool × ℕ)) (ψ : Matrix Unit Unit (Hf E a b → ℂ)) : PT A.blk :=
  ⟨fun v => A.ka (wa v) v, fun v => A.kb (wb v) v, fun v => A.valW (wa v), fun v => A.valW (wb v), A.T, ψ,
    PositivityTheory.Rg.BcB.F.sizeOf ψ⟩

def ptB (ψ : Matrix Unit Unit (Hf E a b → ℂ)) : PT A.blk := A.pt (fun _ => []) (fun _ => []) ψ

def ff (S : Set (Pl E)) (φ₁ φ₂ : ∀ w : Pl E, LF a b w) : Matrix Unit Unit (Hf E a b → ℂ) :=
  fun _ _ h => A.blk.vol⁻¹ * finFn S φ₁ φ₂ h

variable (S : Set (Pl E)) {Z : Finset (Pl E)} (L : Lv a b Z)

def fx (T : Finset (Pl E)) (φ : ∀ w : Pl E, LF a b w) (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) :
    Matrix Unit Unit (Hf E a b → ℂ) := A.ff S (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂)

def hk (T : Finset (Pl E)) (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) : Matrix Unit Unit (Hf E a b → ℂ) :=
  A.fx S L T L.ln e₁ e₂

def idm : Matrix Unit Unit (Hf E a b → ℂ) := A.ff S L.ln L.ln

def hk1 (w : Pl E) (p : Fin (a + 1) × Fin (b + 1)) (side : Bool) : Matrix Unit Unit (Hf E a b → ℂ) :=
  A.hk S L {w} (fun _ => if side then .one else .gen p) (fun _ => if side then .gen p else .one)

def gen (T : Finset (Pl E)) (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) : Gam a b S Z → PT A.blk
  | .inl _ => A.ptB (A.idm S L)
  | .inr (.inl x) => A.pt (fun v => if v = x.1 ∧ x.2.2.2 = false then [(x.2.1, x.2.2.1)] else [])
      (fun v => if v = x.1 ∧ x.2.2.2 = true then [(x.2.1, x.2.2.1)] else []) (A.idm S L)
  | .inr (.inr (.inl x)) => A.ptB (A.hk1 S L x.1.1 x.2.1 x.2.2)
  | .inr (.inr (.inr _)) => A.ptB (A.hk S L T e₁ e₂)

def tw (_ : Ar l₁ l₂ D) : Matrix (Io (Ml l₁) (Ml l₂) Unit) (Io (Ml l₁) (Ml l₂) Unit) ℂ := opM (Tl l₁) (Tl l₂) 1

end Ar

def LevelF {ι : Type} (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E))) (f : ι → H E a b → ℂ) : Prop :=
  ∀ i, ∀ u₁ ∈ K₁, ∀ u₂ ∈ K₂, ∀ x, f i (x * (finGL E a u₁, finGL E b u₂)) = f i x

def SmSlices {ι : Type} (f : ι → H E a b → ℂ) : Prop :=
  (∀ i m₂, ∃ φ : Sm E a, φ.1 = fun x => f i (x, m₂)) ∧ ∀ i m₁, ∃ φ : Sm E b, φ.1 = fun x => f i (m₁, x)

def Sees (B : Block E) (g : ℕ → B.Hb) (X : Set (CuspSub E B.a)) (K : Subgroup (GL (Fin B.a) (Af E)))
    (W : Submodule ℂ (Kinf E B.a → ℂ)) : Prop :=
  ∀ f : B.I → H E B.a B.b → ℂ, OrthTo B g f → ∀ i m₂, ∀ φ : Sm E B.a, (φ.1 = fun x => f i (x, m₂)) → φ ≠ 0 → TypeB K W φ →
    ∀ π ∈ X, ∀ ψ ∈ π.V, ∀ z : ℂ, ¬ ∀ y, φ.1 y = ψ.1 y * Complex.exp (z * logAbs y.val.det)

end UpperTheory.Zero.ConvolutionTheory.EB
