import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.CommStar

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

structure Alg {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Q : Submodule ℂ H) [CompleteSpace Q]
    {Γ : Type} (op : Γ → (H →L[ℂ] H)) (v : Γ → ℂ) : Type 1 where
  B : Type
  [cr : CommRing B]
  [sr : StarRing B]
  [al : Algebra ℂ B]
  [sm : StarModule ℂ B]
  R : B →⋆ₐ[ℂ] (Q →L[ℂ] Q)
  P : B →⋆ₐ[ℂ] ℂ
  F : B →⋆ₐ[ℂ] (H →L[ℂ] H)
  ι : Γ → B
  hF : ∀ x, F (ι x) = op x
  hP : ∀ x, P (ι x) = v x
  hR : ∀ y (q : Q), (R y q : H) = F y q
  top : StarAlgebra.adjoin ℂ (Set.range ι) = ⊤

attribute [instance] Alg.cr Alg.sr Alg.al Alg.sm

def AlgEx : Prop := ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Q : Submodule ℂ H)
  [CompleteSpace Q] (Γ : Type) (op : Γ → (H →L[ℂ] H)) (v : Γ → ℂ), (∀ x y, Commute (op x) (op y)) →
  (∀ x y, Commute (op x) (star (op y))) → (∀ x, ∀ f ∈ Q, op x f ∈ Q ∧ star (op x) f ∈ Q) → Nonempty (Alg Q op v)

def PeakAlg : Prop := ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Q : Submodule ℂ H)
  [CompleteSpace Q] (Γ : Type) (op : Γ → (H →L[ℂ] H)) (v : Γ → ℂ) (𝔄 : Alg Q op v) (arch : Γ → Prop) (a₀ x : Γ) (ρ : ℝ),
  arch a₀ → v a₀ = 1 → 0 < ρ →
  (∀ s : 𝔄.B →⋆ₐ[ℂ] ℂ, (∀ y, ‖s y‖ ≤ ‖𝔄.R y‖) → (∀ γ, arch γ → s (𝔄.ι γ) = v γ) → ‖s (𝔄.ι x)‖ < ρ) →
  ∃ (J : Type) (_ : Fintype J) (c : J → ℂ) (w : J → List ({γ // arch γ} × Bool)),
    ∑ j, c j * wdVal (fun γ : {γ // arch γ} => v γ) (w j) = 1 ∧
      ‖(op x * ((∑ j, c j • wdVal (fun γ : {γ // arch γ} => op γ) (w j)) * op a₀)) ∘L Q.subtypeL‖ < ρ

def PowNorm : Prop := ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Q : Submodule ℂ H) (U : H →L[ℂ] H) (ρ : ℝ),
  (∀ f ∈ Q, U f ∈ Q) → ‖U ∘L Q.subtypeL‖ ≤ ρ → ∀ k : ℕ, (∀ f ∈ Q, (U ^ k) f ∈ Q) ∧ ‖(U ^ k) ∘L Q.subtypeL‖ ≤ ρ ^ k

def ConvMul : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (f : B.I → H E B.a B.b → ℂ), (∀ i, Continuous (f i)) →
  (∀ t t' : PT B, t.Ok → t'.Ok → PositivityTheory.Rg.BcB.E.conv B.D.μ (t.mul t').Φ f =
    PositivityTheory.Rg.BcB.E.conv B.D.μ t.Φ (PositivityTheory.Rg.BcB.E.conv B.D.μ t'.Φ f)) ∧
  ∀ ψ ψ' : Matrix B.κ B.κ (Hf E B.a B.b → ℂ), IsFinM ψ → IsFinM ψ' →
    convF B.ν (mulF B.ν ψ ψ') f = convF B.ν ψ (convF B.ν ψ' f) ∧ convF B.ν (ψ + ψ') f = convF B.ν ψ f + convF B.ν ψ' f ∧
      ∀ c : ℂ, convF B.ν (c • ψ) f = c • convF B.ν ψ f ∧ convF B.ν ψ (c • f) = c • convF B.ν ψ f

def RealAlg : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (Q : Submodule ℂ B.Hb) [CompleteSpace Q] (Γ : Type) [Countable Γ]
  (t : Γ → PT B) (v : Γ → ℂ) (𝔄 : Alg Q (fun x => (t x).op) v) (a₀ : Γ) (g : ℕ → B.Hb) (s : 𝔄.B →⋆ₐ[ℂ] ℂ), (∀ x, (t x).Ok) →
  Keeps B Q → Tests B Q g → (∀ y, ‖s y‖ ≤ ‖𝔄.R y‖) → s (𝔄.ι a₀) ≠ 0 → Realised t a₀ g fun x => s (𝔄.ι x)

def RepAlg : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) χa χb,
  (∀ (C : Cmb B) ψ R, C.Ok ψ R → IsTestM C.Φ ∧ IsROp B.D C.Φ C.op) ∧
  (∀ t : PT B, t.Ok → Rep B χa χb t.ψ (t.val χa χb) (max t.T t.r) t.op) ∧
  (∀ ψ v R R' U, R ≤ R' → Rep B χa χb ψ v R U → Rep B χa χb ψ v R' U) ∧
  ∀ ψ ψ' v v' R R' U U', Rep B χa χb ψ v R U → Rep B χa χb ψ' v' R' U' →
    Rep B χa χb (mulF B.ν ψ ψ') (v * v') (R + R' + B.c) (U * U')

def WordRep : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) χa χb (Γ : Type) (t : Γ → PT B) (t₀ : PT B) (J : Type) [Fintype J] (c : J → ℂ)
  (w : J → List (Γ × Bool)), (∀ v, IsHerm (χa v)) → (∀ v, IsHerm (χb v)) → t₀.Ok → (∀ x, (t x).Ok ∧ (t x).ψ = t₀.ψ) →
  mulF B.ν t₀.ψ t₀.ψ = t₀.ψ → adjF t₀.ψ = t₀.ψ → ∃ R, 0 ≤ R ∧
    Rep B χa χb t₀.ψ ((∑ j, c j * wdVal (fun x => (t x).val χa χb) (w j)) * t₀.val χa χb) R
      ((∑ j, c j • wdVal (fun x => (t x).op) (w j)) * t₀.op)

def PeakRun : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Block E) (Q : Submodule ℂ B.Hb) [CompleteSpace Q] χa χb (Γ : Type) [Countable Γ]
  (t : Γ → PT B) (arch : Γ → Prop) (a₀ x : Γ) (g : ℕ → B.Hb) (ρ : ℝ), GenOk t → Keeps B Q → Tests B Q g →
  (∀ v, IsHerm (χa v)) → (∀ v, IsHerm (χb v)) → arch a₀ → (t a₀).val χa χb = 1 → (∀ γ, arch γ → (t γ).ψ = (t a₀).ψ) →
  mulF B.ν (t a₀).ψ (t a₀).ψ = (t a₀).ψ → adjF (t a₀).ψ = (t a₀).ψ → 0 < ρ →
  (∀ s : Γ → ℂ, (∀ γ, arch γ → s γ = (t γ).val χa χb) → Realised t a₀ g s → ‖s x‖ < ρ) →
  ∃ V R, 0 ≤ R ∧ Rep B χa χb (t a₀).ψ 1 R V ∧ ‖((t x).op * V) ∘L Q.subtypeL‖ < ρ

def ArEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
  (D : Dom E a b), Nonempty (Ar l₁ l₂ D)

def LefL : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
  (D : Dom E a b) (A : Ar l₁ l₂ D), VCAll A.blk (Tl l₁) (Tl l₂) ∧
  ∀ v k k' val val' T, IsMult A.μa (Ml l₁ v) k val T → IsMult A.μb (Ml l₂ v) k' val' T →
    LefAt A.μa A.μb (l₁ v) (l₂ v) (val (chi l₁ v) * val' (chi l₂ v))
      fun y => phiOf (Ml l₁ v) (Tl l₁ v) k y.1 * phiOf (Ml l₂ v) (Tl l₂ v) k' y.2

def PtOk : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
  (D : Dom E a b) (A : Ar l₁ l₂ D), (∀ v, IsHerm (chi l₁ v)) ∧ (∀ v, IsHerm (chi l₂ v)) ∧
  (∀ wa wb ψ, IsFinM ψ → (A.pt wa wb ψ).Ok) ∧ (∀ ψ, (A.ptB ψ).val (chi l₁) (chi l₂) = 1) ∧
  ∀ wa wb ψ χa χb, (A.pt wa wb ψ).val χa χb =
    (∏ v, zVal (wa v) (χa v)) * (∏ v, zVal (wb v) (χb v)) * (A.ptB ψ).val χa χb

def LvEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Z : Finset (Pl E)) (φ : ∀ w : Pl E, LF a b w),
  (∀ w ∈ Z, Lc (K2 a b w) (φ w)) → ∃ L : Lv a b Z, L.Fix φ

def LocAlg : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (Z : Finset (Pl E)) (L : Lv a b Z) (w : Pl E),
  IsHecke ((L.L₁ w).prod (L.L₂ w)) (L.ln w) ∧ lfStar (L.ln w) = L.ln w ∧ (w ∉ Z → L.ln w = (K2 a b w : Set _).indicator 1) ∧
  (∀ f : LF a b w, IsHecke ((L.L₁ w).prod (L.L₂ w)) f → PositivityTheory.Rg.BcN.F2.mconv f (L.ln w) = f ∧ PositivityTheory.Rg.BcN.F2.mconv (L.ln w) f = f) ∧
  ∀ f : LF a b w, IsHecke (K2 a b w) f → PositivityTheory.Rg.BcN.F2.mconv f ((K2 a b w : Set _).indicator 1) = f ∧
    PositivityTheory.Rg.BcN.F2.mconv ((K2 a b w : Set _).indicator 1) f = f ∧ IsHecke (K2 a b w) (lfStar f)

def SphComm2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (f f' : LF a b w), IsHecke (K2 a b w) f → IsHecke (K2 a b w) f' →
  PositivityTheory.Rg.BcN.F2.mconv f f' = PositivityTheory.Rg.BcN.F2.mconv f' f

def PositionTest : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (S : Set (Pl E)) (Z : Finset (Pl E)) (L : Lv a b Z), SplitIn S Z →
  L.Fix L.ln ∧ IsTestP L.ln ∧ ∀ φ, L.Fix φ → (∀ w ∈ Z, Lc (K2 a b w) (φ w)) ∧ ∀ T e, IsTestP (intersection_update_fsHerm_neg_one Z T φ e)

def FfAlg : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
  (D : Dom E a b) (A : Ar l₁ l₂ D) (S : Set (Pl E)), IsSection S → A.blk.vol ≠ 0 ∧
  ∀ φ₁ φ₂ : ∀ w : Pl E, LF a b w, IsTestP φ₁ → IsTestP φ₂ → IsFinM (A.ff S φ₁ φ₂) ∧
    adjF (A.ff S φ₁ φ₂) = A.ff S (fun w => lfStar (φ₁ w)) (fun w => lfStar (φ₂ w)) ∧
    (IsTestP fun w => lfStar (φ₁ w)) ∧ (IsTestP fun w => lfStar (φ₂ w)) ∧
    ∀ φ₁' φ₂' : ∀ w : Pl E, LF a b w, IsTestP φ₁' → IsTestP φ₂' → mulF A.ν (A.ff S φ₁ φ₂) (A.ff S φ₁' φ₂') =
      A.ff S (fun w => PositivityTheory.Rg.BcN.F2.mconv (φ₁ w) (φ₁' w)) (fun w => PositivityTheory.Rg.BcN.F2.mconv (φ₂ w) (φ₂' w))

def HkMul : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
  (D : Dom E a b) (A : Ar l₁ l₂ D) (S : Set (Pl E)) (Z : Finset (Pl E)) (L : Lv a b Z), IsSection S → SplitIn S Z →
  IsFinM (A.idm S L) ∧ mulF A.ν (A.idm S L) (A.idm S L) = A.idm S L ∧ adjF (A.idm S L) = A.idm S L ∧
  (∀ T, A.hk S L T (fun _ => .one) (fun _ => .one) = A.idm S L) ∧ (∀ e₁ e₂, A.hk S L ∅ e₁ e₂ = A.idm S L) ∧
  (∀ T φ e₁ e₂, L.Fix φ → IsFinM (A.fx S L T φ e₁ e₂) ∧ mulF A.ν (A.fx S L T φ e₁ e₂) (A.idm S L) = A.fx S L T φ e₁ e₂ ∧
    ∀ e₁' e₂', mulF A.ν (A.fx S L T φ e₁ e₂) (A.hk S L T e₁' e₂') =
      A.fx S L T φ (fun w => (e₁ w).mul (e₁' w)) (fun w => (e₂ w).mul (e₂' w))) ∧
  (∀ T e₁ e₂, IsFinM (A.hk S L T e₁ e₂) ∧ mulF A.ν (A.idm S L) (A.hk S L T e₁ e₂) = A.hk S L T e₁ e₂) ∧
  ∀ T w e₁ e₂, w ∉ T → A.hk S L (insert w T) e₁ e₂ = mulF A.ν (A.hk S L {w} e₁ e₂) (A.hk S L T e₁ e₂)

def HkComm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
  (D : Dom E a b) (A : Ar l₁ l₂ D) (S : Set (Pl E)) (Z : Finset (Pl E)) (L : Lv a b Z), IsSection S → SplitIn S Z →
  ∀ T T' e₁ e₂ e₁' e₂', mulF A.ν (A.hk S L T e₁ e₂) (A.hk S L T' e₁' e₂') = mulF A.ν (A.hk S L T' e₁' e₂') (A.hk S L T e₁ e₂) ∧
    mulF A.ν (A.hk S L T e₁ e₂) (adjF (A.hk S L T' e₁' e₂')) = mulF A.ν (adjF (A.hk S L T' e₁' e₂')) (A.hk S L T e₁ e₂)

def HkLin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
  (D : Dom E a b) (A : Ar l₁ l₂ D) (S : Set (Pl E)) (Z : Finset (Pl E)) (L : Lv a b Z), IsSection S → SplitIn S Z →
  ∀ w ∈ S, w ∉ Z → ∀ (x y z : Ex (Fin (a + 1) × Fin (b + 1))) (c : ℂ),
    A.hk S L {w} (fun _ => x.add y) (fun _ => z) = A.hk S L {w} (fun _ => x) (fun _ => z) + A.hk S L {w} (fun _ => y) (fun _ => z) ∧
    A.hk S L {w} (fun _ => .smul c x) (fun _ => z) = c • A.hk S L {w} (fun _ => x) (fun _ => z) ∧
    (IsSplitAt w →
      A.hk S L {w} (fun _ => z) (fun _ => x.add y) = A.hk S L {w} (fun _ => z) (fun _ => x) + A.hk S L {w} (fun _ => z) (fun _ => y) ∧
      A.hk S L {w} (fun _ => z) (fun _ => .smul c x) = c • A.hk S L {w} (fun _ => z) (fun _ => x)) ∧
    (¬ IsSplitAt w → A.hk S L {w} (fun _ => z) (fun _ => x) = A.hk S L {w} (fun _ => z) (fun _ => y))

def GenSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
  (D : Dom E a b) (A : Ar l₁ l₂ D) (S : Set (Pl E)) (Z : Finset (Pl E)) (L : Lv a b Z), IsSection S → SplitIn S Z →
  ∀ T e₁ e₂, GenOk (A.gen S L T e₁ e₂) ∧ Countable (Gam a b S Z)

def KgFacts : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (Z : Finset (Pl E)) (L : ∀ w : Pl E, Subgroup (GLw n w)),
  IsSection S → SplitIn S Z → (∀ w, IsOpen (L w : Set (GLw n w)) ∧ L w ≤ KGL w n) → (∀ w ∉ Z, L w = KGL w n) →
  IsOpen (Kg S L : Set (GL (Fin n) (Af E))) ∧ Kg S L ≤ Kf E n ∧ ∀ w, Off Z w → ∀ k ∈ KGL w n, locGL E n w k ∈ Kg S L

def IdmAct : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
  (D : Dom E a b) (A : Ar l₁ l₂ D) (S : Set (Pl E)) (Z : Finset (Pl E)) (L : Lv a b Z), IsSection S → SplitIn S Z →
  (∀ x y, ∀ u₁ ∈ Kg S L.L₁, ∀ u₂ ∈ Kg S L.L₂, ∀ h, A.idm S L x y ((u₁, u₂) * h) = A.idm S L x y h) ∧
  (∀ T φ e₁ e₂, L.Fix φ → ∀ x y, ∀ u₁ ∈ Kg S L.L₁, ∀ u₂ ∈ Kg S L.L₂, ∀ h,
    A.fx S L T φ e₁ e₂ x y ((u₁, u₂) * h) = A.fx S L T φ e₁ e₂ x y h) ∧
  ∀ f : A.blk.I → H E a b → ℂ, LevelF (Kg S L.L₁) (Kg S L.L₂) f → convF A.ν (A.idm S L) f = f

def HkVal : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
  (D : Dom E a b) (A : Ar l₁ l₂ D) (S : Set (Pl E)) (Z : Finset (Pl E)) (L : Lv a b Z), IsSection S → SplitIn S Z →
  ∀ (f : A.blk.I → H E a b → ℂ) (t₁ t₂ : Pl E → Fin (a + 1) × Fin (b + 1) → ℂ) (T : Finset (Pl E)) (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))),
    TEv S T e₂ → Disjoint T Z → (∀ i, Continuous (f i)) → LevelF (Kg S L.L₁) (Kg S L.L₂) f →
    (∀ w ∈ T, ∀ p, convF A.ν (A.hk1 S L w p false) f = t₁ w p • f ∧
      (IsSplitAt w → convF A.ν (A.hk1 S L w p true) f = t₂ w p • f)) →
    convF A.ν (A.hk S L T e₁ e₂) f = (∏ w ∈ T, (e₁ w).ev (t₁ w) * (e₂ w).ev (t₂ w)) • f

def SatRead₁ : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
  (D : Dom E a b) (A : Ar l₁ l₂ D) (S : Set (Pl E)) (Z : Finset (Pl E)) (L : Lv a b Z), IsSection S → SplitIn S Z →
  ∀ (f : A.blk.I → H E a b → ℂ), f ≠ 0 → (∀ i, Continuous (f i)) → LevelF (Kg S L.L₁) (Kg S L.L₂) f → SmSlices f →
    ∀ w ∈ S, w ∉ Z → ∀ t : Fin (a + 1) × Fin (b + 1) → ℂ, (∀ p, convF A.ν (A.hk1 S L w p false) f = t p • f) →
    ∃ B₁ B₂ : Multiset ℂˣ, B₁.card = a ∧ B₂.card = b ∧ (∀ p, t p = satEig (qV E w) a B₁ p.1 * satEig (qV E w) b B₂ p.2) ∧
      (∀ φ ∈ slices₁ f, φ ≠ 0 → IsSatVecGL w (UpperTheory.V.Cj.S.fL a w) φ B₁) ∧
      ∀ φ ∈ slices₂ f, φ ≠ 0 → IsSatVecGL w (UpperTheory.V.Cj.S.fL b w) φ B₂

def SatRead₂ : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
  (D : Dom E a b) (A : Ar l₁ l₂ D) (S : Set (Pl E)) (Z : Finset (Pl E)) (L : Lv a b Z), IsSection S → SplitIn S Z →
  ∀ (f : A.blk.I → H E a b → ℂ), f ≠ 0 → (∀ i, Continuous (f i)) → LevelF (Kg S L.L₁) (Kg S L.L₂) f → SmSlices f →
    ∀ w ∈ S, w ∉ Z → IsSplitAt w → ∀ t : Fin (a + 1) × Fin (b + 1) → ℂ, (∀ p, convF A.ν (A.hk1 S L w p true) f = t p • f) →
    ∃ B₁ B₂ : Multiset ℂˣ, B₁.card = a ∧ B₂.card = b ∧
      (∀ p, t p = satEig (qV E w) a (inv B₁) p.1 * satEig (qV E w) b (inv B₂) p.2) ∧
      (∀ φ ∈ slices₁ f, φ ≠ 0 → IsSatVecGL (cPl w) (UpperTheory.V.Cj.S.fL a (cPl w)) φ B₁) ∧
      ∀ φ ∈ slices₂ f, φ ≠ 0 → IsSatVecGL (cPl w) (UpperTheory.V.Cj.S.fL b (cPl w)) φ B₂

def PackStep : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b),
  ∃ (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ W₁ ∧ FiniteDimensional ℂ W₂ ∧
  ∀ (D : Dom E a b) (A : Ar l₁ l₂ D) (S : Set (Pl E)) (Z : Finset (Pl E)) (L : Lv a b Z), IsSection S → SplitIn S Z →
    ∀ T e₁ e₂ (s : Gam a b S Z → ℂ) (f : A.blk.I → H E a b → ℂ), s (.inl ()) ≠ 0 → Eig (A.gen S L T e₁ e₂) s f →
    ∃ (χa : InfinitePlace E → Inf a) (χb : InfinitePlace E → Inf b),
      (∀ v r m, GlobalTheory.Dec.gelfVal (χa v r) m = s (.inr (.inl (v, r, m, false))) / s (.inl ())) ∧
      (∀ v r m, GlobalTheory.Dec.gelfVal (χb v r) m = s (.inr (.inl (v, r, m, true))) / s (.inl ())) ∧
      LevelF (Kg S L.L₁) (Kg S L.L₂) f ∧ SmSlices f ∧
      (∀ φ ∈ slices₁ f, IsAutForm φ ∧ TypeB (Kg S L.L₁) W₁ φ ∧ UpperTheory.V.Cj.S.HasCap φ (mOf χa)) ∧
      (∀ φ ∈ slices₂ f, IsAutForm φ ∧ TypeB (Kg S L.L₂) W₂ φ ∧ UpperTheory.V.Cj.S.HasCap φ (mOf χb)) ∧
      ∀ y, convF A.ν (A.gen S L T e₁ e₂ (.inr (.inr y))).ψ f = (s (.inr (.inr y)) / s (.inl ())) • f

def ReadOne : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b),
  ∃ (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ W₁ ∧ FiniteDimensional ℂ W₂ ∧
  ∀ (D : Dom E a b) (A : Ar l₁ l₂ D) (S : Set (Pl E)) (Z : Finset (Pl E)) (L : Lv a b Z), IsSection S → SplitIn S Z →
    ∀ T e₁ e₂ (s : Gam a b S Z → ℂ) (f : A.blk.I → H E a b → ℂ), TIn S T e₂ → Disjoint T Z → s (.inl ()) ≠ 0 →
    Eig (A.gen S L T e₁ e₂) s f →
    ∃ (χa : InfinitePlace E → Inf a) (χb : InfinitePlace E → Inf b) (φ₁ : Sm E a) (φ₂ : Sm E b) (B₁ B₂ : Pl E → Multiset ℂˣ),
      (∀ v r m, GlobalTheory.Dec.gelfVal (χa v r) m = s (.inr (.inl (v, r, m, false))) / s (.inl ())) ∧
      (∀ v r m, GlobalTheory.Dec.gelfVal (χb v r) m = s (.inr (.inl (v, r, m, true))) / s (.inl ())) ∧
      φ₁ ∈ slices₁ f ∧ φ₁ ≠ 0 ∧ IsAutForm φ₁ ∧ TypeB (Kg S L.L₁) W₁ φ₁ ∧ UpperTheory.V.Cj.S.HasCap φ₁ (mOf χa) ∧
      φ₂ ≠ 0 ∧ IsAutForm φ₂ ∧ TypeB (Kg S L.L₂) W₂ φ₂ ∧ UpperTheory.V.Cj.S.HasCap φ₂ (mOf χb) ∧
      (∀ w, Off Z w → (B₁ w).card = a ∧ (B₂ w).card = b ∧ IsSatVecGL w (UpperTheory.V.Cj.S.fL a w) φ₁ (B₁ w) ∧
        IsSatVecGL w (UpperTheory.V.Cj.S.fL b w) φ₂ (B₂ w)) ∧
      s (.inr (.inr (.inr ()))) / s (.inl ()) = val T e₁ e₂ B₁ B₂

def ValLim : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (T : Finset (Pl E)) (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (B₁ B₂ : ℕ → Pl E → Multiset ℂˣ)
  (C₁ C₂ : Pl E → Multiset ℂˣ),
  (∀ w, w ∈ T ∨ cPl w ∈ T → (C₁ w).card = a ∧ (C₂ w).card = b ∧ (∀ k, (B₁ k w).card = a ∧ (B₂ k w).card = b) ∧
    (∀ i : ℕ, Tendsto (fun k => satEig (qV E w) a (B₁ k w) i) atTop (𝓝 (satEig (qV E w) a (C₁ w) i))) ∧
    ∀ i : ℕ, Tendsto (fun k => satEig (qV E w) b (B₂ k w) i) atTop (𝓝 (satEig (qV E w) b (C₂ w) i))) →
  Tendsto (fun k => val T e₁ e₂ (B₁ k) (B₂ k)) atTop (𝓝 (val T e₁ e₂ C₁ C₂))

def SatCard : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : CD E n) (w : Pl E) (B : Multiset ℂˣ), D.Sat w B → B.card = n

def InfLimit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
  (D : Dom E a b) (A : Ar l₁ l₂ D) (S : Set (Pl E)) (Z : Finset (Pl E)) (L : Lv a b Z) T e₁ e₂
  (s : Gam a b S Z → ℂ) (sk : ℕ → Gam a b S Z → ℂ) (χa : ℕ → InfinitePlace E → Inf a) (χb : ℕ → InfinitePlace E → Inf b),
  (∀ γ, γ.arch → s γ = (A.gen S L T e₁ e₂ γ).val (chi l₁) (chi l₂)) → (∀ x, Tendsto (fun k => sk k x) atTop (𝓝 (s x))) →
  (∀ k v r m, GlobalTheory.Dec.gelfVal (χa k v r) m = sk k (.inr (.inl (v, r, m, false))) / sk k (.inl ())) →
  (∀ k v r m, GlobalTheory.Dec.gelfVal (χb k v r) m = sk k (.inr (.inl (v, r, m, true))) / sk k (.inl ())) →
  s (.inl ()) = 1 ∧
  (∀ τ (ε : ℝ), 0 < ε → ∀ᶠ k in atTop, Multiset.Rel (fun x y => ‖x - y‖ ≤ ε) (mOf (χa k) τ) (mOf (chi l₁) τ)) ∧
    ∀ τ (ε : ℝ), 0 < ε → ∀ᶠ k in atTop, Multiset.Rel (fun x y => ‖x - y‖ ≤ ε) (mOf (χb k) τ) (mOf (chi l₂) τ)

def TestsEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (l₁ : InfinitePlace E → DomWeight n) (l₂ : InfinitePlace E → DomWeight 0)
  (D : Dom E n 0) (A : Ar l₁ l₂ D) (π : CuspSub E n), ThetaFix π → ∀ (K : Subgroup (GL (Fin n) (Af E)))
  (W : Submodule ℂ (Kinf E n → ℂ)), IsOpen (K : Set (GL (Fin n) (Af E))) → K ≤ Kf E n → FiniteDimensional ℂ W →
  Keeps A.blk (piSp D π A.blk.I) ∧ Keeps A.blk (piSp D π A.blk.I)ᗮ ∧
    ∃ g : ℕ → A.blk.Hb, Tests A.blk (piSp D π A.blk.I)ᗮ g ∧ Sees A.blk g {π} K W

def RegS : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (S : Set (Pl E)) (u₁ : GL (Fin a) E) (u₂ : GL (Fin b) E), IsTransl u₁ → IsTransl u₂ →
  ∀ φ₁ φ₂ : ∀ w : Pl E, LF a b w, IsTestP φ₁ → IsTestP φ₂ →
  (∃ w ∈ S, IsSplitAt w ∧ ∀ y z, φ₁ w y ≠ 0 → φ₂ w z ≠ 0 → ((y * z).1.val.charpoly * (y * z).2.val.charpoly).Separable) →
  (∀ d x h₂, finFn S φ₁ φ₂ ((gFin (PositivityTheory.Rg.Tf.Loc.twConj (thetaA E a) x (ratGL E a d)), h₂) * (ratF E a u₁, ratF E b u₂)⁻¹) ≠ 0 →
    IsRegD d) ∧
  ∀ d x h₁, finFn S φ₁ φ₂ ((h₁, gFin (PositivityTheory.Rg.Tf.Loc.twConj (thetaA E b) x (ratGL E b d))) * (ratF E a u₁, ratF E b u₂)⁻¹) ≠ 0 →
    IsRegD d

def PowRep : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
  (D : Dom E a b) (A : Ar l₁ l₂ D) (S : Set (Pl E)) (Z : Finset (Pl E)) (L : Lv a b Z), IsSection S → SplitIn S Z →
  ∀ (u₁ : GL (Fin a) E) (u₂ : GL (Fin b) E) φ T (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) U (R : ℝ), L.Fix φ → 0 ≤ R →
    Rep A.blk (chi l₁) (chi l₂) (A.hk S L T e₁ e₂) 1 R U →
    (A.ptB (A.fx S L T φ (fun _ => .one) fun _ => .one)).Ok ∧ (A.ptB (rt u₁ u₂ (A.idm S L))).Ok ∧
    ∃ r₀ r₁ : ℝ, 0 ≤ r₀ ∧ 0 ≤ r₁ ∧ ∀ k : ℕ, Rep A.blk (chi l₁) (chi l₂)
      (rt u₁ u₂ (A.fx S L T φ (fun w => (e₁ w).pow k) fun w => (e₂ w).pow k)) 1 (r₀ + k * r₁)
      ((A.ptB (A.fx S L T φ (fun _ => .one) fun _ => .one)).op * U ^ k * (A.ptB (rt u₁ u₂ (A.idm S L))).op)

def CmbTest : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
  (D : Dom E a b) (A : Ar l₁ l₂ D) (S : Set (Pl E)) (Z : Finset (Pl E)) (L : Lv a b Z), IsSection S → SplitIn S Z →
  ∀ (u₁ : GL (Fin a) E) (u₂ : GL (Fin b) E), IsTransl u₁ → IsTransl u₂ → ∃ c : ℝ, 0 ≤ c ∧
  ∀ φ T (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (C : Cmb A.blk) (R : ℝ), L.Fix φ → (∃ w ∈ Z, RegAt2 a b w (φ w)) → 0 ≤ R →
    C.Ok (rt u₁ u₂ (A.fx S L T φ e₁ e₂)) R →
    (∀ j ∈ C.s, D4.IsTest2J (trM (C.t j).Φ A.tw) (c * (1 + R))) ∧ D4.IsTest2J (trM C.Φ A.tw) (c * (1 + R))

def SeenFam : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (S : Set (Pl E)) (Z : Finset (Pl E)) (L : Lv a b Z), SplitIn S Z →
  ∀ φ T (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))), L.Fix φ → TIn S T e₂ → (∀ w ∈ Z, seen φ L.ln w = φ w) ∧
    ∀ k, TEv S T (fun w => (e₂ w).pow k) ∧ seen (intersection_update_fsHerm_neg_one Z T φ fun w => (e₁ w).pow k) (intersection_update_fsHerm_neg_one Z T L.ln fun w => (e₂ w).pow k) = fam Z T φ e₁ e₂ k ∧
      IsTestP (fam Z T φ e₁ e₂ k) ∧ val T (fun w => (e₁ w).pow k) (fun w => (e₂ w).pow k) = fun B₁ B₂ => val T e₁ e₂ B₁ B₂ ^ k

def CmbEll : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a)
  (l₂ : InfinitePlace E → DomWeight b) (D : Dom E a b) (A : Ar l₁ l₂ D) (μ₁ : Measure (GA E a)) (μ₂ : Measure (GA E b)),
  μ₁.IsHaarMeasure → μ₂.IsHaarMeasure → ∃ κ : ℂ, κ ≠ 0 ∧
  ∀ (S : Set (Pl E)) (Z : Finset (Pl E)) (L : Lv a b Z), IsSection S → SplitIn S Z →
  ∀ (u₁ : GL (Fin a) E) (u₂ : GL (Fin b) E), IsTransl u₁ → IsTransl u₂ →
  ∀ φ T (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (k : ℕ) (C : Cmb A.blk) (R : ℝ), L.Fix φ → (∃ w ∈ Z, RegAt2 a b w (φ w)) → TIn S T e₂ → 0 ≤ R →
    C.Ok (rt u₁ u₂ (A.fx S L T φ (fun w => (e₁ w).pow k) fun w => (e₂ w).pow k)) R →
    ellSum2 μ₁ μ₂ (trM C.Φ A.tw) = κ * C.val (chi l₁) (chi l₂) * geomSt2 S l₁ l₂ (fam Z T φ e₁ e₂ k)

def CmbPi : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → ∃ l₁ : InfinitePlace E → DomWeight n,
    (∀ v, π.HasInfChar v.embedding (infOfWeight (l₁ v))) ∧
    ∀ (l₂ : InfinitePlace E → DomWeight 0) (D : Dom E n 0) (A : Ar l₁ l₂ D) (S : Set (Pl E)), IsSection S →
    ∀ Z : Finset (Pl E), SplitIn S Z → ∀ (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)),
    (∀ w, Off Z w → (CG.mk π).HasSat w (B w)) → (∀ w ∈ Z, π.IsLocComp w (τ w)) →
    ∀ (u₁ : GL (Fin n) E) (u₂ : GL (Fin 0) E), IsTransl u₁ → ∃ c : ℂ, c ≠ 0 ∧
    ∀ (L : Lv n 0 Z) φ T (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) (C : Cmb A.blk) (R : ℝ), L.Fix φ → TEv S T e₂ →
      Disjoint T Z → C.Ok (rt u₁ u₂ (A.fx S L T φ e₁ e₂)) R → IsTwTr D.μ π (trM C.Φ A.tw)
        (c * C.val (chi l₁) (chi l₂) * (∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => φ w (g, 1)) * val T e₁ e₂ B 0)

def ValNil : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Z T : Finset (Pl E)) (S : Set (Pl E)) (D : CD E 0) (B₁ B₂ : Pl E → Multiset ℂˣ)
  (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))), IsSection S → SplitIn S Z → (∀ w ∈ T, w ∈ S) → Disjoint T Z →
  (∀ w, Off Z w → D.Sat w (B₂ w)) → val T e₁ e₂ B₁ B₂ = val T e₁ e₂ B₁ 0

end UpperTheory.Zero.ConvolutionTheory.EB
