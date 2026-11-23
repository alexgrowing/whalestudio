import Formalism.SharpRestriction.GrowthBounds.ProjectionLemmaBaseLevel

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

structure RS (p n' : ℕ) where
  W : Type
  Qq : Type
  O : Type
  Kf : Type
  [ringW : CommRing W]
  [domW : IsDomain W]
  [dvrW : IsDiscreteValuationRing W]
  [fieldQ : Field Qq]
  [algW : Algebra W Qq]
  [ring : CommRing O]
  [dom : IsDomain O]
  [dvr : IsDiscreteValuationRing O]
  [fieldK : Field Kf]
  [algO : Algebra O Kf]
  ι : Qq →+* Kf
  σ : Qq ≃+* Qq
  jO : W →+* O
  w : O
  std : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ jO w

attribute [instance] RS.ringW RS.domW RS.dvrW RS.fieldQ RS.algW RS.ring RS.dom RS.dvr RS.fieldK RS.algO

section Clean

variable {p n' : ℕ} (R : RS p n') {m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ)

def CCL (t c : ℕ) (e : Edge R.W R.Qq (m + 1)) : Submodule R.O (Vsp R.Kf lam0) :=
  scale (algebraMap R.O R.Kf R.w ^ (-(t : ℤ))) (HL R.ι R.σ lam0 e.src) ⊓ Re p R.ι R.σ R.w 1 lam0 e ⊓
    ⨅ (e' : Edge R.W R.Qq (m + 1)) (_ : IsEdge p n' 1 e' ∧ e'.src = e.src ∧ e' ≠ e),
      scale (algebraMap R.O R.Kf R.w ^ (c : ℤ)) (Re p R.ι R.σ R.w 1 lam0 e')

def CCL' (t c : ℕ) (e : Edge R.W R.Qq (m + 1)) : Submodule R.O (Module.Dual R.Kf (Vsp R.Kf lam0)) :=
  scale (algebraMap R.O R.Kf R.w ^ (-(t : ℤ))) (Formalism.GradedWeylDivisibility.dualLat R.O R.Kf (HL R.ι R.σ lam0 e.tgt)) ⊓
    Re' p R.ι R.σ R.w 1 lam0 e ⊓
    ⨅ (e' : Edge R.W R.Qq (m + 1)) (_ : IsEdge p n' 1 e' ∧ e'.tgt = e.tgt ∧ e' ≠ e),
      scale (algebraMap R.O R.Kf R.w ^ (c : ℤ)) (Re' p R.ι R.σ R.w 1 lam0 e')

def FacL (t c : ℕ) (e : Edge R.W R.Qq (m + 1)) (n : ℕ) (D : ℝ) : Prop :=
  FactorsLE p (be (Kf := R.Kf) p 1 lam0) (CCL R lam0 t c e) (CCL' R lam0 t c e) n D

def RhoL (t c : ℕ) (D X : ℝ) : Prop :=
  ∀ e : Edge R.W R.Qq (m + 1), IsEdge p n' 1 e →
    RhoGE p (be (Kf := R.Kf) p 1 lam0) (CCL R lam0 t c e) (CCL' R lam0 t c e) D X

def dL : ℝ := (dimV R.Kf lam0 : ℝ) / gaussianNumber (p ^ n') (m + 1)

end Clean

def ex {n' : ℕ} {TT : Finset (Fin n')} (f : TT → ℕ) : Fin n' → ℕ := fun s => if h : s ∈ TT then f ⟨s, h⟩ else 0

def flatW {n' : ℕ} (m : ℕ) {TT : Finset (Fin n')} (al be : TT → ℕ) : Fin n' → Fin (m + 1) → ℤ :=
  fun s i => if h : s ∈ TT then
    (if i = 0 then (al ⟨s, h⟩ : ℤ) else if i = Fin.last m then -(be ⟨s, h⟩ : ℤ) else 0) else 0

def topW {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) : Fin n' → Fin (m + 1) → ℤ :=
  fun s => if s ∈ TT then lam0 s else 0

structure Cst where
  C₀ : ℝ
  CH : ℝ
  CA : ℝ
  CE1 : ℝ
  CE2 : ℝ
  Cm : ℝ
  Ckap : ℝ
  Ct : ℝ
  Cs : ℝ

def Cst.Pos (K : Cst) : Prop :=
  0 < K.C₀ ∧ 0 < K.CH ∧ 0 < K.CA ∧ 0 < K.CE1 ∧ 0 < K.CE2 ∧ 0 < K.Cm ∧ 0 < K.Ckap ∧ 0 < K.Ct ∧ 0 < K.Cs

def Cst.admitted (D : Formalism.BasicNotions.D7) (K : Cst) : Prop := AdmB D K.C₀ K.CH K.CA K.CE1 K.CE2 K.Cm K.Ckap K.Ct 4 K.Cs

structure Dat where
  p : ℕ
  n' : ℕ
  m : ℕ
  hm : m ≠ 0
  TT : Finset (Fin n')
  G' : ℕ
  N₁ : ℕ
  Y : ℝ
  Yb : ℝ
  ar : ℝ
  b' : ℝ
  bl : ℝ
  bu : ℝ
  ccl : ℕ
  Dp : ℕ
  cStar : ℕ

instance (X : Dat) : NeZero X.m := ⟨X.hm⟩

namespace Dat

variable (X : Dat)

def a : ℕ := ⌈X.ar⌉₊

def N : ℕ := X.TT.card

def k : ℝ := (X.m : ℝ) + 1

def Hyp (C₀ CH : ℝ) : Prop :=
  HypI C₀ CH X.p X.n' X.m X.TT X.G' X.N₁ X.Y X.Yb X.ar X.b' X.bl X.bu X.ccl X.Dp X.cStar

def c4 : ℕ := X.cStar + 2 * X.N * X.ccl + 2 * X.n' * X.ccl

def u0c : ℕ := ⌈((X.m : ℝ) + 2) * lgA X.p X.a X.m⌉₊

def kap1c : ℕ := ⌈kappaOneExponent X.p X.a X.m⌉₊

variable (K : Cst)

def D0 : ℝ := totalDegreeBudget K.CA X.p X.m X.TT X.N₁ X.Y X.a

def D1 : ℝ := X.D0 K + 4 * X.N * X.u0c

def J0 : ℝ := cleaningBudget K.C₀ X.m X.N₁ X.a X.b'

def Jn : ℕ := ⌊X.J0 K⌋₊

def t0 (A B : X.TT → ℕ) : ℝ := t0I K.C₀ K.Ct X.p X.m X.TT X.G' X.N₁ X.a X.b' X.c4 (ex A) (ex B)

def tStar (al be : X.TT → ℕ) : ℕ := ⌈X.t0 K al be + X.N * X.J0 K⌉₊

variable (R : RS X.p X.n')

def kF (al be : X.TT → ℕ) : ℝ :=
  sInf {κ : ℝ | 0 ≤ κ ∧ RhoL R (flatW X.m al be) (X.tStar K al be) X.c4 (X.D1 K)
    ((1 - κ) * dL R (flatW X.m al be))}

def kx (A B : X.TT → ℕ) : ℝ :=
  kapPI K.C₀ K.CE1 K.CE2 K.Cm K.Ckap X.p X.m X.TT X.G' X.N₁ X.Y X.a X.b' X.c4 +
    ∑ jj, kapTI R.O K.C₀ K.CA K.CE1 K.CE2 K.Cm X.p X.n' X.m X.TT X.G' X.N₁ X.Y X.a X.b' X.c4 (ex A) (ex B) jj

def Inside (aa bb : X.TT → ℤ) : Prop := ∀ s, (X.a : ℤ) ≤ aa s - X.ccl ∧ X.bl ≤ ((bb s - X.ccl : ℤ) : ℝ)

open Classical in

def kText (aa bb : X.TT → ℤ) : ℝ :=
  (if X.Inside aa bb then X.kF K R (fun s => (aa s - X.ccl).toNat) (fun s => (bb s - X.ccl).toNat) else 1) +
    2 * X.kF K R (fun s => (aa s + X.ccl).toNat) (fun s => (bb s + X.ccl).toNat) +
    12 * X.N * X.k * X.ccl / X.b'

end Dat

def LPRingIndep : Prop :=
  ∀ (p n' : ℕ) (R₁ R₂ : RS p n') (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (t D : ℕ) (κ : ℝ) (cStar : ℕ),
    LPprime (W := R₁.W) p n' R₁.ι R₁.σ R₁.w r lam0 t D κ cStar →
      LPprime (W := R₂.W) p n' R₂.ι R₂.σ R₂.w r lam0 t D κ cStar

def RestEdge : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ), IsDominant lam0 →
    ∀ (t c n : ℕ) (D : ℝ) (e e' : Edge R.W R.Qq (m + 1)), IsEdge p n' 1 e → IsEdge p n' 1 e' →
      FacL R lam0 t c e n D → FacL R lam0 t c e' n D

def RhoUpperBoundSmallDepth : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ), IsDominant lam0 →
    ∀ (t c n : ℕ) (D : ℝ), 0 ≤ D → 2 * D < c → (∀ e, IsEdge p n' 1 e → FacL R lam0 t c e n D) →
      (n : ℝ) ≤ dL R lam0

def RhoLowerBoundLargeConductor : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ), IsDominant lam0 →
    ∀ (t c D : ℕ) (κ : ℝ), 8 * D < c → 4 * (D + 1) ≤ c → RhoL R lam0 t c D ((1 - κ) * dL R lam0) →
      LPprime (W := R.W) p n' R.ι R.σ R.w 1 lam0 t D κ c

def RhoSumLowerBoundEdge : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ), 2 ≤ m → ∀ (TT : Finset (Fin n')) (a : ℕ) (A B : TT → ℕ),
    (∀ s, A s + B s + 1 ≤ 8 * a) →
    ∀ (t c : ℕ) (D X : ℝ) (e : Edge R.W R.Qq (m + 1)), IsEdge p n' 1 e → 0 ≤ D →
      RhoGE p (beHH (Kf := R.Kf) (m := m) p TT (ex A) (ex B)) (CCe p R.ι R.σ R.w TT (ex A) (ex B) t c e)
        (CCe' p R.ι R.σ R.w TT (ex A) (ex B) t c e) D X →
      ∃ n : (TT → ℕ) → ℕ,
        (∀ j : TT → ℕ, (∀ s, j s ≤ min (A s) (B s)) →
          FacL R (flatW m (fun s => A s - j s) (fun s => B s - j s)) t c e (n j)
            (D + 4 * TT.card * (⌈((m : ℝ) + 2) * lgA p a m⌉₊ : ℕ))) ∧
        X ≤ ∑ j ∈ Fintype.piFinset (fun s : TT => Finset.range (min (A s) (B s) + 1)), (n j : ℝ)

def CloudWeightLowerBound : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ), 2 ≤ m → ∀ (TT : Finset (Fin n')) (a ccl : ℕ) (b' : ℝ) (aw bw : Fin n' → ℤ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (A B : TT → ℕ),
    IsBaseWeight TT aw bw ccl lam0 → IsDominant lam0 → (∀ s, s ∉ TT → lam0 s = 0) →
    (∀ s : TT, (A s : ℤ) = aw s - ccl ∧ (B s : ℤ) = bw s - ccl) →
    0 < b' → (∀ s, b' / 3 ≤ A s ∧ b' / 3 ≤ B s) → 2 * ccl ≤ 8 * a →
    12 * (TT.card : ℝ) * ((m : ℝ) + 1) * ccl / b' ≤ 1 / 9 →
    ∀ (t c₂ : ℕ) (D₁ κ₁ κ₂ : ℝ), 0 ≤ D₁ → 4 * D₁ < c₂ → 2 * TT.card * ccl ≤ c₂ → 0 ≤ κ₁ → κ₁ ≤ 1 → 0 ≤ κ₂ →
      RhoL R (flatW m A B) t c₂ D₁ ((1 - κ₁) * dL R (flatW m A B)) →
      RhoL R (flatW m (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) t c₂ D₁
        ((1 - κ₂) * dL R (flatW m (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl))) →
      RhoL R lam0 t (c₂ - 2 * TT.card * ccl) (2 * D₁ + TT.card * (⌈kappaOneExponent p a m⌉₊ : ℕ))
        ((1 - (κ₁ + 2 * κ₂ + 12 * (TT.card : ℝ) * ((m : ℝ) + 1) * ccl / b')) * dL R lam0)

def ResidueClassCount : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ) (TT : Finset (Fin n')) (ccl : ℕ) (aw bw : Fin n' → ℤ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ), IsBaseWeight TT aw bw ccl lam0 → IsDominant lam0 →
    ∀ (t c₃ : ℕ) (D κ : ℝ), 2 * n' * ccl ≤ c₃ →
      RhoL R (topW TT lam0) t c₃ D ((1 - κ) * dL R (topW TT lam0)) →
      RhoL R lam0 (t + 2 * n' * ccl) (c₃ - 2 * n' * ccl) D ((1 - κ) * dL R lam0)

def TransportedAlt (K : Cst) (F : ℝ → Dat → Prop) : Prop :=
  ∃ T Cn : ℝ, 0 < T ∧ 0 < Cn ∧ ∀ CH : ℝ, T ≤ CH → ∀ C : ℝ, Cn ≤ C → ∀ X : Dat, X.Hyp K.C₀ CH → F C X

structure FactsLP (K : Cst) (C : ℝ) (X : Dat) : Prop where
  cst : 8 * (X.Dp + 1) ≤ X.cStar
  bpos : 0 < X.b'
  ppos : 0 < X.p
  m2 : 2 ≤ X.m
  D1nn : 0 ≤ X.D1 K
  four_depth_lt_conductor : 4 * X.D1 K < X.c4
  dle : 2 * X.D1 K + X.N * X.kap1c ≤ X.Dp
  a8 : 2 * X.ccl ≤ 8 * X.a
  eps : 12 * (X.N : ℝ) * X.k * X.ccl / X.b' ≤ 1 / 9
  lowa : X.b' / 3 ≤ X.a
  lowb : X.b' / 3 ≤ X.bl
  tle : ∀ aw bw : Fin X.n' → ℤ, (∀ s ∈ X.TT, aw s ∈ IaZ X.m X.Y X.ar ∧ bw s ∈ IbZ X.bl X.bu) →
    (X.tStar K (fun s => (aw s + X.ccl).toNat) (fun s => (bw s + X.ccl).toNat) : ℝ) + 2 * X.n' * X.ccl ≤
      tI K.C₀ C X.p X.n' X.m X.TT X.G' X.N₁ X.ar X.b' X.ccl X.cStar aw bw

def MidLP (K : Cst) (C : ℝ) : Prop :=
  ∀ X : Dat, FactsLP K C X → ∀ (R : RS X.p X.n') (aw bw : Fin X.n' → ℤ) (lam0 : Fin X.n' → Fin (X.m + 1) → ℤ),
    WeightI X.TT X.Y X.ar X.bl X.bu X.ccl aw bw lam0 →
    ∀ t : ℕ, tI K.C₀ C X.p X.n' X.m X.TT X.G' X.N₁ X.ar X.b' X.ccl X.cStar aw bw ≤ t →
      LPprime (W := R.W) X.p X.n' R.ι R.σ R.w 1 lam0 t X.Dp (X.kText K R (fun s => aw s) (fun s => bw s)) X.cStar

def Cst.Cmean (K : Cst) : ℝ := 6 * (K.CA + K.Cs) + 8

end Formalism.MainNotions.flipOneThree.Pf

end
