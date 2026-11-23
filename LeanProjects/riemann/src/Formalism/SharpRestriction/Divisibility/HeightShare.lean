import Mathlib
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace Formalism.MainNotions.HeightShare

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.BasicNotions

section Lat

variable {F : Type} [Field F] [NumberField F] [StarRing F]

def coordC (A : HLat F) (v : InfinitePlace F) (x : A.V) : A.ι → ℂ :=
  fun i => v.embedding (A.b.repr x i)

def nsq (A : HLat F) (v : InfinitePlace F) (c : A.ι → ℂ) : ℝ :=
  ∑ k, ‖(Matrix.mulVec (A.X v)⁻¹ c) k‖ ^ 2

def nrm (A : HLat F) (v : InfinitePlace F) (x : A.V) : ℝ := Formalism.HermitianLatticesTheory.normAt A.b A.X v x

theorem nrm_eq (A : HLat F) (v : InfinitePlace F) (x : A.V) :
    nrm A v x = Real.sqrt (nsq A v (coordC A v x)) := rfl

def degL (A : HLat F) : ℝ := - A.lcv / 2

def SmallSpan (A : HLat F) (Λ : ℝ) : Prop :=
  ∃ (k : ℕ) (u : Fin k → A.V), (∀ i, u i ∈ A.L) ∧ Submodule.span F (Set.range u) = ⊤ ∧
    ∀ i v, nrm A v (u i) ≤ Λ

end Lat

section Data

variable {F : Type} [Field F] [NumberField F] [StarRing F]

structure LData (G : Formalism.BasicNotions.DV.Geo F) where
  Y : G.Var
  bd : G.Cl Y
  L : G.Dv Y
  W : HLat F
  ιW : W.V →ₗ[F] G.Fn Y
  n : ℕ
  w : Fin n → W.V
  abelian₂ : ℝ

namespace LData

variable {G : Formalism.BasicNotions.DV.Geo F} (B : LData G)

def Dm : ℕ := G.dim B.Y

def Lbar : G.Adl B.Y := G.ofW B.Y B.L B.W B.ιW

def del : ℝ := (G.inter B.Y (fun _ => B.L) : ℝ)

def h : ℝ := G.arTop B.Y B.Lbar / (((B.Dm : ℝ) + 1) * B.del)

def wY : Fin B.n → G.Fn B.Y := fun i => B.ιW (B.w i)

def phi (v : InfinitePlace F) : G.Met B.Y v.embedding B.L :=
  G.fsMet B.Y v.embedding B.L
    (fun k : B.W.ι => ∑ i, (B.W.X v) i k • G.cx B.Y v.embedding (B.ιW (B.W.b i)))

def Hyp : Prop :=
  1 ≤ B.Dm ∧ Function.Injective B.ιW ∧ (∀ x, B.ιW x ∈ G.H0 B.Y B.L) ∧ B.W.Good ∧
  G.bpf B.Y B.L (B.ιW '' (B.W.L : Set B.W.V)) ∧ G.properCl B.Y B.bd ∧
  Submodule.span (𝓞 F) (Set.range B.w) = B.W.L ∧
  (∀ i v, nrm B.W v (B.w i) ≤ B.abelian₂) ∧ 1 ≤ B.abelian₂

end LData

structure HSData (G : Formalism.BasicNotions.DV.Geo F) extends LData G where
  L2 : G.Dv Y
  A : G.Dv Y
  W2 : HLat F
  ι2 : W2.V →ₗ[F] G.Fn Y
  T : ℕ
  M : ℕ → HLat F
  ιM : ∀ j, (M j).V →ₗ[F] G.Fn Y
  j0 : ℕ
  beta : ℝ
  LamD : ℝ
  LamT : ℝ
  J : ℝ

namespace HSData

variable {G : Formalism.BasicNotions.DV.Geo F} (S : HSData G)

def Vsp (j : ℕ) : Submodule F (G.Fn S.Y) := LinearMap.range (S.ιM j)

def K : G.Dv S.Y := G.KY S.Y

def L2bar : G.Adl S.Y := G.ofW S.Y S.L2 S.W2 S.ι2

def phi2 (v : InfinitePlace F) : G.Met S.Y v.embedding S.L2 :=
  G.fsMet S.Y v.embedding S.L2
    (fun k : S.W2.ι => ∑ i, (S.W2.X v) i k • G.cx S.Y v.embedding (S.ι2 (S.W2.b i)))

def Setup : Prop :=
  S.toLData.Hyp ∧ Function.Injective S.ι2 ∧ (∀ x, S.ι2 x ∈ G.H0 S.Y S.L2) ∧ S.W2.Good ∧
  G.bpf S.Y S.L2 (S.ι2 '' (S.W2.L : Set S.W2.V)) ∧ 2 * S.Dm ≤ S.T ∧
  (∀ j ≤ S.T, (S.M j).Good ∧ Function.Injective (S.ιM j) ∧
    G.H0 S.Y (S.K + S.A + j • S.L) ≤ S.Vsp j ∧
    ∃ Δ, G.Eff S.Y Δ ∧ G.subCl S.Y (G.supp S.Y Δ) S.bd ∧
      S.Vsp j ≤ G.H0 S.Y (S.K + S.A + j • S.L + Δ)) ∧
  S.Vsp 0 = G.H0 S.Y (S.K + S.A)

def NonvanishingSectionCondition : Prop :=
  1 ≤ S.j0 ∧ G.phiBir S.Y S.L (S.ιW '' (S.W.L : Set S.W.V)) ∧
  G.phiNoContr S.Y S.L (S.ιW '' (S.W.L : Set S.W.V)) S.bd ∧
  (∃ f ∈ G.H0 S.Y (S.j0 • S.L), f ≠ 0 ∧ G.vanishOn S.Y (S.j0 • S.L) f S.bd) ∧
  G.big S.Y S.L2 ∧ G.nef S.Y S.A ∧ G.big S.Y S.A ∧
  G.Eff S.Y (S.A - S.L2 - S.Dm • S.L) ∧
  G.subCl S.Y (G.supp S.Y (S.A - S.L2 - S.Dm • S.L)) S.bd

def H1 : Prop :=
  ∀ j < S.T, ∀ x ∈ S.W.L, ∀ f ∈ (S.M j).L, ∃ g ∈ (S.M (j + 1)).L,
    S.ιM (j + 1) g = S.ιW x * S.ιM j f ∧
    ∀ v, nrm (S.M (j + 1)) v g ≤ Real.sqrt S.beta * nrm S.W v x * nrm (S.M j) v f

def H2 : Prop :=
  ∀ j ≤ S.T, ∀ v : InfinitePlace F, ∀ c : (S.M j).ι → ℂ,
    (∑ i, c i • G.cx S.Y v.embedding (S.ιM j ((S.M j).b i))) ∈
      Submodule.span ℂ (G.cx S.Y v.embedding '' (G.H0 S.Y (S.K + (S.L2 + (S.Dm + j) • S.L)) :
        Set (G.Fn S.Y))) →
    nsq (S.M j) v c ≤ S.beta ^ (S.Dm + j + 1) *
      ∫ y, G.pnK S.Y v.embedding (S.L2 + (S.Dm + j) • S.L)
        (G.mAdd S.Y v.embedding S.L2 ((S.Dm + j) • S.L) (S.phi2 v)
          (G.mPow S.Y v.embedding S.L (S.Dm + j) (S.phi v)))
        (∑ i, c i • G.cx S.Y v.embedding (S.ιM j ((S.M j).b i))) y ∂(G.vol S.Y v.embedding)

def H3 : Prop :=
  AddSubgroup.closure (Set.range S.w) = S.W.L.toAddSubgroup ∧
  SmallSpan (S.M S.Dm) S.LamD ∧ SmallSpan (S.M S.T) S.LamT ∧
  1 ≤ S.beta ∧ 1 ≤ S.LamD ∧ 1 ≤ S.LamT

def H4 : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] (c : Fin (G.dim S.Y) → Fin S.n → 𝓞 E),
    G.cutGood S.Y S.bd E S.wY c →
      G.resFull S.Y E S.wY c (S.M 0) (S.ιM 0) S.L2bar ∧
      - S.del * S.J - ((S.Dm : ℝ) + 3) * G.cutHt S.Y S.Lbar E S.wY c ≤
        G.resDeg S.Y E S.wY c (S.M 0) (S.ιM 0) S.L2bar

def Hyp : Prop := S.Setup ∧ S.NonvanishingSectionCondition ∧ S.H1 ∧ S.H2 ∧ S.H3 ∧ S.H4

def d : ℕ := (S.M S.T).rank

def z : ℝ := 1 - (Nat.choose (S.T - 1) S.Dm : ℝ) * S.del / (S.d : ℝ)

def logRho (C : ℝ) : ℝ :=
  Real.log S.abelian₂ +
    C * Real.log ((S.n : ℝ) * S.Dm * S.j0 * S.del * (2 + |S.h| + Real.log S.abelian₂))

def rho (C : ℝ) : ℝ := Real.exp (S.logRho C)

def g : ℝ := ((S.Dm : ℝ) + 1) * (Real.log S.n + 1) / 2 + 1

def Claim (C : ℝ) : Prop :=
  (1 - S.z) * ((S.T : ℝ) * S.h - 3 * ((S.Dm : ℝ) + 1) * |S.h| - S.J
      - C * (S.Dm : ℝ) ^ 2 * Real.log (S.rho C * S.T)
      - ((S.T : ℝ) + S.Dm + 1) * Real.log S.beta - ((S.T : ℝ) + (S.Dm : ℝ) ^ 2) * (S.g + 2))
    - S.z * ((S.T : ℝ) * Real.log (2 * S.rho C * Real.sqrt S.beta) + Real.log S.LamD
      + Real.log S.LamT)
  ≤ degL (S.M S.T) / (S.d : ℝ)

end HSData

def inter1 {F : Type} [Field F] [NumberField F] [StarRing F] (G : Formalism.BasicNotions.DV.Geo F) (Y : G.Var)
    (B L : G.Dv Y) : ℝ :=
  (G.inter Y (fun i => if i.val = 0 then B else L) : ℝ)

def cTot {F : Type} [Field F] [NumberField F] (cFin : ℕ → ℝ) (cInf : InfinitePlace F → ℝ) : ℝ :=
  (∑ᶠ (p : ℕ) (_ : p.Prime), cFin p) + (∑ v, cInf v) / (Fintype.card (InfinitePlace F) : ℝ)

structure VData {G : Formalism.BasicNotions.DV.Geo F} (B : LData G) where
  TT : Set ℕ
  Mp : ℕ → HLat F
  io : ∀ τ, (Mp τ).V →ₗ[F] G.Fn B.Y
  delP : ℝ
  sl : ℝ
  cFin : ℕ → ℝ
  cInf : InfinitePlace F → ℝ

namespace VData

variable {G : Formalism.BasicNotions.DV.Geo F} {B : LData G} (V : VData B)

def c : ℝ := cTot V.cFin V.cInf

def Hyp : Prop :=
  V.TT.Infinite ∧ (∀ τ ∈ V.TT, 1 ≤ τ) ∧
  (∀ τ ∈ V.TT, (V.Mp τ).Good ∧ Function.Injective (V.io τ) ∧
    ∀ x, V.io τ x ∈ G.H0 B.Y (τ • B.L)) ∧
  Tendsto (fun τ : ℕ => ((V.Mp τ).rank : ℝ) / ((τ : ℝ) ^ B.Dm / (B.Dm.factorial : ℝ)))
    (atTop ⊓ 𝓟 V.TT) (𝓝 V.delP) ∧
  (∀ ε > 0, ∀ᶠ τ : ℕ in atTop ⊓ 𝓟 V.TT,
    V.sl - ε ≤ degL (V.Mp τ) / ((τ : ℝ) * (V.Mp τ).rank)) ∧
  (∀ τ ∈ V.TT, ∀ (v : HeightOneSpectrum (𝓞 F)) (x : (V.Mp τ).V), x ∈ (V.Mp τ).L →
    G.supFin B.Y B.Lbar v τ (V.io τ x) ≤
      Real.exp ((τ : ℝ) * V.cFin (ringChar (𝓞 F ⧸ v.asIdeal)))) ∧
  (∃ o : ℕ → ℝ, Tendsto (fun τ : ℕ => o τ / (τ : ℝ)) (atTop ⊓ 𝓟 V.TT) (𝓝 0) ∧
    ∀ τ ∈ V.TT, ∀ (v : InfinitePlace F) (x : (V.Mp τ).V), x ∈ (V.Mp τ).L →
      G.supInf B.Y B.Lbar v τ (V.io τ x) ≤
        Real.exp ((τ : ℝ) * V.cInf v + o τ) * nrm (V.Mp τ) v x) ∧
  {p : ℕ | V.cFin p ≠ 0}.Finite

end VData

end Data

section Gen

variable {F : Type} [Field F] [NumberField F] [StarRing F] (G : Formalism.BasicNotions.DV.Geo F)

def BaseChangeDefiniteGood [IsTotallyComplex F] (C : ℝ) : Prop :=
  ∀ (S : HSData G), S.Hyp → S.Claim C

def BinomialShareLowerBound [IsTotallyComplex F] : Prop :=
  ∀ (S : HSData G), S.Hyp → (Nat.choose (S.T - 1) S.Dm : ℝ) * S.del ≤ (S.d : ℝ)

def ShareInequality [IsTotallyComplex F] : Prop :=
  ∀ (S : HSData G), S.Hyp →
    ∀ (E : Type) [Field E] [NumberField E] [Algebra F E]
      (c : Fin (G.dim S.Y) → Fin S.n → 𝓞 E),
      G.cutGood S.Y S.bd E S.wY c →
      ∀ Bt Lt : G.Dv S.Y, G.nef S.Y Bt → S.Vsp S.T ≤ G.H0 S.Y Bt →
        G.nef S.Y Lt → G.Eff S.Y (Lt - S.L) →
        (∀ f ∈ S.Vsp S.T, f ≠ 0 →
            (G.cutOrd S.Y E S.wY c Bt f : ℝ) ≤ inter1 G S.Y Bt S.L / S.del) ∧
        (S.d : ℝ) ≤ (Nat.choose (⌊inter1 G S.Y Bt S.L / S.del⌋₊ + S.Dm) S.Dm : ℝ) * S.del ∧
        inter1 G S.Y Bt S.L ≤ inter1 G S.Y Bt Lt

def LemmaVCorollary [IsTotallyComplex F] : Prop :=
  ∀ (B : LData G), B.Hyp → 0 < B.del → ∀ (V : VData B), V.Hyp → V.sl ≤ 0 → 0 ≤ V.c →
    ∀ cs : ℝ, Real.log B.abelian₂ ≤ cs → V.sl - V.c - cs * (1 - V.delP / B.del) ≤ B.h

def LemmaVStrong [IsTotallyComplex F] : Prop :=
  ∀ (B : LData G), B.Hyp → 0 < B.del → ∀ (V : VData B), V.Hyp →
    ∀ t : ℝ, Real.log B.abelian₂ ≤ t → V.delP / B.del * max (V.sl - V.c + t) 0 ≤ B.h + t

def LemmaVVolumeGeneral [IsTotallyComplex F] : Prop :=
  ∀ (B : LData G), B.Hyp → 0 < B.del →
    ∀ (TT : Set ℕ) (Sig : ℕ → Set (G.Fn B.Y)) (cFin : ℕ → ℝ) (cInf : InfinitePlace F → ℝ)
      (t0 : ℝ) (o : ℕ → ℝ),
      TT.Infinite → (∀ τ ∈ TT, 1 ≤ τ) →
      (∀ τ ∈ TT, (Sig τ).Finite ∧ Sig τ ⊆ (G.H0 B.Y (τ • B.L) : Set (G.Fn B.Y))) →
      {p : ℕ | cFin p ≠ 0}.Finite →
      Tendsto (fun τ : ℕ => o τ / (τ : ℝ)) (atTop ⊓ 𝓟 TT) (𝓝 0) →
      (∀ τ ∈ TT, ∀ f ∈ Sig τ, ∀ v : HeightOneSpectrum (𝓞 F),
        G.supFin B.Y B.Lbar v τ f ≤ Real.exp ((τ : ℝ) * cFin (ringChar (𝓞 F ⧸ v.asIdeal)))) →
      (∀ τ ∈ TT, ∀ f ∈ Sig τ, ∀ v : InfinitePlace F,
        G.supInf B.Y B.Lbar v τ f ≤ Real.exp ((τ : ℝ) * (cInf v + t0) + o τ)) →
      Real.log B.abelian₂ ≤ cTot cFin cInf + t0 →
      ∀ ε > 0, ∀ᶠ τ : ℕ in atTop ⊓ 𝓟 TT,
        (B.Dm.factorial : ℝ) * Real.log ((Sig τ).ncard : ℝ) /
            ((Module.finrank ℚ F : ℝ) * (τ : ℝ) ^ (B.Dm + 1)) ≤
          B.del * (B.h + cTot cFin cInf + t0) + ε

def sectionLogWeight (Y : G.Var) (σ : F →+* ℂ) (Δs : G.Dv Y) (φs : G.Met Y σ Δs)
    (s : Fin (G.dim Y) → G.FnC Y σ) (y : G.pts Y σ) : ℝ :=
  (G.dim Y : ℝ) * Real.log (∑ i, G.pn Y σ Δs φs (s i) y)

def OhsawaTakegoshiExtension : Prop :=
  ∀ (Y : G.Var) (σ : F →+* ℂ)
    (ΔE : G.Dv Y) (φE : G.Met Y σ ΔE) (Δs : G.Dv Y)
    (φs : G.Met Y σ Δs) (s : Fin (G.dim Y) → G.FnC Y σ)
    (S : Set (G.pts Y σ)) (δ : ℝ),
    0 < δ → 1 ≤ G.dim Y → S.Finite →
    G.mSmooth Y σ ΔE φE → G.mSmooth Y σ Δs φs →
    (∀ i, s i ∈ Submodule.span ℂ (G.cx Y σ '' (G.H0 Y Δs : Set (G.Fn Y)))) →
    G.redZero Y σ Δs s S →
    (∀ y, sectionLogWeight G Y σ Δs φs s y ≤ 0) →
    (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), G.mPsh Y σ ΔE φE (fun y => α * sectionLogWeight G Y σ Δs φs s y)) →
    ∀ gS : G.FnC Y σ, G.regOn Y σ ΔE gS S →
      ∃ Fs ∈ Submodule.span ℂ (G.cx Y σ '' (G.H0 Y (G.KY Y + ΔE) : Set (G.Fn Y))),
        G.agreeOn Y σ ΔE Fs gS S ∧
        Integrable (fun y => G.pnK Y σ ΔE φE Fs y * Real.exp (-(sectionLogWeight G Y σ Δs φs s y)) /
            (1 + (δ * sectionLogWeight G Y σ Δs φs s y) ^ 2)) (G.vol Y σ) ∧
        ∫ y, G.pnK Y σ ΔE φE Fs y * Real.exp (-(sectionLogWeight G Y σ Δs φs s y)) /
            (1 + (δ * sectionLogWeight G Y σ Δs φs s y) ^ 2) ∂(G.vol Y σ) ≤
          (34 / δ) * ∑ᶠ (y) (_ : y ∈ S), G.resNorm Y σ ΔE φE Δs φs s gS y *
            (2 ^ (G.dim Y + 1) * Real.pi ^ G.dim Y / ((G.dim Y - 1).factorial : ℝ))

def KawamataViehwegVanishing : Prop :=
  ∀ (Y : G.Var) (Δ : G.Dv Y),
    G.nef Y Δ → G.big Y Δ → ∀ i, 0 < i → G.hdim Y i (G.KY Y + Δ) = 0

def ArithmeticHilbertSamuel : Prop :=
  ∀ (Y : G.Var) (L : G.Dv Y) (W : HLat F) (ι : W.V →ₗ[F] G.Fn Y) (ci : InfinitePlace F → ℝ),
    Function.Injective ι → (∀ x, ι x ∈ G.H0 Y L) → W.Good →
    G.bpf Y L (ι '' (W.L : Set W.V)) →
    G.nefA Y (G.twist Y (G.ofW Y L W ι) ci 0) →
    G.arVol Y (G.twist Y (G.ofW Y L W ι) ci 0) = G.arTop Y (G.twist Y (G.ofW Y L W ι) ci 0)

def AsymptoticRiemannRoch : Prop :=
  ∀ (Y : G.Var) (L : G.Dv Y), 1 ≤ G.dim Y → G.nef Y L →
    ∃ C : ℝ, ∀ τ : ℕ, 1 ≤ τ →
      |(Module.finrank F (G.H0 Y (τ • L)) : ℝ) -
          (G.inter Y (fun _ => L) : ℝ) * (τ : ℝ) ^ G.dim Y / ((G.dim Y).factorial : ℝ)| ≤
        C * (τ : ℝ) ^ (G.dim Y - 1)

def GloballyGeneratedNef : Prop :=
  (∀ (Y : G.Var) (L : G.Dv Y) (V : Set (G.Fn Y)), V ⊆ (G.H0 Y L : Set (G.Fn Y)) → G.bpf Y L V →
    G.nef Y L) ∧
  (∀ (Y : G.Var) (N : G.Dv Y), G.nef Y N → (G.big Y N ↔ 0 < G.inter Y (fun _ => N))) ∧
  (∀ (Y : G.Var) (Ns : Fin (G.dim Y) → G.Dv Y), (∀ i, G.nef Y (Ns i)) → 0 ≤ G.inter Y Ns)

def GoodCutBasePointFree : Prop :=
  ∀ (Y : G.Var) (bd : G.Cl Y) (L B : G.Dv Y) (a n : ℕ) (w : Fin n → G.Fn Y)
    (c : Fin (G.dim Y) → Fin n → 𝓞 F),
    (∀ k, w k ∈ G.H0 Y L) →
    (∃ V : Set (G.Fn Y), V ⊆ (Submodule.span F (Set.range w) : Set (G.Fn Y)) ∧ G.bpf Y L V) →
    G.cutGood Y bd F w c →
    (∀ i, 0 < i → i < G.dim Y → G.hdim Y i (B - (a + i) • L) = 0) →
    ∀ f ∈ G.H0 Y B, a ≤ G.cutOrd Y F w c B f →
      f ∈ Submodule.span F {x | ∃ α : Fin (G.dim Y) → ℕ, ∑ i, α i = a ∧
        ∃ g ∈ G.H0 Y (B - a • L), x = (∏ i, (∑ k, (c i k : F) • w k) ^ α i) * g}

end Gen

def ArchimedeanSignatureMatching : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ), ‖M.det‖ ≤ ∏ j, Real.sqrt (∑ i, ‖M i j‖ ^ 2)

def adm3 : Prop :=
  ∀ (k : Type) [Field k] (D a : ℕ), 1 ≤ D → 1 ≤ a →
    ∃ (b : ℕ → ℕ) (e : Fin (b 0) → (Fin D →₀ ℕ))
      (d : ∀ i : ℕ, Matrix (Fin (b i)) (Fin (b (i + 1))) (MvPolynomial (Fin D) k)),
      b 0 = Nat.choose (a + D - 1) (D - 1) ∧ Function.Injective e ∧ (∀ j, ∑ l, e j l = a) ∧
      (∀ i, D ≤ i → b i = 0) ∧ (∀ i r s, (d i r s).IsHomogeneous 1) ∧
      {y | ∃ v : Fin (b 0) → MvPolynomial (Fin D) k,
          y = ∑ j, v j * MvPolynomial.monomial (e j) 1} =
        ((Ideal.span (Set.range (MvPolynomial.X : Fin D → MvPolynomial (Fin D) k)) ^ a :
          Ideal (MvPolynomial (Fin D) k)) : Set (MvPolynomial (Fin D) k)) ∧
      (∀ v : Fin (b 0) → MvPolynomial (Fin D) k,
        ∑ j, v j * MvPolynomial.monomial (e j) 1 = 0 ↔ ∃ u, v = (d 0).mulVec u) ∧
      ∀ i (v : Fin (b (i + 1)) → MvPolynomial (Fin D) k),
        (d i).mulVec v = 0 ↔ ∃ u, v = (d (i + 1)).mulVec u

def adm5 : Prop :=
  ∀ (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (Kc : Set (Fin N → ℝ)), A.det ≠ 0 → Convex ℝ Kc →
    (∀ x ∈ Kc, -x ∈ Kc) → (2 : ENNReal) ^ N * ENNReal.ofReal |A.det| < volume Kc →
    ∃ zv : Fin N → ℤ, zv ≠ 0 ∧ Matrix.mulVec A (fun i => (zv i : ℝ)) ∈ Kc

def MinkowskiCounting : Prop :=
  ∀ (N m : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (Kc : Set (Fin N → ℝ)), A.det ≠ 0 → Convex ℝ Kc →
    MeasurableSet Kc → (∀ x ∈ Kc, -x ∈ Kc) →
    (m : ENNReal) * (2 : ENNReal) ^ N * ENNReal.ofReal |A.det| < volume Kc →
    ∃ Z : Finset (Fin N → ℤ), m < Z.card ∧
      ∀ zv ∈ Z, Matrix.mulVec A (fun i => (zv i : ℝ)) ∈ Kc

def adm6 : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [DecidableEq R] (n : ℕ) (p : MvPolynomial (Fin n) R),
    p ≠ 0 → ∀ Sf : Finset R,
      ((Fintype.piFinset fun _ : Fin n => Sf).filter (fun x => MvPolynomial.eval x p = 0)).card ≤
        p.totalDegree * Sf.card ^ (n - 1)

section Gen2

variable {F : Type} [Field F] [NumberField F] [StarRing F] (G : Formalism.BasicNotions.DV.Geo F)

def AdmG : Prop :=
  OhsawaTakegoshiExtension G ∧ KawamataViehwegVanishing G ∧ adm3 ∧ ArchimedeanSignatureMatching ∧ ArithmeticHilbertSamuel G ∧ AsymptoticRiemannRoch G ∧ GloballyGeneratedNef G

def ExtensionVanishingCountingHypotheses : Prop :=
  OhsawaTakegoshiExtension G ∧ KawamataViehwegVanishing G ∧ GoodCutBasePointFree G ∧ ArchimedeanSignatureMatching ∧ adm5 ∧ MinkowskiCounting ∧ adm6 ∧ ArithmeticHilbertSamuel G

def ShareGeneral [IsTotallyComplex F] (C : ℝ) : Prop :=
  AdmG G → BaseChangeDefiniteGood G C ∧ BinomialShareLowerBound G ∧ ShareInequality G ∧ LemmaVCorollary G ∧ LemmaVStrong G ∧ LemmaVVolumeGeneral G

end Gen2

abbrev GeoClass : Type 1 :=
  ∀ (F : Type) [Field F] [NumberField F] [StarRing F], Formalism.BasicNotions.DV.Geo F → Prop

def ShareAbsoluteConstant (𝒢 : GeoClass) : Prop :=
  ∃ C : ℝ, ∀ (F : Type) [Field F] [NumberField F] [StarRing F] [IsTotallyComplex F]
    (G : Formalism.BasicNotions.DV.Geo F), 𝒢 F G → ShareGeneral G C

section Rec

variable (D : Formalism.BasicNotions.D7) (X : Formalism.BasicNotions.DivX D)

def Conclusion1 (C : ℝ) : Prop := BaseChangeDefiniteGood X.geo C
def Conclusion2 : Prop := BinomialShareLowerBound X.geo
def PointsLemma : Prop := ShareInequality X.geo
def Conclusion4 : Prop := LemmaVCorollary X.geo
def Conclusion5 : Prop := LemmaVStrong X.geo
def Conclusion6 : Prop := LemmaVVolumeGeneral X.geo
def adm1 : Prop := OhsawaTakegoshiExtension X.geo
def adm2 : Prop := KawamataViehwegVanishing X.geo
def adm7 : Prop := ArithmeticHilbertSamuel X.geo
def adm8 : Prop := AsymptoticRiemannRoch X.geo
def adm9 : Prop := GloballyGeneratedNef X.geo

def admitted : Prop := AdmG X.geo

theorem hilbert_samuel_of_hypotheses (h : admitted D X) : adm7 D X := h.2.2.2.2.1

def Stmt (C : ℝ) : Prop := ShareGeneral X.geo C

end Rec

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def AdmF : Prop := ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, admitted (Fm.D x i) (Fm.X x i)

def Conclusion1Family (C : ℝ) : Prop := ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, Conclusion1 (Fm.D x i) (Fm.X x i) C

def Conclusion2Family : Prop := ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, Conclusion2 (Fm.D x i) (Fm.X x i)

def Conclusion3Family : Prop := ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, PointsLemma (Fm.D x i) (Fm.X x i)

def SlopeLemmaFamily : Prop := ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, Conclusion4 (Fm.D x i) (Fm.X x i)

def SlopeLossFamily : Prop := ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, Conclusion5 (Fm.D x i) (Fm.X x i)

def Conclusion6Family : Prop := ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, Conclusion6 (Fm.D x i) (Fm.X x i)

def ShareFamilyAtConstant (C : ℝ) : Prop :=
  AdmF Fm → Conclusion1Family Fm C ∧ Conclusion2Family Fm ∧ Conclusion3Family Fm ∧ SlopeLemmaFamily Fm ∧ SlopeLossFamily Fm ∧ Conclusion6Family Fm

def KudlaFamilyStatement (_CH : ℝ) : Prop :=
  AdmF Fm → (∃ C : ℝ, Conclusion1Family Fm C) ∧ Conclusion2Family Fm ∧ Conclusion3Family Fm ∧ SlopeLemmaFamily Fm ∧ SlopeLossFamily Fm ∧ Conclusion6Family Fm

end Fam

def ClosedAbsoluteShare (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∃ C : ℝ, Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ShareFamilyAtConstant Fm C)

end Formalism.MainNotions.HeightShare

end
