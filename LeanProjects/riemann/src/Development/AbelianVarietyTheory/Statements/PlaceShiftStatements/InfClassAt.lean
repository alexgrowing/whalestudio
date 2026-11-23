import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.SumSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Sizes

variable {D : D7}

abbrev PlL (D : D7) : Type := HeightOneSpectrum (𝓞 D.what₂.LL)

def Loss (dl : PlL D → ℝ) (B : ℝ) : Prop :=
  (∀ w, 0 ≤ dl w) ∧ {w | dl w ≠ 0}.Finite ∧ ∀ s : Finset (PlL D), ∑ w ∈ s, lw w * dl w ≤ B

def LossLe (w : PlL D) (z : ℂ) (a : ℝ) : Prop := ∃ y, D.what₂.embLL y = z ∧ (y = 0 ∨ -a ≤ (vw w y : ℝ))

def AbsLe (σ : D.what₂.LL →+* ℂ) (z : ℂ) (B : ℝ) : Prop := ∃ y, D.what₂.embLL y = z ∧ ‖σ y‖ ≤ Real.exp B

variable {n n' : ℕ} (lam : D.what₂.Tau → DomWeight n) (lam' : D.what₂.Tau → DomWeight n')

def InLat (w : PlL D) (a : ℝ) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (v : VV ℂ lam) : Prop :=
  ∃ (u : VV D.what₂.LL lam) (s : D.what₂.LL), GlobalTheory.CoefModel.mapVV D.what₂.embLL lam u = v ∧ s ≠ 0 ∧ (vw w s : ℝ) ≤ a ∧
    s • u ∈ nabAtr (labLL D) lam Λ

def nrm (H : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (v : VV ℂ lam) : ℝ := (pairK lam H v v).re

def NrmLe (σ : D.what₂.LL →+* ℂ) (v : VV ℂ lam) (B : ℝ) : Prop :=
  ∃ u : VV D.what₂.LL lam, GlobalTheory.CoefModel.mapVV D.what₂.embLL lam u = v ∧ nrm lam (fun _ => 1) (GlobalTheory.CoefModel.mapVV σ lam u) ≤ B

theorem LossLe.mono {w : PlL D} {z : ℂ} {a a' : ℝ} (h : LossLe w z a) (ha : a ≤ a') : LossLe w z a' :=
  let ⟨y, e, h⟩ := h
  ⟨y, e, h.imp_right fun h => (neg_le_neg ha).trans h⟩

example (w : PlL D) (σ : D.what₂.LL →+* ℂ) : LossLe w 0 0 ∧ AbsLe σ 1 0 := ⟨⟨0, map_zero _, Or.inl rfl⟩, 1, map_one _, by simp⟩

variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

def sig : ℝ := ∑ v ∈ G.pl.S0, (G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal)

def bOne (C b : ℝ) : ℝ := C * D.R.f * D.R.m * (bigN D : ℝ) ^ 2 * (Real.log b + sig G) * b

def aOne (C b : ℝ) : ℝ := C * D.R.f * bigN D * b * Real.log b + C * D.R.m * (bigN D : ℝ) ^ 2 * sig G

def Away (t : T) (w : PlL D) : Prop :=
  ∀ PP ∈ L.Q t, PP.under (𝓞 D.host.F) ∈ G.pl.S0 ∨ ∀ l : ℕ, l.Prime → (l : 𝓞 D.host.E) ∈ PP.asIdeal → (l : 𝓞 D.what₂.LL) ∉ w.asIdeal

open Classical in

def depL (l : ℕ) : ℕ := (G.pl.W0.filter fun PP => (l : 𝓞 D.host.E) ∈ PP.asIdeal).sup (depthAt G)

variable {G} {W : G.Weil} (S : GridChoice W Set.univ)

def latAt (X : Node) (x : FinPt G X) : Submodule (𝓞 D.host.E) (Fin (G.V X).rank → D.host.E) :=
  (Formalism.UG.CS.globLat (finG (G.V X) x) (G.Λ X)).comap ((S.N.fr X).1.mulVecLin.restrictScalars (𝓞 D.host.E))

def Occurs (t : T) (Φ : G.Datum) (β : CosFam G t) (d : PureDat G t) : Prop :=
  β ∈ S.supp t Φ ∧ ∃ τ, IsCosetExpansion S t Φ β (expDepth S t Φ β) τ ∧ d ∈ τ.support

def topVal (Ψ : GLf G → WtSp G) (x : FinPt G (.top 0)) : VV ℂ (wt G (.top 0)) :=
  rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ (psiC Ψ x)

def rowVal (v : VV ℂ (listedWt G (.grid 0 D.R.m))) : VV ℂ (wt G (.grid 0 D.R.m)) :=
  rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ (funOf (listedWt G (.grid 0 D.R.m)) v)

variable (G) in

abbrev lastPair : VV ℂ (wt G (.top D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m)) →ₗ[ℂ] ℂ :=
  brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))

end Sizes

abbrev ChQ := ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}, Face D A → Choice R → ℝ → ℝ → Prop

def BigC (Q : ChQ) : Prop :=
  ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ C0 : ℝ, ∀ ε C : ℝ, C0 ≤ C → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → Q F ch C large₂.sc.b

section Claims

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (F : Face D A) (ch : Choice R) (C b : ℝ)

def formOf (t : T) (x : Fin ((A.fam.R t).nV (A.fam.lvl F.P0 F.ψ0)) → D.what₂.LL) : A.fam.amb.FR t :=
  (A.fam.R t).S.basis.equivFun.symm (((A.fam.R t).vE (A.fam.lvl F.P0 F.ψ0)).mulVec x)

def DepthAt : Prop := ∀ t Φ, ∀ β ∈ ch.S.supp t Φ,
  (∃ τ, IsCosetExpansion ch.S.toGridChoice t Φ β (expDepth ch.S.toGridChoice t Φ β) τ) ∧
    ∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → Away ch.G t w →
      padicValNat l (expDepth ch.S.toGridChoice t Φ β) ≤ depL ch.G l

def FinScalAt : Prop := ∃ dl, Loss dl (D.R.m * bOne ch.G C b) ∧ ∀ w : PlL D, LossLe w ch.S.sAA (dl w)

def FinCoefAt : Prop := ∃ dl, Loss dl (D.R.m * bOne ch.G C b) ∧ ∀ t w, Away ch.G t w → ∀ Φ, ∀ β ∈ ch.S.supp t Φ,
  LossLe w (∏ v, ((ch.S.term t Φ β v).coef : ℂ)) (dl w)

def FinDatAt : Prop := ∃ dl, Loss dl (D.R.m * bOne ch.G C b) ∧ ∀ t w, Away ch.G t w → ∀ Φ, ∀ β ∈ ch.S.supp t Φ, ∀ x y,
  LossLe w (∏ v, (ch.S.term t Φ β v).datum (ch.S.colAt t v x) (ch.S.rowAt t v y)) (dl w)

def FinGamAt : Prop := ∃ dl, Loss dl (D.R.m * bOne ch.G C b) ∧ ∀ t (w : PlL D) Φ β (c : ch.S.Classes t Φ β),
  LossLe w (ch.S.invGam c) (dl w)

def FinTopAt : Prop := ∃ dl, Loss dl (bOne ch.G C b) ∧ ∀ t w, Away ch.G t w → ∀ Φ β d, Occurs ch.S.toGridChoice t Φ β d →
  ∀ (c : ch.S.Classes t Φ β) (j : Fin D.R.m) (a : ℝ) v, InLat _ w a (latAt ch.S.toGridChoice (.top j) (ch.S.ptTop c j)) v →
    InLat _ w (a + dl w) (latAt ch.S.toGridChoice (.top (j + 1)) (ch.S.ptTop c (j + 1)))
      (ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) v)

def FinRowAt : Prop := ∃ dl, Loss dl (bOne ch.G C b) ∧ ∀ t w, Away ch.G t w → ∀ Φ β d, Occurs ch.S.toGridChoice t Φ β d →
  ∀ (c : ch.S.Classes t Φ β) (i : Fin D.R.m) (a : ℝ) v,
    InLat _ w a (latAt ch.S.toGridChoice (.grid i D.R.m) (ch.S.ptRow c i)) v →
    InLat _ w (a + dl w) (latAt ch.S.toGridChoice (.grid (i + 1) D.R.m) (ch.S.ptRow c (i + 1)))
      (ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) v)

def FinPairAt : Prop := ∃ dl, Loss dl (bOne ch.G C b) ∧ ∀ (w : PlL D) (y : FinPt ch.G (.grid D.R.m D.R.m)) (a a' : ℝ) u v,
  InLat _ w a (latAt ch.S.toGridChoice (.top D.R.m) (finEmb ch.G.sp.topDec y)) u →
    InLat _ w a' (latAt ch.S.toGridChoice (.grid D.R.m D.R.m) y) v → LossLe w (lastPair ch.G u v) (a + a' + dl w)

def FinPsiAt : Prop := ∀ (w : PlL D) c, ∀ u ∈ wLat ch.G (ch.rp.lat c), ∀ x,
  InLat _ w 0 (latAt ch.S.toGridChoice (.top 0) x) (topVal ch.S.toGridChoice (ch.rp.delta c u) x)

def FinFormAt : Prop := ∃ dl, Loss dl (bOne ch.G C b) ∧ ∀ t (w : PlL D), ∀ x ∈ (A.fam.R t).Mt (A.fam.lvl F.P0 F.ψ0), ∀ y,
  InLat _ w (dl w) (latAt ch.S.toGridChoice (.grid 0 D.R.m) y)
    (rowVal ch.S.toGridChoice (ch.S.formC t (R.jX t (formOf F t x)) y))

def FinAt : Prop := ∃ dl, Loss dl (D.R.m * bOne ch.G C b / 2) ∧ ∀ X' M, IsTestLat ch.G ch.rp ch.n ch.e X' M →
  ∀ t w, Away ch.G t w → ∀ x ∈ (A.fam.R t).Mt (A.fam.lvl F.P0 F.ψ0), ∀ y : Fin ch.n → D.what₂.LL,
    (∀ a, D.what₂.embLL (y a) = vK ch t (formOf F t x) a) → ∃ s : D.what₂.LL, s ≠ 0 ∧ (vw w s : ℝ) ≤ dl w ∧ s • y ∈ M

def AwayAt : Prop := ∀ w, Away ch.G (R.mu w) w

def InfScalAt : Prop := ∀ σ : D.what₂.LL →+* ℂ, AbsLe σ ch.S.sAA (D.R.m * aOne ch.G C b)

def InfTensAt : Prop := ∀ (σ : D.what₂.LL →+* ℂ) Φ, ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ x y,
  AbsLe σ ((∏ v, ((ch.S.term A.μ0 Φ β v).coef : ℂ)) *
    ∏ v, (ch.S.term A.μ0 Φ β v).datum (ch.S.colAt A.μ0 v x) (ch.S.rowAt A.μ0 v y)) (C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * sig ch.G)

def InfCountAt : Prop := (Nat.card ch.G.Datum : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b) ∧ ∀ Φ,
  ((ch.S.supp A.μ0 Φ).ncard : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b) ∧ ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ τ,
    IsCosetExpansion ch.S.toGridChoice A.μ0 Φ β (expDepth ch.S.toGridChoice A.μ0 Φ β) τ →
      (τ.support.card : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b)

def InfClassAt : Prop := (Nat.card ch.G.ClPlus : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b) ∧ ∀ Φ, ∀ β ∈ ch.S.supp A.μ0 Φ,
  (Nat.card (ch.S.Classes A.μ0 Φ β) : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b)

def InfTopAt : Prop := ∃ g : InfinitePlace D.what₂.LL → ℝ, Formalism.PairingDivisionLocalBalance.meanInf _ g ≤ aOne ch.G C b ∧
  ∀ (p : InfinitePlace D.what₂.LL) Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (j : Fin D.R.m) B v,
    NrmLe _ p.embedding v B →
      NrmLe _ p.embedding (ch.S.Z.kkMap 1 (d.1 j) (ch.S.ptTop c j) (ch.S.ptTop c (j + 1)) v) (Real.exp (g p) * B)

def InfRowAt : Prop := ∃ g : InfinitePlace D.what₂.LL → ℝ, Formalism.PairingDivisionLocalBalance.meanInf _ g ≤ aOne ch.G C b ∧
  ∀ (p : InfinitePlace D.what₂.LL) Φ β d, Occurs ch.S.toGridChoice A.μ0 Φ β d → ∀ (c : ch.S.Classes A.μ0 Φ β) (i : Fin D.R.m) B v,
    NrmLe _ p.embedding v B →
      NrmLe _ p.embedding (ch.S.Z.kkMap 1 (d.2 i) (ch.S.ptRow c i) (ch.S.ptRow c (i + 1)) v) (Real.exp (g p) * B)

def InfPairAt : Prop := ∀ (σ : D.what₂.LL →+* ℂ) B B' u v, NrmLe _ σ u B → NrmLe _ σ v B' →
  ∃ y, D.what₂.embLL y = lastPair ch.G u v ∧ ‖σ y‖ ^ 2 ≤ Real.exp (aOne ch.G C b) * B * B'

def InfPsiAt : Prop := ∀ (σ : D.what₂.LL →+* ℂ) c u x, NrmLe _ σ (topVal ch.S.toGridChoice (ch.rp.delta c u) x)
  (nrm (LaP ch.G) (fun τ => (gramKd (emb D) (Xp ch.G).gram τ).map σ) (GlobalTheory.CoefModel.mapVV σ _ u))

def InfFormAt : Prop := ∀ (σ : D.what₂.LL →+* ℂ) x y,
  NrmLe _ σ (rowVal ch.S.toGridChoice (ch.S.formC A.μ0 (R.jX A.μ0 (formOf F A.μ0 x)) y))
    (Real.exp (D.R.m * aOne ch.G C b) *
      (star (fun i => σ (x i)) ⬝ᵥ (((A.fam.R A.μ0).HV (A.fam.lvl F.P0 F.ψ0)).map σ).mulVec fun i => σ (x i)).re)

def InfAt : Prop := ∀ X' M, IsTestLat ch.G ch.rp ch.n ch.e X' M → ∀ X, IsMetric ((A.fam.R A.μ0).HV (A.fam.lvl F.P0 F.ψ0)) X →
  ∀ V : Matrix (Fin ch.n) (Fin ((A.fam.R A.μ0).nV (A.fam.lvl F.P0 F.ψ0))) D.what₂.LL,
    (∀ x a, D.what₂.embLL (V.mulVec x a) = vK ch A.μ0 (formOf F A.μ0 x) a) →
      Formalism.HN.htMap (Pi.basisFun _ _) X (Pi.basisFun _ _) X' V.mulVecLin ≤ D.R.m * aOne ch.G C b

end Claims

def DepthK : Prop := BigC fun _ ch _ _ => DepthAt ch

def FinScalK : Prop := BigC fun _ ch C b => FinScalAt ch C b

def FinCoefK : Prop := BigC fun _ ch C b => FinCoefAt ch C b

def FinDatK : Prop := BigC fun _ ch C b => FinDatAt ch C b

def FinGamK : Prop := BigC fun _ ch C b => FinGamAt ch C b

def FinTopK : Prop := BigC fun _ ch C b => FinTopAt ch C b

def FinRowK : Prop := BigC fun _ ch C b => FinRowAt ch C b

def FinPairK : Prop := BigC fun _ ch C b => FinPairAt ch C b

def FinPsiK : Prop := BigC fun _ ch _ _ => FinPsiAt ch

def FinFormK : Prop := BigC fun F ch C b => FinFormAt F ch C b

def FinK : Prop := BigC fun F ch C b => FinAt F ch C b

def AwayK : Prop := BigC fun _ ch _ _ => AwayAt ch

def InfScalK : Prop := BigC fun _ ch C b => InfScalAt ch C b

def InfTensK : Prop := BigC fun _ ch C _ => InfTensAt ch C

def InfCountK : Prop := BigC fun _ ch C b => InfCountAt ch C b

def InfClassK : Prop := BigC fun _ ch C b => InfClassAt ch C b

def InfTopK : Prop := BigC fun _ ch C b => InfTopAt ch C b

def InfRowK : Prop := BigC fun _ ch C b => InfRowAt ch C b

def InfPairK : Prop := BigC fun _ ch C b => InfPairAt ch C b

def InfPsiK : Prop := BigC fun _ ch _ _ => InfPsiAt ch

def InfFormK : Prop := BigC fun F ch C b => InfFormAt F ch C b

def InfK : Prop := BigC fun F ch C b => InfAt F ch C b

end GlobalTheory.SumSize

end
