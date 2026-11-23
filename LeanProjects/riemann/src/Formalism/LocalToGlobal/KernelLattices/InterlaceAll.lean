import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
import Formalism.LocalToGlobal.Columns.CoefficientsModP.BaseCh

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Col.Br

section Io

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)

def upperParabolic : Pol K ι n →ₐ[K] Pol K ι N := rename (upVar hN)

def zExp (b : ι → Fin n → ℕ) : ι × Fin N × Fin N →₀ ℕ :=
  ∑ τ, ∑ s, Finsupp.single (τ, iL hN, iC hN s) (b τ s)

def bFac (b : ι → Fin n → ℕ) : ℕ := ∏ τ, ∏ s, (b τ s).factorial

def raise (b : ι → Fin n → ℕ) : Pol K ι n →ₗ[K] Pol K ι N :=
  LinearMap.mulLeft K (monomial (zExp hN b) (1 : K)) ∘ₗ (upperParabolic hN).toLinearMap

variable (lam : ι → DomWeight N) (sg : ι → DomWeight n)

def ioConst (K : Type) [Field K] (lam : ι → DomWeight N) (sg : ι → DomWeight n) : K :=
  ∏ τ, ((cBr hN (lam τ) (sg τ) : ℤ) : K) * fockB (xiBr K hN (lam τ) (sg τ)) (xiBr K hN (lam τ) (sg τ)) /
    (fockB (extremal K n (sg τ)) (extremal K n (sg τ)) * ((∏ s, (bExp hN lam sg τ s).factorial : ℕ) : K))

def ioStd : VV K sg →ₗ[K] VV K lam :=
  ioConst hN K lam sg • (projVV lam ∘ₗ raise hN (bExp hN lam sg) ∘ₗ (VV K sg).subtype)

def ioAt (t : ι → K) : VV K sg →ₗ[K] VV K lam := (∏ τ, t τ ^ (-nBr (lam τ) (sg τ))) • ioStd hN lam sg

def hTen (K : Type) [Field K] {n : ℕ} (sg : ι → DomWeight n) : Pol K ι n := ten fun τ => extremal K n (sg τ)

def xiTen (K : Type) [Field K] (lam : ι → DomWeight N) (sg : ι → DomWeight n) : Pol K ι N :=
  ten fun τ => xiBr K hN (lam τ) (sg τ)

def SameShiftAll : Prop := ∀ τ, SameShift (lam τ) (sg τ)

def InterlaceAll : Prop := ∀ τ, Interlace hN (lam τ) (sg τ)

def BrTranspose (K : Type) [Field K] : Prop :=
  ∀ (f : VV K lam) (g : VV K sg), pairBK sg (brStd hN lam sg f) g = pairBK lam f (ioStd hN lam sg g)

def IoHw (K : Type) [Field K] [CharZero K] : Prop :=
  InterlaceAll hN lam sg → SameShiftAll lam sg → ∀ h : hTen K sg ∈ VV K sg, (ioStd hN lam sg ⟨hTen K sg, h⟩ : Pol K ι N) = ((∏ τ, (cBr hN (lam τ) (sg τ) : ℤ) : ℤ) : K) • xiTen hN K lam sg

def IoEquiv (K : Type) [Field K] [CharZero K] : Prop :=
  SameShiftAll lam sg → ∀ (g : ι → GL (Fin n) K) (x : VV K sg) (hx : actP sg g x.1 ∈ VV K sg),
    (ioStd hN lam sg ⟨actP sg g x.1, hx⟩ : Pol K ι N) =
      actP lam (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL K n N hN.symm (g τ)) (ioStd hN lam sg x : Pol K ι N)

def CoefXi (K : Type) [Field K] : Prop :=
  coefLast hN (bExp hN lam sg) (xiTen hN K lam sg) = hTen K sg

end Io

section Fn

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)
  (lam : ι → DomWeight N) (sg : ι → DomWeight n)

def lowerFn (Pt : Type) (t : ι → K) : (Pt → VV K lam) →ₗ[K] (Pt → VV K sg) :=
  (brAt hN lam sg t).compLeft Pt

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

def lowerK (u : Pr.Word) : (RowPt Pr R sel mu → VV X.K (W.lamTrue u R.m)) →ₗ[X.K] (RowPt Pr R sel mu → VV X.K W.sgTrue) :=
  (brC W u).compLeft _

def periodK (P : LevFam X.E X.K R.r Pr.vGs) (h : (mtildeGSD W Ch sel mu P).Ok) :
    (RowPt Pr R sel mu → VV X.K W.sgTrue) →ₗ[X.K] (RowPt Pr R sel mu → VV X.K W.sgTrue) →ₗ[X.K] X.K :=
  (mtildeGSD W Ch sel mu P).csOf h (mtildeGSD W Ch sel mu P).outSec fun d' =>
    (pairBK (K := X.K) W.sgTrue).compl₁₂ (LinearMap.proj d') (LinearMap.proj d')

end Fn

section BC

variable {K K' : Type} [Field K] [Field K'] (j : K →+* K') {ι : Type} [Fintype ι] {n : ℕ}

def bcVV (lam : ι → DomWeight n) : VV K lam →+ VV K' lam where
  toFun x := ⟨MvPolynomial.map j x.1, ((Formalism.L2.DIV.baseChangeSpace_holds K K' j ι n lam).1 x.1).1 x.2⟩
  map_zero' := by ext1; simp
  map_add' x y := by ext1; simp

def BrAtMap {N : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) : Prop :=
  ∀ (t : ι → K) (x : VV K lam), brAt hN lam sg (fun τ => j (t τ)) (bcVV j lam x) = bcVV j sg (brAt hN lam sg t x)

end BC

section One

variable (K : Type) [Field K] {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n)

def toUnit (N : ℕ) : MvPolynomial (Fin N × Fin N) K ≃ₐ[K] Pol K Unit N :=
  renameEquiv K (Equiv.punitProd (Fin N × Fin N)).symm

def brOne : MvPolynomial (Fin N × Fin N) K →ₗ[K] MvPolynomial (Fin n × Fin n) K :=
  (toUnit K n).symm.toLinearMap ∘ₗ (VV K (fun _ : Unit => sg)).subtype ∘ₗ brStdP hN (fun _ : Unit => lam) (fun _ : Unit => sg) ∘ₗ
    (toUnit K N).toLinearMap

def beOnVal : ℝ := |((cBr hN lam sg : ℤ) : ℝ)| * Real.sqrt (kapBr ℝ hN lam sg)

end One

section Record

open Formalism.MainNotions.product_first_zeroth_parts

def BrOneIsBr (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) : Prop :=
  ∀ τ, Formalism.MainNotions.PrimeDegreeVariant.Interlace (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ) →
    Formalism.MainNotions.PrimeDegreeVariant.IsBr (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ) (brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ))

def BeOnTie (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) : Prop :=
  ∀ τ, (D.fm u).beOn τ = opNorm D u τ (brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ))

def BeOnEq (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) : Prop :=
  ∀ τ, Formalism.MainNotions.PrimeDegreeVariant.Interlace (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ) →
    opNorm D u τ (brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)) =
    beOnVal (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)

def LowerTie (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) : Prop :=
  ∃ P : Pend D u, ∀ τ, P.br τ = brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)

def brTen (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
    MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ :=
  blk fun τ => brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)

def LowerTieAt (D : Formalism.BasicNotions.D7) (u : D.what₂.Word)
    (coM : D.what₂.places.Pl → (D.fm u).clsP → (((D.mem u).C.Y D.R.m → ℂ) →ₗ[ℂ]
      MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ))
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) : Prop :=
  (∀ φ ∈ (D.fm u).Fi D.R.m, Pt D u φ ∈ (D.fm u).ptC) ∧
  ∃ P : Pend D u, P.coM = coM ∧ P.gP = gP ∧ ∀ τ, P.br τ = brOne ℂ (Nm_succ D.R).symm (lamTr D u τ) (sgTr D u τ)

def FullAt (D : Formalism.BasicNotions.D7) (u : D.what₂.Word)
    (coM : D.what₂.places.Pl → (D.fm u).clsP → (((D.mem u).C.Y D.R.m → ℂ) →ₗ[ℂ]
      MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ))
    (w : D.what₂.places.Pl) (c : (D.fm u).clsP) : Prop :=
  ∀ p ∈ CSpan ((D.fm u).lam D.R.m), ∃ φ ∈ (D.fm u).Fi D.R.m, coM w c (φ ((D.fm u).til c)) = p

def SeenAt (D : Formalism.BasicNotions.D7) (u : D.what₂.Word)
    (coM : D.what₂.places.Pl → (D.fm u).clsP → (((D.mem u).C.Y D.R.m → ℂ) →ₗ[ℂ]
      MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ))
    (w : D.what₂.places.Pl) (c : (D.fm u).clsP) : Prop :=
  ∃ φ ∈ (D.fm u).Fi D.R.m, brTen D u (coM w c (φ ((D.fm u).til c))) ≠ 0

def negOp (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) :
    MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
      MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ :=
  blk fun τ => sqAct ℂ _ (lamTr D u τ) (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) (-1))

def sgnSg (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) : ℂ := ∏ τ, (-1 : ℂ) ^ Formalism.MainNotions.PrimeDegreeVariant.wsum (sgTr D u τ)

def ValEps (D : Formalism.BasicNotions.D7) (u : D.what₂.Word)
    (coM : D.what₂.places.Pl → (D.fm u).clsP → (((D.mem u).C.Y D.R.m → ℂ) →ₗ[ℂ]
      MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ))
    (w : D.what₂.places.Pl) (c : (D.fm u).clsP) (ε : ℂ) : Prop :=
  ∀ φ ∈ (D.fm u).Fi D.R.m, negOp D u (coM w c (φ ((D.fm u).til c))) = ε • coM w c (φ ((D.fm u).til c))

def FullAtEps (D : Formalism.BasicNotions.D7) (u : D.what₂.Word)
    (coM : D.what₂.places.Pl → (D.fm u).clsP → (((D.mem u).C.Y D.R.m → ℂ) →ₗ[ℂ]
      MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ))
    (w : D.what₂.places.Pl) (c : (D.fm u).clsP) (ε : ℂ) : Prop :=
  ∀ p ∈ CSpan ((D.fm u).lam D.R.m), negOp D u p = ε • p → ∃ φ ∈ (D.fm u).Fi D.R.m, coM w c (φ ((D.fm u).til c)) = p

def ParityAt (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (ε : ℂ) : Prop := ε = sgnSg D u

def lowerNormAt (D : Formalism.BasicNotions.D7) (u : D.what₂.Word)
    (coM : D.what₂.places.Pl → (D.fm u).clsP → (((D.mem u).C.Y D.R.m → ℂ) →ₗ[ℂ]
      MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ))
    (gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ)
    (w : D.what₂.places.Pl) (φ : Fn D u D.R.m) : ℝ :=
  ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
    (nfAll (D.fm u).sg (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (brTen D u (coM w c (φ ((D.fm u).til c)))))
      (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (brTen D u (coM w c (φ ((D.fm u).til c)))))).re

structure LowerShape {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} (P : PeriodMap R C)
    (Pt : Type) {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) (t : ι → ℂˣ) where
  iz : P.Wz ≃ₗ[ℂ] (Pt → VV ℂ lam)
  ir : P.Wrow ≃ₗ[ℂ] (Pt → VV ℂ sg)
  comm : ∀ x, ir (P.lowerMap x) = lowerFn hN lam sg Pt (fun τ => (t τ : ℂ)) (iz x)

end Record

section Chi

variable {G : Type} [CommGroup G]

def chiScalar (mt chi : G →* ℂˣ) (N N' : ℕ) (x x' : G) : ℂˣ :=
  ((mt⁻¹ * chi ^ (-((N' / 2 : ℕ) : ℤ))) x * (mt * chi ^ (((N / 2 : ℕ) : ℤ))) x') *
    (chi x ^ (((N' / 2 : ℕ) : ℤ)) * chi x' ^ (-((N / 2 : ℕ) : ℤ)))

end Chi

end Formalism.L2.Ker
