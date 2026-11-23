import Mathlib
import Formalism.LocalToGlobal.Columns.AtTLemmas
import Formalism.LocalRingCardinality.DataArith
import Formalism.GL3MeanSquares.RationalMatrixPrimeOrderBound

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]

def lenO (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (Ow w) V) : ℕ∞ :=
  Module.length (Ow w) (A ⧸ B.comap A.subtype)

def lenOU (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (Ow w) V) : ℚ :=
  ((lenO w A B).toNat : ℚ) / (eW w : ℚ)

def mapO {V' : Type} [AddCommGroup V'] [Module K V'] (w : HeightOneSpectrum (𝓞 K)) (f : V →ₗ[K] V') (A : Submodule (Ow w) V) :
    Submodule (Ow w) V' :=
  A.map (f.restrictScalars (Ow w))

def piO {ι : Type} (w : HeightOneSpectrum (𝓞 K)) (A : ι → Submodule (Ow w) V) : Submodule (Ow w) (ι → V) where
  carrier := {x | ∀ i, x i ∈ A i}
  add_mem' := fun hx hy i => (A i).add_mem (hx i) (hy i)
  zero_mem' := fun i => (A i).zero_mem
  smul_mem' := fun r _ hx i => (A i).smul_mem r (hx i)

def scalO (w : HeightOneSpectrum (𝓞 K)) (c : K) (A : Submodule (Ow w) V) : Submodule (Ow w) V :=
  mapO w (c • (LinearMap.id : V →ₗ[K] V)) A

end Gen

def sumShiftW {n : ℕ} (lam : DomWeight n) (b : ℤ) : ℤ := ∑ i, (lam.w i + b)

section LemB

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def TbSwC (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) (b : ℤ) : Submodule (Ow w) (ColV W Ch u j) :=
  scalO w ((Pr.T u : X.K) ^ b) (SwC W Ch u j w)

def TbSwNabC (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) (b : ℤ) : Submodule (Ow w) (ColV W Ch u j) :=
  scalO w ((Pr.T u : X.K) ^ b) (SwNabC W Ch u j w)

def LemBInclAt (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) (P : {P // P ∈ Pr.vT u}) (b : ℤ) : Prop :=
  TbSwC W Ch u j w b ≤ BvWC W Ch u j w P

def LemBIdxAt (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (P : {P // P ∈ Pr.vT u}) (τ : X.Tau) (b : ℤ) : Prop :=
  ∃ n : ℕ, lenO w (BvWC W Ch u 0 w P) (TbSwC W Ch u 0 w b) = n ∧
    (R.N 0 : ℤ) * (n : ℤ) = (eW w : ℤ) * (finrank X.K (MfV W Ch u) : ℤ) * sumShiftW (W.lamTrue u 0 τ) b

def LemBInclNabAt (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) (P : {P // P ∈ Pr.vT u}) (b : ℤ) : Prop :=
  TbSwNabC W Ch u j w b ≤ BvNabWC W Ch u j w P

def LemBIdxNabAt (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (P : {P // P ∈ Pr.vT u}) (τ : X.Tau) (b : ℤ) : Prop :=
  ∃ n : ℕ, lenO w (BvNabWC W Ch u 0 w P) (TbSwNabC W Ch u 0 w b) = n ∧
    (R.N 0 : ℤ) * (n : ℤ) = (eW w : ℤ) * (finrank X.K (MfV W Ch u) : ℤ) * sumShiftW (W.lamTrue u 0 τ) b

def LemmaBIncl : Prop :=
  X.Ok → Pr.Ok → ∀ (u : Pr.Word) (j : ℕ), j ≤ R.m → ∀ (w : HeightOneSpectrum (𝓞 X.K)) (τ : X.Tau) (P : {P // P ∈ Pr.vT u}), SeesP w τ P.1 →
    ∀ b : ℤ, -(W.lamTrue u j τ).detShift ≤ b → LemBInclAt W Ch u j w P b

def LemmaBIdx : Prop :=
  X.Ok → Pr.Ok → 2 * X.f * R.k < Pr.g 0 - 1 →
    ∀ (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (τ : X.Tau) (P : {P // P ∈ Pr.vT u}), SeesP w τ P.1 →
      ∀ b : ℤ, -(W.lamTrue u 0 τ).detShift ≤ b → LemBIdxAt W Ch u w P τ b

def LemmaBInclNab : Prop :=
  X.Ok → Pr.Ok → ∀ (u : Pr.Word) (j : ℕ), j ≤ R.m → ∀ (w : HeightOneSpectrum (𝓞 X.K)) (τ : X.Tau) (P : {P // P ∈ Pr.vT u}), SeesP w τ P.1 →
    ∀ b : ℤ, -(W.lamTrue u j τ).detShift ≤ b → LemBInclNabAt W Ch u j w P b

def LemmaBIdxNab : Prop :=
  X.Ok → Pr.Ok → 2 * X.f * R.k < Pr.g 0 - 1 →
    ∀ (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (τ : X.Tau) (P : {P // P ∈ Pr.vT u}), SeesP w τ P.1 →
      ∀ b : ℤ, -(W.lamTrue u 0 τ).detShift ≤ b → LemBIdxNabAt W Ch u w P τ b

def CoefBInclAt (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) (P : {P // P ∈ Pr.vT u}) (b : ℤ) : Prop :=
  ∀ d : ColDeco X Pr u (R.N j),
    scalO w ((Pr.T u : X.K) ^ b) (atW w (delAtr X.emb (W.lamTrue u j) d.1.Lsh)) ≤ atW w (BvLat W u j P d)

def CoefBIdxAt (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (P : {P // P ∈ Pr.vT u}) (τ : X.Tau) (b : ℤ) : Prop :=
  ∀ d : ColDeco X Pr u (R.N 0), ∃ n : ℕ,
    lenO w (atW w (BvLat W u 0 P d)) (scalO w ((Pr.T u : X.K) ^ b) (atW w (delAtr X.emb (W.lamTrue u 0) d.1.Lsh))) = n ∧
      (R.N 0 : ℤ) * (n : ℤ) = (eW w : ℤ) * (finrank X.K (VV X.K (W.lamTrue u 0)) : ℤ) * sumShiftW (W.lamTrue u 0 τ) b

def CoefLemmaBIncl : Prop :=
  X.Ok → Pr.Ok → ∀ (u : Pr.Word) (j : ℕ), j ≤ R.m → ∀ (w : HeightOneSpectrum (𝓞 X.K)) (τ : X.Tau) (P : {P // P ∈ Pr.vT u}), SeesP w τ P.1 →
    ∀ b : ℤ, -(W.lamTrue u j τ).detShift ≤ b → CoefBInclAt W u j w P b

def CoefLemmaBIdx : Prop :=
  X.Ok → Pr.Ok → ∀ (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (τ : X.Tau) (P : {P // P ∈ Pr.vT u}), SeesP w τ P.1 →
    ∀ b : ℤ, -(W.lamTrue u 0 τ).detShift ≤ b → CoefBIdxAt W u w P τ b

end LemB

section LemC

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def UramOp (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) : Module.End X.K (ColRamV W Ch u j) :=
  (UOp W Ch u j P).restrict fun _ h => UOp_mem_ColRamV W Ch u j P h

def DramOp (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) : Module.End X.K (ColRamV W Ch u j) :=
  (DOp W Ch u j P).restrict fun _ h => DOp_mem_ColRamV W Ch u j P h

def TbUC (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) (b : ℤ) : Module.End X.K (ColV W Ch u j) :=
  ((Pr.T u : X.K) ^ b) • UOp W Ch u j P

def TbUR (u : Pr.Word) (j : ℕ) (P : {P // P ∈ Pr.vT u}) (b : ℤ) : Module.End X.K (ColRamV W Ch u j) :=
  ((Pr.T u : X.K) ^ b) • UramOp W Ch u j P

def SramWC (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) : Submodule (Ow w) (ColV W Ch u j) :=
  SwC W Ch u j w ⊓ (ColRamV W Ch u j).restrictScalars (Ow w)

def BramWC (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) (P : {P // P ∈ Pr.vT u}) : Submodule (Ow w) (ColV W Ch u j) :=
  BvWC W Ch u j w P ⊓ (ColRamV W Ch u j).restrictScalars (Ow w)

def vdetTbU (u : Pr.Word) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.K)) (P : {P // P ∈ Pr.vT u}) (b : ℤ) : ℚ :=
  (vAdd w (LinearMap.det (TbUR W Ch u j P b)) : ℚ) / (eW w : ℚ)

end LemC

section T5

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

def bAtC [Nonempty X.Tau] (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (P : {P // P ∈ Pr.vT u}) : ℤ := W.bTop u (tauOfC w P.1)

def TUprodR [Nonempty X.Tau] (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : Module.End X.K (MramV W Ch u) :=
  ((VVTc W u w).toList.map fun P => TbUR W Ch u 0 P (bAtC W u w P)).prod

def idxNlamC (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : ℚ :=
  lidxUW w (MramL W Ch u) (NlamG W Ch u w)

def bndLemC (u : Pr.Word) (τ : X.Tau) : ℚ :=
  (finrank X.K (MfV W Ch u) : ℚ) * (sumShiftW (W.lamTrue u 0 τ) (W.bTop u τ) : ℚ) / (R.N 0 : ℚ) +
    ((R.N 0 : ℚ) - 1) * (finrank X.K (MramV W Ch u) : ℚ)

def idxBndC (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) : ℚ :=
  (R.m : ℚ) * ∑ τ ∈ topsP W u w, bndLemC W Ch u τ

def indexBoundPerDegree (u : Pr.Word) (Wt : X.Tau → ℕ) : ℝ :=
  (R.m : ℝ) * ∑ τ ∈ W.tops, ((W.aTop u τ : ℝ) / (R.k : ℝ) + 2 * (Wt τ : ℝ) + (R.k : ℝ) - 1)

def IsWtBound (u : Pr.Word) (Wt : X.Tau → ℕ) : Prop :=
  ∀ (τ : X.Tau) (i : Fin (R.N 0)), i.1 ≠ 0 → ((W.lamTrue u 0 τ).w i).natAbs ≤ Wt τ

def wtT {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) : ℝ := 2 * lW w * (eW w : ℝ)

def priceIC (u : Pr.Word) : ℝ :=
  (1 / (finrank X.K (MramV W Ch u) : ℝ)) *
    ∑ᶠ w : {w : HeightOneSpectrum (𝓞 X.K) // prW w = Pr.T u}, wtT w.1 * ((idxNlamC W Ch u w.1 : ℚ) : ℝ)

def WeightHalf (Pr : Primes X) : Prop :=
  ∀ u : Pr.Word, ∑ᶠ w : {w : HeightOneSpectrum (𝓞 X.K) // seenC Pr u w}, wtT w.1 = Real.log (Pr.T u)

end T5

section Col

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

abbrev KerArg (u : Pr.Word) : Type := ∀ j : ℕ, ColV W Ch u j →ₗ[X.K] ColV W Ch u (j + 1)

variable {W Ch}

def colArg {u : Pr.Word} (kk : KerArg W Ch u) (i : ℕ) : MfV W Ch u →ₗ[X.K] ColV W Ch u i :=
  Formalism.HermitianLattices.LocalLatticeBases.chainK X.K (fun j => ColV W Ch u j) kk i

def KernelFourierIntegralBound {u : Pr.Word} (kk : KerArg W Ch u) (w : HeightOneSpectrum (𝓞 X.K)) (e1 : ℕ) : Prop :=
  ∀ j, j < R.m → ∀ s ∈ SwC W Ch u j w, ((Pr.T u : X.K) ^ e1) • UprodC W Ch u (j + 1) w (kk j s) ∈ SwC W Ch u (j + 1) w

def KernelArgumentHypothesisScalar {u : Pr.Word} (kk : KerArg W Ch u) (c : ℕ → {P // P ∈ Pr.vT u} → X.Kˣ) : Prop :=
  ∀ j, j < R.m → ∀ P, (UOp W Ch u (j + 1) P).comp (kk j) = ((c j P : X.Kˣ) : X.K) • (kk j).comp (UOp W Ch u j P)

def cProdC (W : Wts X Pr.Word R) {u : Pr.Word} (c : ℕ → {P // P ∈ Pr.vT u} → X.Kˣ) (w : HeightOneSpectrum (𝓞 X.K)) (j : ℕ) : X.Kˣ :=
  ∏ P ∈ VVTc W u w, c j P

def ScalarIntegralAtPlace (W : Wts X Pr.Word R) {u : Pr.Word} (c : ℕ → {P // P ∈ Pr.vT u} → X.Kˣ) (w : HeightOneSpectrum (𝓞 X.K)) (ga : ℕ → ℕ) : Prop :=
  ∀ j, j < R.m → ∃ r : Ow w, algebraMap (Ow w) X.K r = ((cProdC W c w j)⁻¹ : X.Kˣ) * (Pr.T u : X.K) ^ ga j

def eColC (R : Ranks) (e1 : ℕ) (ga : ℕ → ℕ) : ℕ := R.m * e1 + ∑ j ∈ Finset.range R.m, (R.m - j) * ga j

end Col

end Formalism.L2.Col
