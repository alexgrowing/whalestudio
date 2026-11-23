import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant

open NumberField MvPolynomial

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OnePlaceBranching

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

def brOne (K : Type) [Field K] {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) :
    MvPolynomial (Fin N × Fin N) K →ₗ[K] MvPolynomial (Fin n × Fin n) K :=
  (rename (R := K) (Prod.snd : Unit × Fin n × Fin n → Fin n × Fin n)).toLinearMap ∘ₗ
    (VV K fun _ : Unit => sg).subtype ∘ₗ
      Br.brStdP (K := K) hN (fun _ : Unit => lam) (fun _ : Unit => sg) ∘ₗ
        (rename (R := K) (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N))).toLinearMap

def OnePlaceIsBr : Prop :=
  ∀ (N n : ℕ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n),
    Br.Interlace hN lam sg → Br.SameShift lam sg →
    Formalism.MainNotions.PrimeDegreeVariant.IsBr hN.symm lam sg (brOne ℂ hN lam sg)

def OnePlaceTranspose : Prop :=
  ∀ (N n : ℕ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n),
    Br.Interlace hN lam sg → Br.SameShift lam sg →
    ∃ io : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ,
      Formalism.MainNotions.PrimeDegreeVariant.IsIota hN.symm lam sg io ∧ Formalism.MainNotions.PrimeDegreeVariant.IsTranspose lam sg io (brOne ℂ hN lam sg)

def IsTensor : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Br.Interlace hN (lam τ) (sg τ)) → (∀ τ, Br.SameShift (lam τ) (sg τ)) →
    ∀ (f : ι → MvPolynomial (Fin N × Fin N) K), (∀ τ, f τ ∈ nablaSq K N (lam τ)) →
      ∀ G : VV K lam, (G : Pol K ι N) = ten f →
        ((Br.brStd hN lam sg G : VV K sg) : Pol K ι n) = ten fun τ => brOne K hN (lam τ) (sg τ) (f τ)

def EquivNe : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Br.Interlace hN (lam τ) (sg τ)) →
    Br.BrEquiv K hN lam sg ∧ ((∀ τ, Br.SameShift (lam τ) (sg τ)) → Br.brStd (K := K) hN lam sg ≠ 0)

def Integral : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n), Br.BrIntegral K hN lam sg

def Homogeneous : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Br.Interlace hN (lam τ) (sg τ)) → (∀ τ, Br.SameShift (lam τ) (sg τ)) →
    ∀ (t : ι → Kˣ) (G : VV K lam),
      Br.brAt hN lam sg (fun τ => (t τ : K)) G =
        Br.brStd hN lam sg (rhoK lam (fun τ => Formalism.MainNotions.PrimeDegreeVariant.lastGL K N (t τ))⁻¹ G) ∧
      Br.brAt hN lam sg (fun τ => (t τ : K)) G =
        (∏ τ, (t τ : K) ^ (-((∑ i, (lam τ).w i) - ∑ i, (sg τ).w i))) • Br.brStd hN lam sg G

def MemberWeights : Prop :=
  ∀ (X : Fields) (Word : Type) (R : Ranks) (W : Wts X Word R), W.Ok → ∀ (u : Word) (τ : X.Tau),
    Br.Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) ∧
    Br.SameShift (W.lamTrue u R.m τ) (W.sgTrue τ)

def Statement : Prop :=
  OnePlaceIsBr ∧ OnePlaceTranspose ∧ IsTensor ∧ EquivNe ∧ Integral ∧ Homogeneous ∧ MemberWeights

theorem interlace_iff {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) :
    Br.Interlace hN lam sg ↔ Formalism.MainNotions.PrimeDegreeVariant.Interlace hN.symm lam sg := by
  refine forall_congr' fun i => ?_
  simp only [Br.aBr, Br.bBr, Br.iS, Br.iC, sub_nonneg]
  exact and_comm

def lamEx : DomWeight 3 := ⟨![3, 1, 1], by decide⟩

def sgEx : DomWeight 2 := ⟨![2, 1], by decide⟩

example : Br.Interlace (N := 3) (n := 2) rfl lamEx sgEx ∧ Br.SameShift lamEx sgEx ∧
    Br.d0 (N := 3) (n := 2) rfl lamEx sgEx = 1 ∧ lamEx.detShift = 1 := by
  refine ⟨?_, rfl, ?_, rfl⟩
  · intro i
    fin_cases i <;> simp [Br.aBr, Br.bBr, Br.iS, Br.iC, lamEx, sgEx]
  · simp [Br.d0, Br.aBr, Br.iS, lamEx, sgEx, Fin.sum_univ_two]

end GlobalTheory.IndefiniteRowSideFullHecke.OnePlaceBranching
