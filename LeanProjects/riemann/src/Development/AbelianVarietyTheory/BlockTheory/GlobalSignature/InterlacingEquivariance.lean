import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.CoefColLemmas
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant

open MvPolynomial NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

def brOne (K : Type) [Field K] {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) :
    MvPolynomial (Fin N × Fin N) K →ₗ[K] MvPolynomial (Fin n × Fin n) K :=
  (rename (Prod.snd : Unit × Fin n × Fin n → Fin n × Fin n)).toLinearMap ∘ₗ
    (VV K fun _ : Unit => sg).subtype ∘ₗ
      Br.brStdP (K := K) hN (fun _ : Unit => lam) (fun _ : Unit => sg) ∘ₗ
        (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N))).toLinearMap

theorem brOne_rename (K : Type) [Field K] {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n)
    (G : VV K fun _ : Unit => lam) :
    brOne K hN lam sg (rename Prod.snd (G : Pol K Unit N)) =
      rename Prod.snd ((Br.brStd hN (fun _ : Unit => lam) (fun _ : Unit => sg) G : VV K fun _ : Unit => sg) : Pol K Unit n) := by
  have h : rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N))
      (rename Prod.snd (G : Pol K Unit N)) = (G : Pol K Unit N) := by
    rw [rename_rename]
    exact rename_id_apply _
  simp only [brOne, Br.brStd, LinearMap.comp_apply, AlgHom.toLinearMap_apply, h, Submodule.subtype_apply]

theorem interlace_iff {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) :
    Br.Interlace hN lam sg ↔ Formalism.MainNotions.PrimeDegreeVariant.Interlace hN.symm lam sg := by
  refine forall_congr' fun i => ?_
  simp only [Br.aBr, Br.bBr, Br.iS, Br.iC]
  omega

def OnePlace : Prop :=
  ∀ (N n : ℕ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n),
    Br.Interlace hN lam sg → Br.SameShift lam sg →
      Formalism.MainNotions.PrimeDegreeVariant.IsBr hN.symm lam sg (brOne ℂ hN lam sg)

def Equivariance : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Br.Interlace hN (lam τ) (sg τ)) → Br.BrEquiv K hN lam sg

def Integrality : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n), Br.BrIntegral K hN lam sg

def Homogeneity : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Br.Interlace hN (lam τ) (sg τ)) → (∀ τ, Br.SameShift (lam τ) (sg τ)) →
    ∀ t : ι → Kˣ,
      Br.brStd hN lam sg ∘ₗ (rhoK lam fun τ => (Formalism.MainNotions.PrimeDegreeVariant.lastGL K N (t τ))⁻¹) = Br.brAt hN lam sg (fun τ => (t τ : K)) ∧
      Br.brAt hN lam sg (fun τ => (t τ : K)) =
        ((∏ τ, t τ ^ (-((∑ i, (lam τ).w i) - ∑ i, (sg τ).w i)) : Kˣ) : K) • Br.brStd hN lam sg

def Members : Prop :=
  ∀ (X : Fields) (Word : Type) (R : Ranks) (W : Wts X Word R), W.Ok → ∀ (u : Word) (τ : X.Tau),
    Br.Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) ∧ Br.SameShift (W.lamTrue u R.m τ) (W.sgTrue τ)

def Statement : Prop := OnePlace ∧ Equivariance ∧ Integrality ∧ Homogeneity ∧ Members

def Transposed : Prop :=
  ∀ (N n : ℕ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n),
    Br.Interlace hN lam sg → Br.SameShift lam sg →
      ∃ io, Formalism.MainNotions.PrimeDegreeVariant.IsIota hN.symm lam sg io ∧ Formalism.MainNotions.PrimeDegreeVariant.IsTranspose lam sg io (brOne ℂ hN lam sg)

def Tensor : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Br.Interlace hN (lam τ) (sg τ)) → (∀ τ, Br.SameShift (lam τ) (sg τ)) →
    ∀ (f : ι → MvPolynomial (Fin N × Fin N) K) (G : VV K lam), (∀ τ, f τ ∈ nablaSq K N (lam τ)) → (G : Pol K ι N) = ten f →
      ((Br.brStd hN lam sg G : VV K sg) : Pol K ι n) = ten fun τ => brOne K hN (lam τ) (sg τ) (f τ)

def BaseChange : Prop :=
  ∀ (K K' : Type) [Field K] [CharZero K] [Field K'] (φ : K →+* K') (N n : ℕ) (hN : N = n + 1)
    (lam : DomWeight N) (sg : DomWeight n), Br.Interlace hN lam sg → Br.SameShift lam sg →
    ∀ f ∈ nablaSq K N lam, brOne K' hN lam sg (map φ f) = map φ (brOne K hN lam sg f)

def iotaNormSq {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) : ℝ :=
  ((Formalism.MainNotions.PrimeDegreeVariant.cBr hN.symm lam sg : ℤ) : ℝ) ^ 2 *
    (normFock lam (Formalism.MainNotions.PrimeDegreeVariant.xi ℂ hN.symm lam sg) (Formalism.MainNotions.PrimeDegreeVariant.xi ℂ hN.symm lam sg)).re

def ExactNorm : Prop :=
  ∀ (N n : ℕ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n),
    Br.Interlace hN lam sg → Br.SameShift lam sg →
      (∀ a : ℂˣ, IsGreatest
        {r : ℝ | ∃ f ∈ delSq ℂ N lam,
          (normFock lam (sqAct ℂ N lam (Formalism.MainNotions.PrimeDegreeVariant.lastGL ℂ N a) f) (sqAct ℂ N lam (Formalism.MainNotions.PrimeDegreeVariant.lastGL ℂ N a) f)).re = 1 ∧
          r = (normFock sg (brOne ℂ hN lam sg f) (brOne ℂ hN lam sg f)).re}
        ((‖(a : ℂ)‖ ^ 2) ^ (-Br.nBr lam sg) * iotaNormSq hN lam sg)) ∧
      iotaNormSq hN lam sg ≤ Formalism.MainNotions.PrimeDegreeVariant.brBd hN.symm lam sg ^ 2 ∧
      (Br.d0 hN lam sg = 0 → iotaNormSq hN lam sg = 1)

def StatementSharp : Prop := Statement ∧ Transposed ∧ Tensor ∧ BaseChange ∧ ExactNorm

theorem brAt_eq {K : Type} [Field K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (t : ι → Kˣ) :
    Br.brAt hN lam sg (fun τ => (t τ : K)) =
      ((∏ τ, t τ ^ (-((∑ i, (lam τ).w i) - ∑ i, (sg τ).w i)) : Kˣ) : K) • Br.brStd hN lam sg := by
  simp [Br.brAt, Br.nBr]

theorem members_sameShift {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R) (hW : W.Ok) (u : Word) (τ : X.Tau) :
    Br.SameShift (W.lamTrue u R.m τ) (W.sgTrue τ) :=
  (lamTrue_sgTrue_detShift W hW u τ).symm

example : ∃ (lam : DomWeight 3) (sg : DomWeight 2),
    Br.Interlace (by rfl : 3 = 2 + 1) lam sg ∧ Br.SameShift lam sg ∧ Br.d0 (by rfl : 3 = 2 + 1) lam sg = 1 := by
  refine ⟨⟨![2, 0, -1], by decide⟩, ⟨![1, -1], by decide⟩, ?_, ?_, ?_⟩
  · unfold Br.Interlace; decide
  · unfold Br.SameShift; decide
  · decide

end GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance
