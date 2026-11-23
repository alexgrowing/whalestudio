import Formalism.LocalToGlobal.Columns.FirstKernelEqLastComponentKernel
import Formalism.LocalToGlobal.Columns.RecChainUnfOne

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

def zOfRow0 (σ₀ : X.K →+* ℂ) (hM : (rowGSD W ΛM).Ok) (F : (rowGSD W ΛM).EqFun) : Fin ((rowGSD W ΛM).hDim hM) → ℂ :=
  fun a => σ₀ (((rowGSD W ΛM).hB hM).repr F a)

end Gen

section Cast

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

theorem levFam_eq_cast {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (e : SG = SG')
    (A : LevFam E K n SG) (B : LevFam E K n SG') (h : ∀ (w : SG') (hw : w.1 ∈ SG), B w = A ⟨w.1, hw⟩) : B = e ▸ A := by
  subst e
  funext w
  exact h w w.2

def decoCast {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (e : SG = SG') (d : DecoSet E n ∅ SG) :
    DecoSet E n ∅ SG' := e ▸ d

variable {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (e : Pr.vGs = SG') (A : LevFam X.E X.K (R.N R.m - 1) Pr.vGs)
  (Λ' : LevFam X.E X.K (R.N R.m - 1) SG')

def rowCast (hΛ : Λ' = e ▸ A) (F : (formGSD (rowVal W SG') Λ').EqFun) : (rowGSD W A).EqFun := by
  subst hΛ
  subst e
  exact F

end Cast

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (P : LevFam X.E X.K R.r Pr.vGs)

theorem rowTy_inv_cast : (rowTy Ch sel mu P).inv = rcol_rowSG_eq sel mu hQ ▸ (rowTyG Ch P).inv := by
  refine levFam_eq_cast (rcol_rowSG_eq sel mu hQ) _ _ fun w hw => ?_
  first
  | (simp only [LevFam.inv, rowTy, LevFam.glue, dif_pos hw]; done)
  | (unfold LevFam.inv rowTy LevFam.glue; rw [dif_pos hw])
  | (simp [LevFam.inv, rowTy, LevFam.glue, hw])

def zOfRow (σ₀ : X.K →+* ℂ) (hM : (rowGSD W (rowTyG Ch P).inv).Ok) (F : MtildeV W Ch sel mu P) : Fin ((rowGSD W (rowTyG Ch P).inv).hDim hM) → ℂ :=
  zOfRow0 W (rowTyG Ch P).inv σ₀ hM (rowCast W (rcol_rowSG_eq sel mu hQ) (rowTyG Ch P).inv _ (rowTy_inv_cast Ch sel mu hQ P) F)

end Main

end Formalism.L2.Col
