import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.DblSchrF

def dblR {R : Type} [CommRing R] {n : ℕ} (J : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  (dbl J).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_dblR {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    incM F (dblR J) = (dbl (incM F J)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  ext i j
  rcases h1 : finSumFinEquiv.symm i with i' | i' <;> rcases h2 : finSumFinEquiv.symm j with j' | j' <;>
    simp [dblR, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.WeilM.dbl, h1, h2]

def ddrF (σ : E →ₐ[F] E) {nS nT : ℕ} {ξ : AF F ⊗[F] E} {JA : Matrix (Fin nT) (Fin nT) E}
    {JB : Matrix (Fin nS) (Fin nS) E} {κ : Type} [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ) :
    Darboux (symp (cA σ) ξ (incM F JA) (incM F (dblR JB))) (κ ⊕ κ) :=
  GlobalTheory.DblSchr.reD _ finSumFinEquiv.symm (incM_dblR JB) (GlobalTheory.DblSchr.dblD _ co)

def omdOfF (σ : E →ₐ[F] E) {nS nT : ℕ} {JA : Matrix (Fin nT) (Fin nT) E} {JB : Matrix (Fin nS) (Fin nS) E}
    {X : Type} [AddCommGroup X] [Module ℂ X]
    (omd₀ : UG (cA σ) (incM F JA) × UG (cA σ) (incM F (dblR JB)) →* Module.End ℂ X) :
    UG (cA σ) (dbl (incM F JB)) →* Module.End ℂ X :=
  omd₀.comp ((MonoidHom.inr _ _).comp (GlobalTheory.DblSchr.reG _ finSumFinEquiv.symm (incM_dblR JB)))

end GlobalTheory.DblSchrF

end
