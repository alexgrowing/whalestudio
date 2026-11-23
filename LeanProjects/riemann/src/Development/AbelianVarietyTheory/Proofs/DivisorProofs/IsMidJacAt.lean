import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDetProdConstAt

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.ThK.DetProd

namespace GlobalTheory.ThK.MidJac

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def e3 (l n d : ℕ) (h : l + n ≤ d) : (Σ i : Fin 3, Fin (![l, n, d - l - n] i)) ≃ Fin d :=
  finSigmaFinEquiv.trans (finCongr (by simp [Fin.sum_univ_three]; omega))

def e2 (a a' : ℕ) : (Σ i : Fin 2, Fin (![a, a'] i)) ≃ Fin (a + a') :=
  finSigmaFinEquiv.trans (finCongr (by simp [Fin.sum_univ_two]))

def midIncl (l n c : ℕ) : GL (Fin n) k →* Levi k (fun i : Fin 3 => Fin (![l, n, c] i)) :=
  MonoidHom.mulSingle (fun i : Fin 3 => GL (Fin (![l, n, c] i)) k) 1

def midJac {V : Type} [AddCommGroup V] [Module ℂ V] (l n d : ℕ) (h : l + n ≤ d) (π : Representation ℂ (GL (Fin d) k) V) :
    Representation ℂ (GL (Fin n) k) (Jacquet π (unipRad k (e3 l n d h))) :=
  (jac (e3 l n d h) π).comp (midIncl l n (d - l - n))

def detInd (a a' : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) :
    Representation ℂ (GL (Fin (a + a')) k) (IndSp (e2 a a') (ofChar (twoDet a a' χ₁ χ₂))) :=
  parInd (e2 a a') (ofChar (twoDet a a' χ₁ χ₂))

section Place

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E]

def absPowAt (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (s : ℂ) : (w.adicCompletion E)ˣ →* ℂˣ :=
  absPow _ s

def IsMidJacAt (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) {n : ℕ} (a a' l : ℕ) (h : l + n ≤ a + a')
    (χ₁ χ₂ : (w.adicCompletion E)ˣ →* ℂˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) : Prop :=
  IsSubquotient π (midJac l n (a + a') h (detInd a a' χ₁ χ₂))

end Place

end GlobalTheory.ThK.MidJac
