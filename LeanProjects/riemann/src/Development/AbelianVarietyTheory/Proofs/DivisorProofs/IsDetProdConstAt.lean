import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.ThK.DetProd

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def twoDet (x x' : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) : Levi k (fun a : Fin 2 => Fin (![x, x'] a)) →* ℂˣ :=
  (detChar _ χ₁).comp (Pi.evalMonoidHom (fun a : Fin 2 => GL (Fin (![x, x'] a)) k) 0) *
    (detChar _ χ₂).comp (Pi.evalMonoidHom (fun a : Fin 2 => GL (Fin (![x, x'] a)) k) 1)

def IsDetProdConst {n : ℕ} (x x' : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) : Prop :=
  ∃ e : (Σ a : Fin 2, Fin (![x, x'] a)) ≃ Fin n, IsSubquotient π (parInd e (ofChar (twoDet x x' χ₁ χ₂)))

def RatioGap (χ₁ χ₂ : kˣ →* ℂˣ) : Prop :=
  ∃ c : ℝ, 1 < |c| ∧ ∀ y : kˣ, ‖((χ₁ y : ℂˣ) : ℂ) / ((χ₂ y : ℂˣ) : ℂ)‖ = nabs k y ^ c

end Local

section Place

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E]

def IsUnramAt (w : HeightOneSpectrum (𝓞 E)) (χ : (w.adicCompletion E)ˣ →* ℂˣ) : Prop := IsUnram χ

def IsDetProdConstAt (w : HeightOneSpectrum (𝓞 E)) {n : ℕ} (x x' : ℕ) (χ₁ χ₂ : (w.adicCompletion E)ˣ →* ℂˣ) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) : Prop :=
  IsDetProdConst x x' χ₁ χ₂ π

def RatioGapAt (w : HeightOneSpectrum (𝓞 E)) (χ₁ χ₂ : (w.adicCompletion E)ˣ →* ℂˣ) : Prop := RatioGap χ₁ χ₂

end Place

end GlobalTheory.ThK.DetProd
