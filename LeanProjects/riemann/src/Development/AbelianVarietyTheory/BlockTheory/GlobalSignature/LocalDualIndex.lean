import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.HermitianLattices.StatementMass

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Characters

variable (F : Type) [Field F] [NumberField F]

theorem psiV_zero (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) : psiV F ψ v 0 = 1 := by
  classical
  have h : pairA F 0 (singleV F v 0) = 0 := by
    have : singleV F v 0 = 0 := RestrictedProduct.single_zero _ v
    rw [this]; rfl
  rw [psiV, h, AddChar.map_zero_eq_one]

theorem psiV_add (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (s t : Fv F v) :
    psiV F ψ v (s + t) = psiV F ψ v s * psiV F ψ v t := by
  classical
  have h : pairA F 0 (singleV F v (s + t)) =
      pairA F 0 (singleV F v s) + pairA F 0 (singleV F v t) := by
    have : singleV F v (s + t) = singleV F v s + singleV F v t :=
      RestrictedProduct.single_add _ v s t
    rw [this]
    exact Prod.ext (add_zero (0 : Ainf F)).symm rfl
  rw [psiV, h, AddChar.map_add_eq_mul]; rfl

def intV (v : HeightOneSpectrum (𝓞 F)) : AddSubgroup (Fv F v) :=
  (v.adicCompletionIntegers F).toSubring.toAddSubgroup

def dualV (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) : AddSubgroup (Fv F v) where
  carrier := {t | ∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (t * s) = 1}
  zero_mem' := fun s _ => by rw [zero_mul, psiV_zero]
  add_mem' := fun {a b} ha hb s hs => by rw [add_mul, psiV_add, ha s hs, hb s hs, one_mul]
  neg_mem' := fun {a} ha s hs => by
    have := ha (-s) (neg_mem hs)
    rwa [mul_neg, ← neg_mul] at this

def dualIndex (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  ((intV F v).relIndex (dualV F ψ v) : ℝ) / ((dualV F ψ v).relIndex (intV F v) : ℝ)

def traceInf (x : Ainf F) : ℝ :=
  ∑ w : InfinitePlace F, (w.mult : ℝ) * (InfinitePlace.Completion.extensionEmbedding w (x w)).re

def stdInf (x : Ainf F) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * (traceInf F x : ℂ))

def IsStdChar (ψ : AddChar (AF F) ℂ) : Prop :=
  IsCharAF F ψ ∧ ∀ x : Ainf F, psiInf F ψ x = stdInf F x

def IsScalingInf (ψ : AddChar (AF F) ℂ) (a : F) : Prop :=
  ∀ x : Ainf F, psiInf F ψ x = stdInf F (algebraMap F (Ainf F) a * x)

theorem isScalingInf_of_eq {ψ₀ ψ : AddChar (AF F) ℂ} (h₀ : IsStdChar F ψ₀) {a : F}
    (h : ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x)) : IsScalingInf F ψ a := by
  intro x
  rw [← h₀.2, psiInf, psiInf, h]
  congr 1
  exact Prod.ext rfl (mul_zero _)

theorem IsStdChar.isScalingInf_one {ψ₀ : AddChar (AF F) ℂ} (h₀ : IsStdChar F ψ₀) :
    IsScalingInf F ψ₀ 1 :=
  isScalingInf_of_eq F h₀ fun x => by rw [map_one, one_mul]

def absInf (a : F) : ℝ := ∏ w : InfinitePlace F, w a ^ w.mult

def differentV (v : HeightOneSpectrum (𝓞 F)) : Ideal (v.adicCompletionIntegers F) :=
  (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (v.adicCompletionIntegers F))

def normDifferentV (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  Nat.card (v.adicCompletionIntegers F ⧸ differentV F v)

def resCard (v : HeightOneSpectrum (𝓞 F)) : ℕ := Ideal.absNorm v.asIdeal

def absDiscr : ℝ := |(discr F : ℝ)|

end Characters

section Densities

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]

open Classical in

def etaV (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  if IsField (Fv F v ⊗[F] E) then -1 else 1

def eulerInv (M : ℕ) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  1 - etaV F E v ^ M * (resCard F v : ℝ) ^ (-(M : ℤ))

def localDensity (ψ : AddChar (AF F) ℂ) (M : ℕ) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  dualIndex F ψ v ^ ((1 : ℝ) / 2 - M) * eulerInv F E M v

end Densities

def DensityProduct : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E →
    (∃! ψ₀ : AddChar (AF F) ℂ, IsStdChar F ψ₀) ∧
    (∀ ψ₀, IsStdChar F ψ₀ → ∀ v : HeightOneSpectrum (𝓞 F),
      (∀ t : Fv F v, t ∈ dualV F ψ₀ v ↔
        ∀ d ∈ differentV F v, t * (d : Fv F v) ∈ v.adicCompletionIntegers F) ∧
      dualIndex F ψ₀ v = normDifferentV F v) ∧
    ((Function.mulSupport (normDifferentV F)).Finite ∧
      ((∏ᶠ v, normDifferentV F v : ℕ) : ℝ) = absDiscr F ∧
      absDiscr F = (2 * Formalism.HermitianLatticesTheory.vInv E) ^ Formalism.HermitianLatticesTheory.fDeg E) ∧
    (∀ ψ₀, IsStdChar F ψ₀ → ∀ ψ, IsCharAF F ψ →
      ∃ a : F, a ≠ 0 ∧ ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x)) ∧
    (∀ M : ℕ, 2 ≤ M → 0 < Formalism.HermitianLatticesTheory.lValEta E M ∧
      HasProd (fun v => (eulerInv F E M v)⁻¹) (Formalism.HermitianLatticesTheory.lValEta E M)) ∧
    (∀ ψ, IsCharAF F ψ →
      (∀ v, (intV F v).relIndex (dualV F ψ v) ≠ 0 ∧ (dualV F ψ v).relIndex (intV F v) ≠ 0) ∧
      ∀ a : F, a ≠ 0 → IsScalingInf F ψ a → ∀ M : ℕ, 2 ≤ M →
        Summable (fun v => |localDensity F E ψ M v - 1|) ∧
        ∃ P : ℝ, 0 < P ∧ HasProd (localDensity F E ψ M) P ∧
          absInf F a ^ ((M : ℝ) - 1 / 2) * P =
            absDiscr F ^ ((1 : ℝ) / 2 - M) / Formalism.HermitianLatticesTheory.lValEta E M)

end GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
