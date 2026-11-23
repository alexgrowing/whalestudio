import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal

namespace GlobalTheory.TamSU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {M : ℕ}

def lieInt (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (Λ : Submodule (𝓞 E) (Fin M → E)) :
    AddSubgroup (Matrix (Fin M) (Fin M) E) where
  carrier := {X | X.trace = 0 ∧ (X.map σ)ᵀ * J + J * X = 0 ∧ ∀ x ∈ Λ, X *ᵥ x ∈ Λ}
  zero_mem' := ⟨by simp, by simp, by simp⟩
  add_mem' {X Y} hX hY := by
    refine ⟨by rw [trace_add, hX.1, hY.1, add_zero], ?_, fun x hx => ?_⟩
    · have e : (X + Y).map σ = X.map σ + Y.map σ := by ext; simp
      rw [e, transpose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX.2.1, hY.2.1, add_zero]
    · rw [add_mulVec]; exact Λ.add_mem (hX.2.2 x hx) (hY.2.2 x hx)
  neg_mem' {X} hX := by
    refine ⟨by rw [trace_neg, hX.1, neg_zero], ?_, fun x hx => ?_⟩
    · have e : (-X).map σ = -X.map σ := by ext; simp
      rw [e, transpose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hX.2.1, neg_zero]
    · rw [neg_mulVec]; exact Λ.neg_mem (hX.2.2 x hx)

def stabSet (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (Λ : Submodule (𝓞 E) (Fin M → E)) :
    Set (GlobalTheory.Published.SUAdelic σ J) :=
  {h | GlobalTheory.Mem.Vol.StabHat F (Λ : Set (Fin M → E)) (finMat σ J h.1)}

def locCount (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (Λ : Submodule (𝓞 E) (Fin M → E))
    (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) : ℕ :=
  Nat.card (Quot fun a b : stabSet σ J Λ => ∀ y ∈ latHat F E (Λ : Set (Fin M → E)),
    (finMat σ J a.1.1 - finMat σ J b.1.1) *ᵥ y ∈
      latHat F E ((((v.asIdeal ^ k).map (algebraMap (𝓞 F) (𝓞 E))) • Λ : Submodule (𝓞 E) (Fin M → E)) : Set (Fin M → E)))

def locVol (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (Λ : Submodule (𝓞 E) (Fin M → E))
    (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  limUnder atTop fun k : ℕ => (locCount σ J Λ v k : ℝ) / (Ideal.absNorm v.asIdeal : ℝ) ^ (k * (M ^ 2 - 1))

def IsTamagawa (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (Λ : Submodule (𝓞 E) (Fin M → E)) (Ψ : Finset (E →+* ℂ))
    (θ : Ψ → (Ainf F ⊗[F] E →+* ℂ)) (e : Fin (M ^ 2 - 1) → Matrix (Fin M) (Fin M) E)
    (μ : Measure (GlobalTheory.Published.SUAdelic σ J)) : Prop :=
  μ.IsHaarMeasure ∧
    Tendsto (fun ε : ℝ => μ {h | h ∈ stabSet σ J Λ ∧
        ∀ ρ a b, ‖infMat σ J (θ ρ) h.1 a b - (1 : Matrix (Fin M) (Fin M) ℂ) a b‖ < ε} /
        GlobalTheory.SUVol.formLie Ψ e (GlobalTheory.SUVol.tanBall Ψ M ε)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (|(discr F : ℝ)| ^ (-((M : ℝ) ^ 2 - 1) / 2) *
        ((Submodule.span (𝓞 F) (Set.range e)).toAddSubgroup.relIndex (lieInt σ J Λ) : ℝ) * ∏' v, locVol σ J Λ v)))

end GlobalTheory.TamSU
