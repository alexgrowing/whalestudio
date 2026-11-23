import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesX

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

def SiegelWeilAniso : Prop := SWAniso ∧ SWAnisoX

variable (σ Y) in

def IsFrame2 (b : GL (Fin n ⊕ Fin n) E) : Prop :=
  (∃ ε : ℤˣ, b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) ∧
    ∃ t : GL (Fin n) E, b.1.toCols₁ = diagCols (Fin n) * t.1

variable (F E) in

def intHat : AddSubgroup (AE F E) :=
  AddSubgroup.closure {z | ∃ a : AF F, evI F a = 0 ∧ (∀ v, evFin F v a ∈ v.adicCompletionIntegers F) ∧
    ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}

variable (F) in

def finOne : AF F := LinearMap.inr F (Ainf F) (Af F) 1

def inFrame (b : GL (Fin n ⊕ Fin n) E) (x : G2 σ Y) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) :=
  incM F (b⁻¹).1 * mat2 x * incM F b.1

def IsStdK (B : Base F E) (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) : Prop :=
  ∀ k, k ∈ K ↔ (∀ w, (inFrame b k).map (piInf (B.emb w)) * ((inFrame b k).map (piInf (B.emb w)))ᴴ = 1) ∧
    ∀ k' ∈ ({k, k⁻¹} : Set (G2 σ Y)), ∀ i j, finOne F • inFrame b k' i j ∈ intHat F E

variable (σ Y) in

def modFun : Submodule ℂ (G2 σ Y → ℂ) :=
  Submodule.span ℂ {f | Continuous f ∧ ∃ N : ℕ, ∀ x, ‖f x‖ ≤ (ht2 x : ℝ) ^ N}

def IsGrowForm (μ : modFun σ Y →ₗ[ℂ] ℂ) : Prop :=
  ∀ N : ℕ, ∃ C : ℝ, ∀ f : modFun σ Y, (∀ x, ‖f.1 x‖ ≤ (ht2 x : ℝ) ^ N) → ‖μ f‖ ≤ C

def EisBL : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ χ : Chr F E, IsHecke F E χ → ∀ c : ℕ, ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ c →
    ∀ b K a, IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ s₁ f, IsSec K χ s₁ f →
      ∃ Ê : ℂ → G2 σ Y → ℂ, (∃ t : ℝ, (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) ∧
          ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re}) ∧
        ∀ s₀, ∃ (k : ℕ) (U : Set ℂ) (H : ℂ → modFun σ Y), U ∈ 𝓝 s₀ ∧ (∀ s ∈ U, s ≠ s₀ → ∀ x, (H s).1 x = (s - s₀) ^ k * Ê s x) ∧
          ∀ μ, IsGrowForm μ → DifferentiableOn ℂ (fun s => μ (H s)) U

def FrameConj : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) →
    ∀ K, IsStab2 (σ := σ) (Y := Y) B K → ∃ b K₀ p t, IsFrame2 σ Y b ∧ IsStdK B b K₀ ∧ IsPar p t ∧ ∀ k, k ∈ K ↔ p⁻¹ * k * p ∈ K₀

end GlobalTheory.ThK.Dbl

end
