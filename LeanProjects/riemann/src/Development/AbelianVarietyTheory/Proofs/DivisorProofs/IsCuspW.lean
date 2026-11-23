import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace GlobalTheory.ThKLiftCusp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def kern {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W)
    (Ψ Φ : (Fin n × Fin d → AF F) → ℂ) (h h' : UA σ W.J) : ℂ :=
  ∫ g in M.dom, theta om Ψ g h * (starRingEnd ℂ) (theta om Φ g h') ∂M.μ

variable (σ) in

def formA {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (x y : Fin d → AE F E) : AE F E :=
  x ⬝ᵥ incM F J *ᵥ fun i => cA σ (y i)

variable (σ) in

def unipSp {d j : ℕ} (W : Spc F E d) (Y : Matrix (Fin d) (Fin j) E) : Subgroup (UA σ W.J) :=
  Subgroup.closure {u | mat u * incM F Y = incM F Y ∧
    (∀ z, (∀ k, formA σ W.J z (incV F fun i => Y i k) = 0) → ∃ a, mat u *ᵥ z = z + incM F Y *ᵥ a) ∧
    ∀ z k, formA σ W.J (mat u *ᵥ z - z) (incV F fun i => Y i k) = 0}

def IsCuspW {d : ℕ} (W : Spc F E d) (f : UA σ W.J → ℂ) : Prop :=
  ∀ (j : ℕ) (Y : Matrix (Fin d) (Fin j) E), 1 ≤ j → Function.Injective Y.mulVec →
    (∀ k l, form σ W.J (fun i => Y i k) (fun i => Y i l) = 0) →
    ∀ (μ : Measure (unipSp σ W Y)) (𝓕 : Set (unipSp σ W Y)), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ W.J).subgroupOf (unipSp σ W Y)) 𝓕 μ → μ 𝓕 = 1 →
      ∀ h, ∫ u in 𝓕, f (u.1 * h) ∂μ = 0

end GlobalTheory.ThKLiftCusp

end
