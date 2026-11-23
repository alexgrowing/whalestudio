import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm

noncomputable section

namespace GlobalTheory.ThK.GLTwo

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (σ : E →ₐ[F] E) in

def IsHypPlane {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) : Prop :=
  n = n₁ + 2 ∧ form σ Y.J H.x H.x = 0 ∧ form σ Y.J H.y H.y = 0 ∧ form σ Y.J H.x H.y = 1 ∧
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) ∧ H.ιᵀ * Y.J * H.ι.map σ = Y₁.J

theorem IsAdapted.isHypPlane {σ : E →ₐ[F] E} {B : Base F E} {n n₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n}
    {Y₁ : Spc F E n₁} {i₀ i₁ : ℕ} (h : H.IsAdapted σ B Y Y₁ i₀ i₁) : IsHypPlane σ H Y Y₁ :=
  ⟨h.rank, h.xx, h.yy, h.xy, h.orth, h.gram⟩

theorem IsIsoPlane.isHypPlane {σ : E →ₐ[F] E} {B : Base F E} {n n₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n}
    {Y₁ : Spc F E n₁} (h : GlobalTheory.ThK.DescB.IsIsoPlane σ B H Y Y₁) : IsHypPlane σ H Y Y₁ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def IsDiagAt (X Y : Matrix (Fin n) (Fin r) E) (i : Fin r) (t : (AE F E)ˣ) (g : GAd σ J) : Prop :=
  (matHom _ σ J g).1 *ᵥ (fun k => adMat F X k i) = t.1 • (fun k => adMat F X k i) ∧
    (matHom _ σ J g).1 *ᵥ (fun k => adMat F Y k i) = cA σ (t⁻¹).1 • (fun k => adMat F Y k i) ∧
    ∀ z ∈ colPerp σ J X {i} ⊓ colPerp σ J Y {i}, (matHom _ σ J g).1 *ᵥ z = z

def WittFrameGLTwoDecomposition : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (h1 : 1 < r), IsWittFrame σ J X Y →
    ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K → ∀ φ : GAd σ J → ℂ, IsAut σ J K φ →
    (∀ S : Finset (Fin r), ¬ (∀ k ∈ S, ∀ i ≤ k, i ∈ S) → IsCuspComp σ J X Y S K φ 0) →
    ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (χa χb : Chr F E) (ma mb : InfinitePlace F → ℤ),
      HasExp τ χa ma → HasExp τ χb mb → (∃ w, ma w ≠ mb w) →
    ∀ za0 za1 zb1 : ℝ, za0 < zb1 + 1 →
    ∀ c0 : GAd σ J → ℂ, IsConstAlong σ J X {⟨0, by omega⟩} φ c0 →
      (∀ t g, IsDiagAt σ J X Y ⟨0, by omega⟩ t g → ∀ x,
        c0 (g * x) = (χa t : ℂ) * (((absE F E t : ℝ) ^ za0 : ℝ) : ℂ) * c0 x) →
    ∀ c01 : GAd σ J → ℂ, IsConstAlong σ J X {⟨0, by omega⟩, ⟨1, h1⟩} φ c01 →
    ∀ (x : GAd σ J) (A B : ℂ), (∀ t g, IsDiagAt σ J X Y ⟨1, h1⟩ t g →
        c01 (g * x) = A * ((χa t : ℂ) * (((absE F E t : ℝ) ^ za1 : ℝ) : ℂ)) +
          B * ((χb t : ℂ) * (((absE F E t : ℝ) ^ zb1 : ℝ) : ℂ))) → B = 0

end GlobalTheory.ThK.GLTwo

end
