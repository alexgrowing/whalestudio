import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.InfB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def coneFun {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ X W) (om : Rep σ X W)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁)) (μ : Measure (idelesAt E (evI F)))
    (u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)) (ν : Chr F E) (z : ℕ)
    (l : SInf F (Fin n₁ × Fin d₁) →L[ℂ] ℂ) (f : SInf F (Fin n × Fin d)) (g : UA σ X.J) : ℂ :=
  ∫ y, l (coneInfInt B M om ei u ν z f g y.1) ∂μ

theorem locOpInf_mul {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {om : Rep σ X W}
    (hex : ∀ g ∈ UAt σ X (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (g, 1)) f f₁)
    (hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d))
    {g h : UA σ X.J} (hg : g ∈ UAt σ X (evI F)) (hh : h ∈ UAt σ X (evI F)) (f : SInf F (Fin n × Fin d)) :
    locOpInf (om (g * h, 1)) f = locOpInf (om (g, 1)) (locOpInf (om (h, 1)) f) := by
  apply locOpInf_eq
  intro r hr
  have h1 := acts_locOpInf (hex h hh f) r hr
  have hr' : Rest (evI F) (locOpInf (om (h, 1)) f) r := ⟨hr.1, by rw [← h1]; exact hpres _ _ hr.2⟩
  have h2 := acts_locOpInf (hex g hg _) r hr'
  rw [show ((g * h, (1 : UA σ W.J)) : UA σ X.J × UA σ W.J) = (g, 1) * (h, 1) by simp, map_mul,
    Module.End.mul_apply, h1, h2]

theorem fac_one (χ : Chr F E) (z : ℝ) : fac χ z 1 = 1 := by
  simp [fac]

end GlobalTheory.ThK.InfB

end
