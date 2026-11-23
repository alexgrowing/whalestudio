import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def DomU {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W)
    (𝓕 : Set ((Fin n × Fin d → Af F) → ℂ)) : Prop :=
  ∃ k : ℕ, ∀ φ ∈ 𝓕, ∃ (p : Seminorm ℂ (SInf F (Fin n × Fin d))) (G : UA σ X.J → ℝ≥0∞), Continuous p ∧ Measurable G ∧
    ∫⁻ g in M.dom, G g ∂M.μ < ⊤ ∧ ∀ (f : SInf F (Fin n × Fin d)) g h,
      ‖theta om (pureA F f φ) g h‖ₑ ≤ ENNReal.ofReal (p f * (ht h : ℝ) ^ k) * G g

def DomWeilU : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → (d + 2 * min r s < 2 * n ∨ min r s = 0) → DomU M om {φ | φ ∈ SB _}

def SoSemiU : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → ∀ N : ℕ, ∃ k : ℕ, ∀ φ ∈ soFin B M, ∃ p : Seminorm ℂ (SInf F (Fin n × Fin d)), Continuous p ∧
    ∀ (f : SInf F (Fin n × Fin d)) g h, ‖theta om (pureA F f φ) g h‖ * (qht g : ℝ) ^ N ≤ p f * (ht h : ℝ) ^ k

def DomSoU : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) χX χW om r s r' s', IsPair B M χX χW om r s r' s' → DomU M om (soFin B M)

theorem domWeil_of_U (h : DomWeilU) : DomWeil := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP hd φ hφ
  obtain ⟨k, hk⟩ := h F E σ B n d X W M χX χW om r s r' s' hP hd
  obtain ⟨p, G, hp, hG, hint, hb⟩ := hk φ hφ
  exact ⟨p, k, G, hp, hG, hint, hb⟩

theorem soSemi_of_U (h : SoSemiU) : SoSemi := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP φ hφ N
  obtain ⟨k, hk⟩ := h F E σ B n d X W M χX χW om r s r' s' hP N
  obtain ⟨p, hp, hb⟩ := hk φ hφ
  exact ⟨p, k, hp, hb⟩

end PositivityTheory.ThKEst

end
