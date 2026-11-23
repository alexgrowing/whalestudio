import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def StabDec : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ r s : ℕ), B.IsGood σ →
    (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → H.IsAdapted σ B Y Y₁ i₀ i₁ →
    (∀ (p : UA σ Y.J) (t : (AE F E)ˣ), mat p *ᵥ incV F H.x = t.1 • incV F H.x →
      ∃ u ∈ unip σ Y H, ∃ g₁ m, IsLevi (W₁ := Y₁) H t g₁ m ∧ p = u * m ∧ (p ∈ ratU σ Y.J → g₁ ∈ ratU σ Y₁.J)) ∧
    (∀ (ξ : Eˣ), ∀ g₁ ∈ ratU σ Y₁.J, ∀ m, IsLevi H (Units.map (inclR (F := F) (AF F)).toMonoidHom ξ) g₁ m → m ∈ ratU σ Y.J) ∧
    ∀ t (g₁ : UA σ Y₁.J) m, IsLevi H t g₁ m → ∀ u ∈ unip σ Y H, m⁻¹ * u * m ∈ unip σ Y H

def ConeA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ r s r' s' : ℕ)
    (M : Model σ X W) (M₀ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ e, IsEv B M M₀ H.ι H'.ι (isoA H H') e → ∀ z : ℕ, 2 * n = d + 2 * z ∧ min r s + 2 ≤ z →
    ∀ (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), Iwa H K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ χX χW om om₀, IsPair B M χX χW om (r + 1) (s + 1) (r' + 1) (s' + 1) → IsPair B M₀ χX χW om₀ r s r' s' →
      ∀ Φ ∈ schA F (Fin n × Fin d), KFinite om K Φ →
      (∀ γ, Moves (σ := σ) (X := X) H γ → ∀ h,
        (∀ᵐ g ∂(M.μ.restrict M.dom), Summable fun x => thv B M om e (shiftA H H' 1) Φ h (γ x * g)) ∧
        IntegrableOn (fun g => ∑' x, thv B M om e (shiftA H H' 1) Φ h (γ x * g)) M.dom M.μ ∧
        ∫ g in M.dom, ∑' x, thv B M om e (shiftA H H' 1) Φ h (γ x * g) ∂M.μ =
          κ * coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ) 1) ∧
      (∀ t h₁ p, IsLevi H' t h₁ p → ∀ h, coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, p * h) Φ) 1 =
        ((χX / χW) t : ℂ) * (((absE F E t : ℝ) ^ (((d : ℝ) - n) / 2) : ℝ) : ℂ) *
          coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ) h₁) ∧
      ∀ h h₁, coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ) h₁ =
        M₀.I om₀ (cone B M om e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ)) h₁

def ConeB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ r s r' s' : ℕ)
    (M : Model σ X W) (M₀ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ e, IsEv B M M₀ H.ι H'.ι (isoB H H') e → ∀ z : ℕ, d + 2 = 2 * n + 2 * z ∧ 2 ≤ z →
    ∀ (K : Subgroup (UA σ X.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), Iwa H K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ χX χW om om₀, IsPair B M χX χW om (r + 1) (s + 1) (r' + 1) (s' + 1) → IsPair B M₀ χX χW om₀ r s r' s' →
      ∀ Φ ∈ M.So B.ψ B.τ₁, KFinite om K Φ →
      (∀ γ, Moves (σ := σ) (X := X) H γ → ∀ h,
        (∀ᵐ g ∂(M.μ.restrict M.dom), Summable fun x => thv B M om e (shiftB σ H H' 1) Φ h (γ x * g)) ∧
        IntegrableOn (fun g => ∑' x, thv B M om e (shiftB σ H H' 1) Φ h (γ x * g)) M.dom M.μ ∧
        ∫ g in M.dom, ∑' x, thv B M om e (shiftB σ H H' 1) Φ h (γ x * g) ∂M.μ =
          κ * coneI B M om M₀ om₀ e K μK μ (shiftB σ H H') χW z (om (1, h) Φ) 1) ∧
      (∀ t h₁ p, IsLevi H' t h₁ p → ∀ h, coneI B M om M₀ om₀ e K μK μ (shiftB σ H H') χW z (om (1, p * h) Φ) 1 =
        ((χX / χW) t : ℂ) * (((absE F E t : ℝ) ^ (((d : ℝ) - n) / 2) : ℝ) : ℂ) *
          coneI B M om M₀ om₀ e K μK μ (shiftB σ H H') χW z (om (1, h) Φ) h₁) ∧
      ∀ h h₁, coneI B M om M₀ om₀ e K μK μ (shiftB σ H H') χW z (om (1, h) Φ) h₁ =
        M₀.I om₀ (cone B M om e K μK μ (shiftB σ H H') χW z (om (1, h) Φ)) h₁

end PositivityTheory.ThKCT

end
