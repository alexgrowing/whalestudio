import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifEx2
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.InfSpanNeBot
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HaarPushforwardEqBallDensity

noncomputable section

namespace SheetDecomposition

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.Dict
  GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas GlobalTheory.CompanionTheory.Ar.Cmp PositivityTheory.EqVol

def MFund {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} {G : Type} [Group G] (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (ρ : G → Ψ → Matrix (Sg j j') (Sg j j') ℂ) (Γ : Subgroup G) (S : Set (Fin n → ℂ)) : Prop :=
  MeasurableSet S ∧ S ⊆ ballDom q ∧ (∀ t ∈ ballDom q, ∃ γ ∈ Γ, moebBall q (ρ γ) t ∈ S) ∧
    ∀ t ∈ S, ∀ γ ∈ Γ, moebBall q (ρ γ) t ∈ S → γ = 1

def rho {E : Type} [Field E] {Ψ : Type} {j j' N : ℕ} (s : Ψ → (E →+* ℂ)) (A : Ψ → Matrix (Fin N) (Sg j j') ℂ)
    (Ai : Ψ → Matrix (Sg j j') (Fin N) ℂ) (γ : GL (Fin N) E) (τ : Ψ) : Matrix (Sg j j') (Sg j j') ℂ :=
  Ai τ * ((γ : Matrix (Fin N) (Fin N) E).map (s τ) * A τ)

def MoebVol : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q q' : Ψ × Fin j × Fin j' ≃ Fin n) (G : Type) [Group G] [Countable G]
    (ρ ρ' : G → Ψ → Matrix (Sg j j') (Sg j j') ℂ) (w : Ψ → Matrix (Sg j j') (Sg j j') ℂ) (U Γ Γ' : Subgroup G) (a : G)
    (S S' : Set (Fin n → ℂ)), (∀ τ, ρ 1 τ = 1) → (∀ x y τ, ρ (x * y) τ = ρ x τ * ρ y τ) → (∀ γ ∈ U, ∀ τ, IsSgU (ρ γ τ)) →
    (∀ γ ∈ Γ', ∀ τ, IsSgU (ρ' γ τ)) → (∀ τ, IsSgU (w τ)) → (∀ γ τ, w τ * ρ' γ τ = ρ (a * γ * a⁻¹) τ * w τ) →
    Γ ≤ U → conjBy a Γ' ≤ U → EqIdx Γ (conjBy a Γ') → MFund q ρ Γ S → MFund q' ρ' Γ' S' → ballMeas q S = ballMeas q' S'

def StdZ : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F), ∃ A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ,
    (∀ τ, (A τ)ᴴ * C.sgr τ * A τ = sgI j j') ∧ ∃ Z : (Fin n → ℂ) → Fin n → ℂ, Set.BijOn Z (ballDom F.q) (ballDom F.q) ∧
      (∀ S, MeasurableSet S → S ⊆ ballDom F.q → MeasurableSet (Z '' S) ∧ ballMeas F.q (Z '' S) = ballMeas F.q S) ∧
      ∀ (γ : GL (Fin (j + j')) E) (δ : Λ ≃ₗ[𝓞 E] Λ), (∀ x, C.e (δ x) = (γ : Matrix (Fin (j + j')) (Fin (j + j')) E) *ᵥ C.e x) →
        (∀ x y, F.form (δ x) (δ y) = F.form x y) →
        (∀ τ, ((γ : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ)))ᴴ * C.gr τ *
          (γ : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ)) = C.gr τ) →
        ∀ t ∈ ballDom F.q, ∀ t' ∈ ballDom F.q, ((F.R t).EqvBy (F.R t') δ ↔
          Z t' = moebBall F.q (rho (fun τ => embOf (F.σ τ)) A (fun τ => C.cinv (A τ) τ) γ) (Z t))

def StdModel : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] [Nonempty Ψ] (j j' n g : ℕ) (Λ : Type)
    [AddCommGroup Λ] [Module (𝓞 E) Λ] (_ : Host E) (F : UnivFam E Ψ j j' n g Λ) (ξ : E) (c₀ : ℝ), 0 < c₀ →
    (∀ τ, embOf (F.σ τ) ξ = Complex.I * (c₀ : ℂ)) →
    ∃ (G : Matrix (Fin (j + j')) (Fin (j + j')) E) (e : Λ →ₗ[𝓞 E] (Fin (j + j') → E))
      (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (Ai : Ψ → Matrix (Sg j j') (Fin (j + j')) ℂ) (Z : (Fin n → ℂ) → Fin n → ℂ),
      (∀ a b, cc (G a b) = G b a) ∧ G.det ≠ 0 ∧ Function.Injective e ∧ IsLat (LinearMap.range e) ∧
      (∀ x y, ((F.form x y : ℤ) : ℚ) = EFf (-ξ) G (e x) (e y)) ∧
      (∀ τ, (A τ)ᴴ * (G.map (embOf (F.σ τ)))ᵀ * A τ = sgI j j' ∧ Ai τ * A τ = 1 ∧ A τ * Ai τ = 1) ∧
      Set.BijOn Z (ballDom F.q) (ballDom F.q) ∧
      (∀ S, MeasurableSet S → S ⊆ ballDom F.q → MeasurableSet (Z '' S) ∧ ballMeas F.q (Z '' S) = ballMeas F.q S) ∧
      ∀ γ ∈ uGrp (ccH E) G, ∀ δ : Λ ≃ₗ[𝓞 E] Λ, (∀ x, e (δ x) = (γ : Matrix (Fin (j + j')) (Fin (j + j')) E) *ᵥ e x) →
        ∀ t ∈ ballDom F.q, ∀ t' ∈ ballDom F.q, ((F.R t).EqvBy (F.R t') δ ↔
          Z t' = moebBall F.q (rho (fun τ => embOf (F.σ τ)) A Ai γ) (Z t))

def ArithIdx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (Ψ : Type)
    (j j' : ℕ) (s : Ψ → (E →+* ℂ)) (G G' : Matrix (Fin (j + j')) (Fin (j + j')) E)
    (L L' : Submodule (𝓞 E) (Fin (j + j') → E)) (ξ : E) (𝔞 : Ideal (𝓞 E)),
    (∀ u : E →+* ℂ, u ∈ Set.range s ∨ ComplexEmbedding.conjugate u ∈ Set.range s) → 0 < j → 0 < j' → 3 ≤ j + j' →
    (∀ a b, cc (G a b) = G b a) → (∀ a b, cc (G' a b) = G' b a) → G.det ≠ 0 → G'.det ≠ 0 →
    (∀ τ, ∃ (A : Matrix (Fin (j + j')) (Sg j j') ℂ), Aᴴ * (G.map (s τ))ᵀ * A = sgI j j') →
    (∀ τ, ∃ (A : Matrix (Fin (j + j')) (Sg j j') ℂ), Aᴴ * (G'.map (s τ))ᵀ * A = sgI j j') →
    IsLat L → IsLat L' → ξ ≠ 0 → cc ξ = -ξ → SDTrace ξ G L → SDTrace ξ G' L' → 𝔞 ≠ ⊥ → Neat (IsCMField.complexConj E) 𝔞 →
    ∃ a : GL (Fin (j + j')) E,
      (a : Matrix (Fin (j + j')) (Fin (j + j')) E)ᵀ * G * (a : Matrix (Fin (j + j')) (Fin (j + j')) E).map (ccH E) = G' ∧
      conjBy a (levelGrp (ccH E) G' L' 𝔞) ≤ uGrp (ccH E) G ∧
      EqIdx (levelGrp (ccH E) G L 𝔞) (conjBy a (levelGrp (ccH E) G' L' 𝔞))

def LevelDict : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (D : Datum H) (N : ℕ)
    (G : Matrix (Fin N) (Fin N) E) (e : D.La →ₗ[𝓞 E] (Fin N → E)) (ξ : E) (form : D.La →ₗ[ℤ] D.La →ₗ[ℤ] ℤ),
    (form = D.EF ∨ form = -D.EF) → Function.Injective e → IsLat (LinearMap.range e) → ξ ≠ 0 →
    (∀ x y, ((form x y : ℤ) : ℚ) = EFf ξ G (e x) (e y)) →
    SDTrace ξ G (LinearMap.range e) ∧
      (∀ γ ∈ levelGrp (ccH E) G (LinearMap.range e) (levIdeal l), ∃ δ, InLevel l D δ ∧
        ∀ x, e (δ x) = (γ : Matrix (Fin N) (Fin N) E) *ᵥ e x) ∧
      ∀ δ, InLevel l D δ → ∃ γ ∈ levelGrp (ccH E) G (LinearMap.range e) (levIdeal l),
        ∀ x, e (δ x) = (γ : Matrix (Fin N) (Fin N) E) *ᵥ e x

def FamVol : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (D D' : Datum H) (Ψ : Type) [Fintype Ψ]
    (j j' n g : ℕ) (F : UnivFam E Ψ j j' n g D.La) (F' : UnivFam E Ψ j j' n g D'.La) (Γ : Subgroup (D.La ≃ₗ[𝓞 E] D.La))
    (Γ' : Subgroup (D'.La ≃ₗ[𝓞 E] D'.La)) (FF FF' : Set (Fin n → ℂ)) (c₀ : ℝ), 0 < j → 0 < j' → 3 ≤ j + j' → 0 < c₀ →
    F'.σ = F.σ → (∀ τ, F.σ τ H.rt = Complex.I * (c₀ : ℂ)) → (F.form = D.EF ∨ F.form = -D.EF) →
    (F'.form = D'.EF ∨ F'.form = -D'.EF) → (∀ γ, γ ∈ Γ ↔ InLevel l D γ) → (∀ γ, γ ∈ Γ' ↔ InLevel l D' γ) →
    F.IsFundSet Γ FF → F'.IsFundSet Γ' FF' → ballMeas F.q FF = ballMeas F'.q FF'

end SheetDecomposition
