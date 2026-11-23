import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.UnipUGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex

noncomputable section

namespace PositivityTheory.ThKEnd.Cusp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

def colOp (i : Fin d) (ρ : Fin d → k) (Y : Matrix (Fin n) (Fin d) k) : Matrix (Fin n) (Fin d) k :=
  Y + Matrix.vecMulVec (fun a => Y a i) ρ

def LeftLaw (ξ : kˣ →* ℂˣ) (l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ φ ∈ SB (Matrix (Fin n) (Fin d) k), ∀ γ : GL (Fin n) k,
    l (fun Y => φ (γ.1 * Y)) = ξ (Matrix.GeneralLinearGroup.det γ) * l φ

def ColLaw (ψ : AddChar k ℂ) (S : Set (Fin d)) (i i' : Fin d) (l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ φ ∈ SB (Matrix (Fin n) (Fin d) k), ∀ ρ : Fin d → k, (∀ s ∈ S, ρ s = 0) → l (fun Y => φ (colOp i ρ Y)) = ψ (ρ i') * l φ

variable (k n d) in

def oneO : Matrix (Fin n) (Fin d) k → ℂ := Set.indicator {Y | ∀ a b, ValuativeRel.valuation k (Y a b) ≤ 1} 1

def torus (i₀ i₁ : Fin d) (x : k) : Matrix (Fin d) (Fin d) k :=
  Matrix.diagonal fun i => if i = i₀ then x else if i = i₁ then x⁻¹ else 1

end Local

def LocSupp : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ψ : AddChar k ℂ), ψ ≠ 1 →
    ∀ (i₀ i₁ : Fin d), i₀ ≠ i₁ → ∀ (ξ : kˣ →* ℂˣ) (l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ), LeftLaw ξ l → ColLaw ψ {i₀} i₀ i₁ l →
    ∀ φ ∈ SB (Matrix (Fin n) (Fin d) k), (∀ Y, ¬ LinearIndependent k ![fun a => Y a i₀, fun a => Y a i₁] → φ Y = 0) → l φ = 0

def LocThree : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ψ : AddChar k ℂ), ψ ≠ 1 →
    ∀ (i₀ i₁ i₂ : Fin d), i₀ ≠ i₁ → i₀ ≠ i₂ → i₁ ≠ i₂ → ∀ (ξ : kˣ →* ℂˣ) (l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ), LeftLaw ξ l →
    ColLaw ψ {i₀} i₀ i₁ l → ColLaw ψ {i₀, i₁} i₁ i₂ l → ∀ φ ∈ SB (Matrix (Fin n) (Fin d) k), l φ = 0

def LocTwo : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ →
    ∀ (ψ : AddChar k ℂ) (c : ℤ), (∀ x, ValuativeRel.valuation k x ≤ ValuativeRel.valuation k ((ϖ ^ c : kˣ) : k) → ψ x = 1) →
    (∃ x, ValuativeRel.valuation k x ≤ ValuativeRel.valuation k ((ϖ ^ (c - 1) : kˣ) : k) ∧ ψ x ≠ 1) →
    ∀ (i₀ i₁ : Fin d), i₀ ≠ i₁ → ∀ (ξ : kˣ →* ℂˣ), (∀ x : kˣ, ValuativeRel.valuation k (x : k) = 1 → ξ x = 1) →
    ∀ l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ, LeftLaw ξ l → ColLaw ψ {i₀} i₀ i₁ l →
    ∀ r : ℂ, r = ξ ϖ * (GlobalTheory.SplitWeil.resCard k : ℂ) ^ ((n : ℤ) - d) → ∃ x : ℂ, ∀ m : ℕ,
      l (fun Y => oneO k n d (Y * torus i₀ i₁ ((ϖ : k) ^ m))) =
        x * ((GlobalTheory.SplitWeil.resCard k : ℂ) * r) ^ (-(m : ℤ)) * ∑ i ∈ Finset.range (2 * m - c + 1).toNat, r ^ i

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def VacBar : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) r s r' s', B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ᶠ v : Pl F in cofinite, ∀ (t : E →ₐ[F] Fv F v) ι, M.IsLinBar B.ψ t 1 1 ι → ∃ c : ℂ, ι (M.vac v) = c • oneO (Fv F v) n d

def Places : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    (∀ (v : Pl F) (t : E →ₐ[F] Fv F v), Continuous (piW t)) ∧
    (∀ z : AE F E, ∀ᶠ v : Pl F in cofinite, ∀ t : E →ₐ[F] Fv F v, ValuativeRel.valuation (Fv F v) (piW t z) ≤ 1) ∧
    (∀ (χ : Chr F E) (T : Set (Pl F)), UnrOff χ T → ∀ v ∉ T, ∀ (t : E →ₐ[F] Fv F v) (x : (Fv F v)ˣ),
      ValuativeRel.valuation (Fv F v) (x : Fv F v) = 1 → chrW χ t x = 1) ∧
    {v : Pl F | Nonempty (E →ₐ[F] Fv F v)}.Infinite

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d j : ℕ}

variable (σ) in

structure IsFrame (W : Spc F E d) (u u' : Matrix (Fin d) (Fin j) E) : Prop where
  uu : uᵀ * W.J * u.map σ = 0
  vv : u'ᵀ * W.J * u'.map σ = 0
  uv : uᵀ * W.J * u'.map σ = 1

def colSp (u : Matrix (Fin d) (Fin j) E) : Submodule E (Fin d → E) := Submodule.span E (Set.range uᵀ)

variable (σ) in

def levM (W : Spc F E d) (u u' : Matrix (Fin d) (Fin j) E) (g : GL (Fin j) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E) :=
  1 + incM F u * (g.1 - 1) * incM F (W.J * u'.map σ)ᵀ - incM F u' * (((g⁻¹).1.map (cA σ))ᵀ - 1) * incM F (W.J * u.map σ)ᵀ

def IsLev {W : Spc F E d} (u u' : Matrix (Fin d) (Fin j) E) (m : GL (Fin j) (AE F E) →* UA σ W.J) : Prop :=
  Continuous m ∧ ∀ g, mat (m g) = levM σ W u u' g

def IsChar (σ : E →ₐ[F] E) (χ : AddChar (AE F E) ℂ) : Prop :=
  Continuous χ ∧ ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), ∃ z, At (evFin F v) z ∧ piW (t.comp σ) z = 0 ∧ χ z ≠ 1

structure IsWh (W : Spc F E d) (u : Matrix (Fin d) (Fin j) E) (χ : AddChar (AE F E) ℂ) (Λ : (UA σ W.J → ℂ) → ℂ) : Prop where
  add : ∀ f f', IsAut (W := W) f → IsAut (W := W) f' → Λ (f + f') = Λ f + Λ f'
  smul : ∀ (c : ℂ) f, Λ (c • f) = c * Λ f
  law : ∀ f, IsAut (W := W) f → ∀ (h : UA σ W.J) (g : Matrix (Fin j) (Fin j) (AE F E)), mat h * incM F u = incM F u * g →
    (∀ a b : Fin j, b < a → g a b = 0) → (∀ a, g a a = 1) →
    (∀ z : Fin d → E, (∀ x ∈ colSp u, form σ W.J z x = 0) →
      mat h *ᵥ incV F z - incV F z ∈ Submodule.span (AE F E) (incV F '' (colSp u : Set (Fin d → E)))) →
    Λ (fun x => f (x * h)) = χ (∑ p : Fin j × Fin j with (p.2 : ℕ) = p.1 + 1, g p.1 p.2) * Λ f

def KeyThree : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (j : ℕ) (u u' : Matrix (Fin (a + a')) (Fin (j + 3)) E),
    IsFrame σ G.W u u' → ∀ χ Λ, IsChar σ χ → IsWh (σ := σ) G.W u χ Λ → ∀ f ∈ Sig B G om om', ∀ h, Λ (fun x => f (x * h)) = 0

def KeyTwo : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (u u' : Matrix (Fin (a + a')) (Fin 2) E),
    IsFrame σ G.W u u' → ∀ m, IsLev u u' m → ∀ χ Λ, IsChar σ χ → IsWh (σ := σ) G.W u χ Λ → ∀ f ∈ Sig B G om om', ∀ h₀,
    ∃ V ∈ 𝓝 h₀, ∃ (b : ℕ → GL (Fin 2) (AE F E)) (y : ℕ → ℂ), b 0 = 1 ∧ (∀ i, Matrix.GeneralLinearGroup.det (b i) = 1) ∧
      Tendsto (fun i => ‖y i‖) atTop atTop ∧ ∀ h ∈ V, ∃ x : ℂ, ∀ i, Λ (fun z => f (z * (m (b i) * h))) = x * y i

end PositivityTheory.ThKEnd.Cusp

end
